
/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

#include <libss.h>
#include <libsf.h>
#include <libsr.h>
#include <libsv.h>
#include <libsl.h>
#include <libsd.h>
#include <libsi.h>

sinode *si_nodenew(sr *r)
{
	sinode *n = (sinode*)ss_malloc(r->a, sizeof(sinode));
	if (ssunlikely(n == NULL)) {
		sr_oom_malfunction(r->e);
		return NULL;
	}
	n->recover = 0;
	n->backup = 0;
	n->flags = 0;
	n->update_time = 0;
	n->used = 0;
	si_branchinit(&n->self);
	n->branch = NULL;
	n->branch_count = 0;
	ss_fileinit(&n->file, r->a);
	ss_mmapinit(&n->map);
	ss_mmapinit(&n->map_swap);
	sv_indexinit(&n->i0);
	sv_indexinit(&n->i1);
	ss_rbinitnode(&n->node);
	ss_rqinitnode(&n->nodecompact);
	ss_rqinitnode(&n->nodebranch);
	ss_listinit(&n->commit);
	return n;
}

static inline int
si_nodeclose(sinode *n, sr *r)
{
	int rcret = 0;
	int rc = ss_munmap(&n->map);
	if (ssunlikely(rc == -1)) {
		sr_malfunction(r->e, "db file '%s' munmap error: %s",
		               n->file.file, strerror(errno));
		rcret = -1;
	}
	rc = ss_fileclose(&n->file);
	if (ssunlikely(rc == -1)) {
		sr_malfunction(r->e, "db file '%s' close error: %s",
		               n->file.file, strerror(errno));
		rcret = -1;
	}
	sv_indexfree(&n->i0, r);
	sv_indexfree(&n->i1, r);
	return rcret;
}

static inline int
si_noderecover(sinode *n, sr *r)
{
	/* recover branches */
	ssiter i;
	ss_iterinit(sd_recover, &i);
	ss_iteropen(sd_recover, &i, r, &n->file);
	int first = 1;
	int rc;
	while (ss_iteratorhas(&i))
	{
		sdindexheader *h = ss_iteratorof(&i);
		sibranch *b;
		if (first) {
			b =  &n->self;
		} else {
			b = si_branchnew(r);
			if (ssunlikely(b == NULL))
				goto error;
		}
		sdindex index;
		sd_indexinit(&index);
		rc = sd_indexcopy(&index, r, h);
		if (ssunlikely(rc == -1))
			goto error;
		si_branchset(b, &index);

		b->next   = n->branch;
		n->branch = b;
		n->branch_count++;

		first = 0;
		ss_iteratornext(&i);
	}
	rc = sd_recover_complete(&i);
	if (ssunlikely(rc == -1))
		goto error;
	ss_iteratorclose(&i);
	return 0;
error:
	ss_iteratorclose(&i);
	return -1;
}

int si_nodeopen(sinode *n, sr *r, sischeme *scheme, sspath *path)
{
	int rc = ss_fileopen(&n->file, path->path);
	if (ssunlikely(rc == -1)) {
		sr_malfunction(r->e, "db file '%s' open error: %s",
		               n->file.file, strerror(errno));
		return -1;
	}
	rc = ss_fileseek(&n->file, n->file.size);
	if (ssunlikely(rc == -1)) {
		si_nodeclose(n, r);
		sr_malfunction(r->e, "db file '%s' seek error: %s",
		               n->file.file, strerror(errno));
		return -1;
	}
	rc = si_noderecover(n, r);
	if (ssunlikely(rc == -1))
		si_nodeclose(n, r);
	if (scheme->mmap) {
		rc = si_nodemap(n, r);
		if (ssunlikely(rc == -1))
			si_nodeclose(n, r);
	}
	return rc;
}

int si_nodecreate(sinode *n, sr *r, sischeme *scheme, sdid *id,
                  sdindex *i,
                  sdbuild *build)
{
	si_branchset(&n->self, i);
	sspath path;
	ss_pathAB(&path, scheme->path, id->parent, id->id, ".db.incomplete");
	int rc = ss_filenew(&n->file, path.path);
	if (ssunlikely(rc == -1)) {
		sr_malfunction(r->e, "db file '%s' create error: %s",
		               path.path, strerror(errno));
		return -1;
	}
	rc = sd_commit(build, r, &n->self.index, &n->file);
	if (ssunlikely(rc == -1))
		return -1;
	if (scheme->mmap) {
		rc = si_nodemap(n, r);
		if (ssunlikely(rc == -1))
			return -1;
	}
	n->branch = &n->self;
	n->branch_count++;
	return 0;
}

int si_nodemap(sinode *n, sr *r)
{
	int rc = ss_mmap(&n->map, n->file.fd, n->file.size, 1);
	if (ssunlikely(rc == -1)) {
		sr_malfunction(r->e, "db file '%s' mmap error: %s",
		               n->file.file, strerror(errno));
		return -1;
	}
	return 0;
}

int si_nodesync(sinode *n, sr *r)
{
	int rc = ss_filesync(&n->file);
	if (ssunlikely(rc == -1)) {
		sr_malfunction(r->e, "db file '%s' sync error: %s",
		               n->file.file, strerror(errno));
		return -1;
	}
	return 0;
}

static inline void
si_nodefree_branches(sinode *n, sr *r)
{
	sibranch *p = n->branch;
	sibranch *next = NULL;
	while (p && p != &n->self) {
		next = p->next;
		si_branchfree(p, r);
		p = next;
	}
	sd_indexfree(&n->self.index, r);
}

int si_nodefree(sinode *n, sr *r, int gc)
{
	int rcret = 0;
	int rc;
	if (gc && n->file.file) {
		rc = ss_fileunlink(n->file.file);
		if (ssunlikely(rc == -1)) {
			sr_malfunction(r->e, "db file '%s' unlink error: %s",
			               n->file.file, strerror(errno));
			rcret = -1;
		}
	}
	si_nodefree_branches(n, r);
	rc = si_nodeclose(n, r);
	if (ssunlikely(rc == -1))
		rcret = -1;
	ss_free(r->a, n);
	return rcret;
}

ss_rbtruncate(si_nodegc_indexgc,
              si_gcv((ssa*)arg, sscast(n, svv, node)))

int si_nodegc_index(sr *r, svindex *i)
{
	if (i->i.root)
		si_nodegc_indexgc(i->i.root, r->a);
	sv_indexinit(i);
	return 0;
}

int si_nodeseal(sinode *n, sr *r, sischeme *scheme)
{
	sspath path;
	ss_pathAB(&path, scheme->path, n->self.id.parent,
	          n->self.id.id, ".db.seal");
	int rc = ss_filerename(&n->file, path.path);
	if (ssunlikely(rc == -1)) {
		sr_malfunction(r->e, "db file '%s' rename error: %s",
		               n->file.file, strerror(errno));
	}
	return rc;
}

int si_nodecomplete(sinode *n, sr *r, sischeme *scheme)
{
	sspath path;
	ss_pathA(&path, scheme->path, n->self.id.id, ".db");
	int rc = ss_filerename(&n->file, path.path);
	if (ssunlikely(rc == -1)) {
		sr_malfunction(r->e, "db file '%s' rename error: %s",
		               n->file.file, strerror(errno));
	}
	return rc;
}
