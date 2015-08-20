#ifndef SV_WRITEITER_H_
#define SV_WRITEITER_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct svwriteiter svwriteiter;

struct svwriteiter {
	ssiter *merge;
	uint64_t limit;
	uint64_t size;
	uint32_t sizev;
	uint64_t vlsn;
	int save_delete;
	int save_update;
	int next;
	int update;
	uint64_t prevlsn;
	sv *v;
	int vdup;
	svupdate *u;
	sr *r;
} sspacked;

static inline int
sv_writeiter_update(svwriteiter *i)
{
	/* apply update only on duplicate statements which are
	 * ready to be garbage-collected */
	sv_updatereset(i->u);

	/* update begin */
	sv *v = ss_iterof(sv_mergeiter, i->merge);
	assert(v != NULL);
	assert(sv_flags(v) & SVUPDATE);
	int rc = sv_updatepush(i->u, i->r, v);
	if (ssunlikely(rc == -1))
		return -1;
	uint64_t prevlsn = sv_lsn(v);
	ss_iternext(sv_mergeiter, i->merge);

	/* iterate over update statements */
	int last_non_upd = 0;
	for (; ss_iterhas(sv_mergeiter, i->merge); ss_iternext(sv_mergeiter, i->merge))
	{
		v = ss_iterof(sv_mergeiter, i->merge);
		int dup = sv_is(v, SVDUP) || sv_mergeisdup(i->merge);
		if (! dup) {
			break;
		}
		if (prevlsn > i->vlsn)
			break;
		/* stop forming updates on a second non-update stmt,
		 * but continue to iterate stream */
		if (last_non_upd) {
			continue;
		}
		last_non_upd = ! (sv_flags(v) & SVUPDATE);
		int rc = sv_updatepush(i->u, i->r, v);
		if (ssunlikely(rc == -1))
			return -1;
		prevlsn = sv_lsn(v);
	}

	/* update */
	rc = sv_update(i->u, i->r);
	if (ssunlikely(rc == -1))
		return -1;
	return 0;
}

static inline void
sv_writeiter_next(ssiter *i)
{
	svwriteiter *im = (svwriteiter*)i->priv;
	if (im->next)
		ss_iternext(sv_mergeiter, im->merge);
	im->next = 0;
	im->v = NULL;
	im->vdup = 0;

	for (; ss_iterhas(sv_mergeiter, im->merge); ss_iternext(sv_mergeiter, im->merge))
	{
		sv *v = ss_iterof(sv_mergeiter, im->merge);
		int dup = sv_is(v, SVDUP) || sv_mergeisdup(im->merge);
		if (im->size >= im->limit) {
			if (! dup)
				break;
		}
		uint64_t lsn = sv_lsn(v);
		if (ssunlikely(dup)) {
			/* keep atleast one visible version for <= vlsn */
			if (im->prevlsn <= im->vlsn)
			{
				if (im->update) {
					im->update = (sv_flags(v) & SVUPDATE) > 0;
				} else {
					continue;
				}
			}
		} else {
			im->update = 0;
			/* delete (stray or on branch) */
			if (!im->save_delete) {
				int del = sv_is(v, SVDELETE);
				if (ssunlikely(del && (lsn <= im->vlsn))) {
					im->prevlsn = lsn;
					continue;
				}
			}
			im->size += im->sizev + sv_size(v);
			/* update */
			if (sv_is(v, SVUPDATE)) {
				int rc;
				/* compaction */
				if (! im->save_update) {
					rc = sv_writeiter_update(im);
					if (ssunlikely(rc == -1))
						return;
					im->prevlsn = lsn;
					im->v = &im->u->result;
					im->vdup = dup;
					im->next = 0;
					break;
				}
				/* branch
				 * keep next ready-to-gc statements to
				 * apply update.
				 */
				im->update = 1;
			}
		}
		im->prevlsn = lsn;
		im->v = v;
		im->vdup = dup;
		im->next = 1;
		break;
	}
}

static inline int
sv_writeiter_open(ssiter *i, sr *r, ssiter *merge, svupdate *u,
                  uint64_t limit,
                  uint32_t sizev, uint64_t vlsn,
                  int save_delete,
                  int save_update)
{
	svwriteiter *im = (svwriteiter*)i->priv;
	im->u     = u;
	im->r     = r;
	im->merge = merge;
	im->limit = limit;
	im->size  = 0;
	im->sizev = sizev;
	im->vlsn  = vlsn;;
	im->save_delete = save_delete;
	im->save_update = save_update;
	assert(im->merge->vif == &sv_mergeiter);
	im->next  = 0;
	im->prevlsn  = 0;
	im->v = NULL;
	im->vdup = 0;
	im->update = 0;
	sv_writeiter_next(i);
	return 0;
}

static inline void
sv_writeiter_close(ssiter *i ssunused)
{ }

static inline int
sv_writeiter_has(ssiter *i)
{
	svwriteiter *im = (svwriteiter*)i->priv;
	return im->v != NULL;
}

static inline void*
sv_writeiter_of(ssiter *i)
{
	svwriteiter *im = (svwriteiter*)i->priv;
	if (ssunlikely(im->v == NULL))
		return NULL;
	return im->v;
}

static inline int
sv_writeiter_resume(ssiter *i)
{
	svwriteiter *im = (svwriteiter*)i->priv;
	im->v       = ss_iterof(sv_mergeiter, im->merge);
	if (ssunlikely(im->v == NULL))
		return 0;
	im->vdup    = sv_is(im->v, SVDUP) || sv_mergeisdup(im->merge);
	im->prevlsn = sv_lsn(im->v);
	im->next    = 1;
	im->update  = 0;
	im->size    = im->sizev + sv_size(im->v);
	return 1;
}

static inline int
sv_writeiter_is_duplicate(ssiter *i)
{
	svwriteiter *im = (svwriteiter*)i->priv;
	assert(im->v != NULL);
	return im->vdup;
}

extern ssiterif sv_writeiter;

#endif
