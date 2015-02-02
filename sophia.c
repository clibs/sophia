
/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

/* amalgamation build
 *
 * version:     1.2
 * build:       cdb9347
 * build date:  Mon Feb  2 10:35:03 EST 2015
 *
 * compilation:
 * cc -O2 -DNDEBUG -std=c99 -pedantic -Wall -Wextra -pthread -c sophia.c
*/

/* {{{ */

#define SOPHIA_BUILD "cdb9347"

#line 1 "sophia/rt/sr_stdc.h"
#ifndef SR_STDC_H_
#define SR_STDC_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

#define _GNU_SOURCE 1

#include <stdlib.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>
#include <limits.h>
#include <math.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>
#include <pthread.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/uio.h>
#include <sys/mman.h>
#include <sys/time.h>
#include <unistd.h>
#include <time.h>
#include <fcntl.h>
#include <dirent.h>
#include <errno.h>

#endif
#line 1 "sophia/rt/sr_macro.h"
#ifndef SR_MACRO_H_
#define SR_MACRO_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

#if __GNUC__ >= 4 && __GNUC_MINOR__ >= 3
#  define srhot __attribute__((hot))
#else
#  define srhot
#endif

#define srpacked __attribute__((packed))
#define srunused __attribute__((unused))
#define srinline __attribute__((always_inline))

#define srcast(N, T, F) ((T*)((char*)(N) - __builtin_offsetof(T, F)))

#define srlikely(EXPR)   __builtin_expect(!! (EXPR), 1)
#define srunlikely(EXPR) __builtin_expect(!! (EXPR), 0)

#define sr_templatecat(a, b) sr_##a##b
#define sr_template(a, b) sr_templatecat(a, b)

#endif
#line 1 "sophia/rt/sr_version.h"
#ifndef SR_VERSION_H_
#define SR_VERSION_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

#define SR_VERSION_MAGIC  8529643324614668147ULL
#define SR_VERSION_A '1'
#define SR_VERSION_B '2'
#define SR_VERSION_C '1'

#if defined(SOPHIA_BUILD)
# define SR_VERSION_COMMIT SOPHIA_BUILD
#else
# define SR_VERSION_COMMIT "unknown"
#endif

typedef struct srversion srversion;

struct srversion {
	uint64_t magic;
	uint8_t  a, b, c;
} srpacked;

static inline void
sr_version(srversion *v)
{
	v->magic = SR_VERSION_MAGIC;
	v->a = SR_VERSION_A;
	v->b = SR_VERSION_B;
	v->c = SR_VERSION_C;
}

static inline int
sr_versioncheck(srversion *v)
{
	if (v->magic != SR_VERSION_MAGIC)
		return 0;
	if (v->a != SR_VERSION_A)
		return 0;
	if (v->b != SR_VERSION_B)
		return 0;
	if (v->c != SR_VERSION_C)
		return 0;
	return 1;
}

#endif
#line 1 "sophia/rt/sr_time.h"
#ifndef SR_TIME_H_
#define SR_TIME_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

void     sr_sleep(uint64_t);
uint64_t sr_utime(void);

#endif
#line 1 "sophia/rt/sr_spinlock.h"
#ifndef SR_LOCK_H_
#define SR_LOCK_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

#if 0
typedef pthread_spinlock_t srspinlock;

static inline void
sr_spinlockinit(srspinlock *l) {
	pthread_spin_init(l, 0);
}

static inline void
sr_spinlockfree(srspinlock *l) {
	pthread_spin_destroy(l);
}

static inline void
sr_spinlock(srspinlock *l) {
	pthread_spin_lock(l);
}

static inline void
sr_spinunlock(srspinlock *l) {
	pthread_spin_unlock(l);
}
#endif

typedef uint8_t srspinlock;

#if defined(__x86_64__) || defined(__i386) || defined(_X86_)
# define CPU_PAUSE __asm__ ("pause")
#else
# define CPU_PAUSE do { } while(0)
#endif

static inline void
sr_spinlockinit(srspinlock *l) {
	*l = 0;
}

static inline void
sr_spinlockfree(srspinlock *l) {
	*l = 0;
}

static inline void
sr_spinlock(srspinlock *l) {
	if (__sync_lock_test_and_set(l, 1) != 0) {
		unsigned int spin_count = 0U;
		for (;;) {
			CPU_PAUSE;
			if (*l == 0U && __sync_lock_test_and_set(l, 1) == 0)
				break;
			if (++spin_count > 100U)
				usleep(0);
		}
	}
}

static inline void
sr_spinunlock(srspinlock *l) {
	__sync_lock_release(l);
}

#endif
#line 1 "sophia/rt/sr_list.h"
#ifndef SR_LIST_H_
#define SR_LIST_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct srlist srlist;

struct srlist {
	srlist *next, *prev;
};

static inline void
sr_listinit(srlist *h) {
	h->next = h->prev = h;
}

static inline void
sr_listappend(srlist *h, srlist *n) {
	n->next = h;
	n->prev = h->prev;
	n->prev->next = n;
	n->next->prev = n;
}

static inline void
sr_listunlink(srlist *n) {
	n->prev->next = n->next;
	n->next->prev = n->prev;
}

static inline void
sr_listpush(srlist *h, srlist *n) {
	n->next = h->next;
	n->prev = h;
	n->prev->next = n;
	n->next->prev = n;
}

static inline srlist*
sr_listpop(srlist *h) {
	register srlist *pop = h->next;
	sr_listunlink(pop);
	return pop;
}

static inline int
sr_listempty(srlist *l) {
	return l->next == l && l->prev == l;
}

static inline void
sr_listmerge(srlist *a, srlist *b) {
	if (srunlikely(sr_listempty(b)))
		return;
	register srlist *first = b->next;
	register srlist *last = b->prev;
	first->prev = a->prev;
	a->prev->next = first;
	last->next = a;
	a->prev = last;
}

static inline void
sr_listreplace(srlist *o, srlist *n) {
	n->next = o->next;
	n->next->prev = n;
	n->prev = o->prev;
	n->prev->next = n;
}

#define sr_listlast(H, N) ((H) == (N))

#define sr_listforeach(H, I) \
	for (I = (H)->next; I != H; I = (I)->next)

#define sr_listforeach_continue(H, I) \
	for (; I != H; I = (I)->next)

#define sr_listforeach_safe(H, I, N) \
	for (I = (H)->next; I != H && (N = I->next); I = N)

#define sr_listforeach_reverse(H, I) \
	for (I = (H)->prev; I != H; I = (I)->prev)

#endif
#line 1 "sophia/rt/sr_pager.h"
#ifndef SR_PAGER_H_
#define SR_PAGER_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct srpagepool srpagepool;
typedef struct srpage srpage;
typedef struct srpager srpager;

struct srpagepool {
	uint32_t used;
	srpagepool *next;
} srpacked;

struct srpage {
	srpagepool *pool;
	srpage *next;
} srpacked;

struct srpager {
	uint32_t page_size;
	uint32_t pool_count;
	uint32_t pool_size;
	uint32_t pools;
	srpagepool *pp;
	srpage *p;
};

void  sr_pagerinit(srpager*, uint32_t, uint32_t);
void  sr_pagerfree(srpager*);
int   sr_pageradd(srpager*);
void *sr_pagerpop(srpager*);
void  sr_pagerpush(srpager*, srpage*);

#endif
#line 1 "sophia/rt/sr_a.h"
#ifndef SR_A_H_
#define SR_A_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sraif sraif;
typedef struct sra sra;

struct sraif {
	int   (*open)(sra*, va_list);
	int   (*close)(sra*);
	void *(*malloc)(sra*, int);
	void *(*realloc)(sra*, void*, int);
	void  (*free)(sra*, void*);
};

struct sra {
	sraif *i;
	char priv[48];
};

static inline int
sr_allocopen(sra *a, sraif *i, ...) {
	a->i = i;
	va_list args;
	va_start(args, i);
	int rc = i->open(a, args);
	va_end(args);
	return rc;
}

static inline int
sr_allocclose(sra *a) {
	return a->i->close(a);
}

static inline void*
sr_malloc(sra *a, int size) {
	return a->i->malloc(a, size);
}

static inline void*
sr_realloc(sra *a, void *ptr, int size) {
	return a->i->realloc(a, ptr, size);
}

static inline void
sr_free(sra *a, void *ptr) {
	a->i->free(a, ptr);
}

static inline char*
sr_strdup(sra *a, char *str) {
	int sz = strlen(str) + 1;
	char *s = sr_malloc(a, sz);
	if (srunlikely(s == NULL))
		return NULL;
	memcpy(s, str, sz);
	return s;
}

static inline char*
sr_memdup(sra *a, void *ptr, size_t size) {
	char *s = sr_malloc(a, size);
	if (srunlikely(s == NULL))
		return NULL;
	memcpy(s, ptr, size);
	return s;
}

#endif
#line 1 "sophia/rt/sr_astd.h"
#ifndef SR_ASTD_H_
#define SR_ASTD_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

extern sraif sr_astd;

#endif
#line 1 "sophia/rt/sr_aslab.h"
#ifndef SR_ASLAB_H_
#define SR_ASLAB_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

extern sraif sr_aslab;

#endif
#line 1 "sophia/rt/sr_error.h"
#ifndef SR_ERROR_H_
#define SR_ERROR_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct srerror srerror;

enum {
	SR_ERROR_NONE  = 0,
	SR_ERROR = 1,
	SR_ERROR_MALFUNCTION = 2
};

struct srerror {
	srspinlock lock;
	int type;
	const char *file;
	const char *function;
	int line;
	char error[256];
};

static inline void
sr_errorinit(srerror *e) {
	e->type = SR_ERROR_NONE;
	e->error[0] = 0;
	e->line = 0;
	e->function = NULL;
	e->file = NULL;
	sr_spinlockinit(&e->lock);
}

static inline void
sr_errorfree(srerror *e) {
	sr_spinlockfree(&e->lock);
}

static inline void
sr_errorreset(srerror *e) {
	sr_spinlock(&e->lock);
	e->type = SR_ERROR_NONE;
	e->error[0] = 0;
	e->line = 0;
	e->function = NULL;
	e->file = NULL;
	sr_spinunlock(&e->lock);
}

static inline void
sr_errorrecover(srerror *e) {
	sr_spinlock(&e->lock);
	assert(e->type == SR_ERROR_MALFUNCTION);
	e->type = SR_ERROR;
	sr_spinunlock(&e->lock);
}

static inline int
sr_errorof(srerror *e) {
	sr_spinlock(&e->lock);
	int type = e->type;
	sr_spinunlock(&e->lock);
	return type;
}

static inline int
sr_errorcopy(srerror *e, char *buf, int bufsize) {
	sr_spinlock(&e->lock);
	int len = snprintf(buf, bufsize, "%s", e->error);
	sr_spinunlock(&e->lock);
	return len;
}

static inline void
sr_verrorset(srerror *e, int type,
             const char *file,
             const char *function, int line,
             char *fmt, va_list args)
{
	sr_spinlock(&e->lock);
	if (srunlikely(e->type == SR_ERROR_MALFUNCTION)) {
		sr_spinunlock(&e->lock);
		return;
	}
	e->file     = file;
	e->function = function;
	e->line     = line;
	e->type     = type;
	int len;
	len = snprintf(e->error, sizeof(e->error), "%s:%d ", file, line);
	vsnprintf(e->error + len, sizeof(e->error) - len, fmt, args);
	sr_spinunlock(&e->lock);
}

static inline int
sr_errorset(srerror *e, int type,
            const char *file,
            const char *function, int line,
            char *fmt, ...)
{
	va_list args;
	va_start(args, fmt);
	sr_verrorset(e, type, file, function, line, fmt, args);
	va_end(args);
	return -1;
}

#define sr_malfunction(e, fmt, ...) \
	sr_errorset(e, SR_ERROR_MALFUNCTION, __FILE__, __FUNCTION__, \
	            __LINE__, fmt, __VA_ARGS__)

#define sr_error(e, fmt, ...) \
	sr_errorset(e, SR_ERROR, __FILE__, __FUNCTION__, __LINE__, fmt, __VA_ARGS__)

#endif
#line 1 "sophia/rt/sr_trace.h"
#ifndef SR_TRACE_H_
#define SR_TRACE_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct srtrace srtrace;

struct srtrace {
	srspinlock lock;
	const char *file;
	const char *function;
	int line;
	char message[100];
};

static inline void
sr_traceinit(srtrace *t) {
	sr_spinlockinit(&t->lock);
	t->message[0] = 0;
	t->line = 0;
	t->function = NULL;
	t->file = NULL;
}

static inline void
sr_tracefree(srtrace *t) {
	sr_spinlockfree(&t->lock);
}

static inline int
sr_tracecopy(srtrace *t, char *buf, int bufsize) {
	sr_spinlock(&t->lock);
	int len = snprintf(buf, bufsize, "%s", t->message);
	sr_spinunlock(&t->lock);
	return len;
}

static inline void
sr_vtrace(srtrace *t,
          const char *file,
          const char *function, int line,
          char *fmt, va_list args)
{
	sr_spinlock(&t->lock);
	t->file     = file;
	t->function = function;
	t->line     = line;
	vsnprintf(t->message, sizeof(t->message), fmt, args);
	sr_spinunlock(&t->lock);
}

static inline int
sr_traceset(srtrace *t,
            const char *file,
            const char *function, int line,
            char *fmt, ...)
{
	va_list args;
	va_start(args, fmt);
	sr_vtrace(t, file, function, line, fmt, args);
	va_end(args);
	return -1;
}

#define sr_trace(t, fmt, ...) \
	sr_traceset(t, __FILE__, __FUNCTION__, __LINE__, fmt, __VA_ARGS__)

#endif
#line 1 "sophia/rt/sr_gc.h"
#ifndef SR_GC_H_
#define SR_GC_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct srgc srgc;

struct srgc {
	srspinlock lock;
	int mark;
	int sweep;
	int complete;
};

static inline void
sr_gcinit(srgc *gc)
{
	sr_spinlockinit(&gc->lock);
	gc->mark     = 0;
	gc->sweep    = 0;
	gc->complete = 0;
}

static inline void
sr_gclock(srgc *gc) {
	sr_spinlock(&gc->lock);
}

static inline void
sr_gcunlock(srgc *gc) {
	sr_spinunlock(&gc->lock);
}

static inline void
sr_gcfree(srgc *gc)
{
	sr_spinlockfree(&gc->lock);
}

static inline void
sr_gcmark(srgc *gc, int n)
{
	sr_spinlock(&gc->lock);
	gc->mark += n;
	sr_spinunlock(&gc->lock);
}

static inline void
sr_gcsweep(srgc *gc, int n)
{
	sr_spinlock(&gc->lock);
	gc->sweep += n;
	sr_spinunlock(&gc->lock);
}

static inline void
sr_gccomplete(srgc *gc)
{
	sr_spinlock(&gc->lock);
	gc->complete = 1;
	sr_spinunlock(&gc->lock);
}

static inline int
sr_gcinprogress(srgc *gc)
{
	sr_spinlock(&gc->lock);
	int v = gc->complete;
	sr_spinunlock(&gc->lock);
	return !v;
}

static inline int
sr_gcready(srgc *gc, float factor)
{
	sr_spinlock(&gc->lock);
	int ready = gc->sweep >= (gc->mark * factor);
	int rc = ready && gc->complete;
	sr_spinunlock(&gc->lock);
	return rc;
}

static inline int
sr_gcrotateready(srgc *gc, int wm)
{
	sr_spinlock(&gc->lock);
	int rc = gc->mark >= wm;
	sr_spinunlock(&gc->lock);
	return rc;
}

static inline int
sr_gcgarbage(srgc *gc)
{
	sr_spinlock(&gc->lock);
	int ready = (gc->mark == gc->sweep);
	int rc = gc->complete && ready;
	sr_spinunlock(&gc->lock);
	return rc;
}

#endif
#line 1 "sophia/rt/sr_seq.h"
#ifndef SR_SEQ_H_
#define SR_SEQ_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef enum {
	SR_DSN,
	SR_DSNNEXT,
	SR_NSN,
	SR_NSNNEXT,
	SR_BSN,
	SR_BSNNEXT,
	SR_LSN,
	SR_LSNNEXT,
	SR_LFSN,
	SR_LFSNNEXT,
	SR_TSN,
	SR_TSNNEXT
} srseqop;

typedef struct {
	srspinlock lock;
	uint32_t dsn;
	uint32_t nsn;
	uint32_t bsn;
	uint64_t lsn;
	uint32_t lfsn;
	uint32_t tsn;
} srseq;

static inline void
sr_seqinit(srseq *n) {
	memset(n, 0, sizeof(*n));
	sr_spinlockinit(&n->lock);
}

static inline void
sr_seqfree(srseq *n) {
	sr_spinlockfree(&n->lock);
}

static inline void
sr_seqlock(srseq *n) {
	sr_spinlock(&n->lock);
}

static inline void
sr_sequnlock(srseq *n) {
	sr_spinunlock(&n->lock);
}

static inline uint64_t
sr_seqdo(srseq *n, srseqop op)
{
	uint64_t v = 0;
	switch (op) {
	case SR_LSN:      v = n->lsn;
		break;
	case SR_LSNNEXT:  v = ++n->lsn;
		break;
	case SR_TSN:      v = n->tsn;
		break;
	case SR_TSNNEXT:  v = ++n->tsn;
		break;
	case SR_NSN:      v = n->nsn;
		break;
	case SR_NSNNEXT:  v = ++n->nsn;
		break;
	case SR_LFSN:     v = n->lfsn;
		break;
	case SR_LFSNNEXT: v = ++n->lfsn;
		break;
	case SR_DSN:      v = n->dsn;
		break;
	case SR_DSNNEXT:  v = ++n->dsn;
		break;
	case SR_BSN:      v = n->bsn;
		break;
	case SR_BSNNEXT:  v = ++n->bsn;
		break;
	}
	return v;
}

static inline uint64_t
sr_seq(srseq *n, srseqop op)
{
	sr_seqlock(n);
	uint64_t v = sr_seqdo(n, op);
	sr_sequnlock(n);
	return v;
}

#endif
#line 1 "sophia/rt/sr_order.h"
#ifndef SR_ORDER_H_
#define SR_ORDER_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef enum {
	SR_LT,
	SR_LTE,
	SR_GT,
	SR_GTE,
	SR_EQ,
	SR_UPDATE,
	SR_ROUTE,
	SR_RANDOM,
	SR_STOP
} srorder;

static inline srorder
sr_orderof(char *order)
{
	srorder cmp = SR_STOP;
	if (strcmp(order, ">") == 0) {
		cmp = SR_GT;
	} else
	if (strcmp(order, ">=") == 0) {
		cmp = SR_GTE;
	} else
	if (strcmp(order, "<") == 0) {
		cmp = SR_LT;
	} else
	if (strcmp(order, "<=") == 0) {
		cmp = SR_LTE;
	} else
	if (strcmp(order, "random") == 0) {
		cmp = SR_RANDOM;
	}
	return cmp;
}

static inline char*
sr_ordername(srorder o)
{
	switch (o) {
	case SR_LT:     return "<";
	case SR_LTE:    return "<=";
	case SR_GT:     return ">";
	case SR_GTE:    return ">=";
	case SR_RANDOM: return "random";
	default: break;
	}
	return NULL;
}

#endif
#line 1 "sophia/rt/sr_trigger.h"
#ifndef SR_TRIGGER_H_
#define SR_TRIGGER_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef int (*srtriggerf)(void *object, void *arg);

typedef struct srtrigger srtrigger;

struct srtrigger {
	srtriggerf func;
	void *arg;
};

void *sr_triggerpointer_of(char*);
void  sr_triggerinit(srtrigger*);
int   sr_triggerset(srtrigger*, char*);
int   sr_triggersetarg(srtrigger*, char*);

static inline void
sr_triggerrun(srtrigger *t, void *object)
{
	if (t->func == NULL)
		return;
	t->func(object, t->arg);
}

#endif
#line 1 "sophia/rt/sr_cmp.h"
#ifndef SR_CMP_H_
#define SR_CMP_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef int (*srcmpf)(char *a, size_t asz, char *b, size_t bsz, void *arg);

typedef struct srcomparator srcomparator;

struct srcomparator {
	srcmpf cmp;
	void *cmparg;
};

static inline int
sr_compare(srcomparator *c, char *a, size_t asize, char *b, size_t bsize)
{
	return c->cmp(a, asize, b, bsize, c->cmparg);
}

int sr_cmpu32(char*, size_t, char*, size_t, void*);
int sr_cmpstring(char*, size_t, char*, size_t, void*);
int sr_cmpset(srcomparator*, char*);
int sr_cmpsetarg(srcomparator*, char*);

#endif
#line 1 "sophia/rt/sr_buf.h"
#ifndef SR_BUF_H_
#define SR_BUF_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct srbuf srbuf;

struct srbuf {
	char *reserve;
	char *s, *p, *e;
};

static inline void
sr_bufinit(srbuf *b)
{
	b->reserve = NULL;
	b->s = NULL;
	b->p = NULL;
	b->e = NULL;
}

static inline void
sr_bufinit_reserve(srbuf *b, void *buf, int size)
{
	b->reserve = buf;
	b->s = buf;
	b->p = b->s; 
	b->e = b->s + size;
}

static inline void
sr_buffree(srbuf *b, sra *a)
{
	if (srunlikely(b->s == NULL))
		return;
	if (srunlikely(b->s != b->reserve))
		sr_free(a, b->s);
	b->s = NULL;
	b->p = NULL;
	b->e = NULL;
}

static inline void
sr_bufreset(srbuf *b) {
	b->p = b->s;
}

static inline int
sr_bufsize(srbuf *b) {
	return b->e - b->s;
}

static inline int
sr_bufused(srbuf *b) {
	return b->p - b->s;
}

static inline int
sr_bufensure(srbuf *b, sra *a, int size)
{
	if (srlikely(b->e - b->p >= size))
		return 0;
	int sz = sr_bufsize(b) * 2;
	int actual = sr_bufused(b) + size;
	if (srunlikely(actual > sz))
		sz = actual;
	char *p;
	if (srunlikely(b->s == b->reserve)) {
		p = sr_malloc(a, sz);
		if (srunlikely(p == NULL))
			return -1;
		memcpy(p, b->s, sr_bufused(b));
	} else {
		p = sr_realloc(a, b->s, sz);
		if (srunlikely(p == NULL))
			return -1;
	}
	b->p = p + (b->p - b->s);
	b->e = p + sz;
	b->s = p;
	assert((b->e - b->p) >= size);
	return 0;
}

static inline int
sr_buftruncate(srbuf *b, sra *a, int size)
{
	assert(size <= (b->p - b->s));
	char *p = b->reserve;
	if (b->s != b->reserve) {
		p = sr_realloc(a, b->s, size);
		if (srunlikely(p == NULL))
			return -1;
	}
	b->p = p + (b->p - b->s);
	b->e = p + size;
	b->s = p;
	return 0;
}

static inline void
sr_bufadvance(srbuf *b, int size)
{
	b->p += size;
}

static inline int
sr_bufadd(srbuf *b, sra *a, void *buf, int size)
{
	int rc = sr_bufensure(b, a, size);
	if (srunlikely(rc == -1))
		return -1;
	memcpy(b->p, buf, size);
	sr_bufadvance(b, size);
	return 0;
}

static inline int
sr_bufin(srbuf *b, void *v) {
	assert(b->s != NULL);
	return (char*)v >= b->s && (char*)v < b->p;
}

static inline void*
sr_bufat(srbuf *b, int size, int i) {
	return b->s + size * i;
}

static inline void
sr_bufset(srbuf *b, int size, int i, char *buf, int bufsize)
{
	assert(b->s + (size * i + bufsize) <= b->p);
	memcpy(b->s + size * i, buf, bufsize);
}

#endif
#line 1 "sophia/rt/sr_injection.h"
#ifndef SR_INJECTION_H_
#define SR_INJECTION_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct srinjection srinjection;

#define SR_INJECTION_SD_BUILD_0      0
#define SR_INJECTION_SD_BUILD_1      1
#define SR_INJECTION_SI_BRANCH_0     2
#define SR_INJECTION_SI_COMPACTION_0 3
#define SR_INJECTION_SI_COMPACTION_1 4
#define SR_INJECTION_SI_COMPACTION_2 5
#define SR_INJECTION_SI_COMPACTION_3 6
#define SR_INJECTION_SI_COMPACTION_4 7
#define SR_INJECTION_SI_RECOVER_0    8

struct srinjection {
	int e[9];
};

#ifdef SR_INJECTION_ENABLE
	#define SR_INJECTION(E, ID, X) \
	if ((E)->e[(ID)]) { \
		X; \
	} else {}
#else
	#define SR_INJECTION(E, ID, X)
#endif

#endif
#line 1 "sophia/rt/sr.h"
#ifndef SR_H_
#define SR_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sr sr;

struct sr {
	srerror *e;
	srcomparator *cmp;
	srseq *seq;
	sra *a;
	srinjection *i;
};

static inline void
sr_init(sr *r,
        srerror *e,
        sra *a,
        srseq *seq,
        srcomparator *cmp,
        srinjection *i)
{
	r->e   = e;
	r->a   = a;
	r->seq = seq;
	r->cmp = cmp;
	r->i   = i;
}

#endif
#line 1 "sophia/rt/sr_c.h"
#ifndef SR_C_H_
#define SR_C_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct src src;
typedef struct srcstmt srcstmt;
typedef struct srcv srcv;

typedef enum {
	SR_CSET,
	SR_CGET,
	SR_CSERIALIZE
} srcop;

typedef enum {
	SR_CRO    = 1,
	SR_CC     = 2,
	SR_CU32   = 4,
	SR_CU64   = 8,
	SR_CSZREF = 16,
	SR_CSZ    = 32, 
	SR_CVOID  = 64
} srctype;

typedef int (*srcf)(src*, srcstmt*, va_list);

struct src {
	char    *name;
	uint8_t  flags;
	srcf     function;
	void    *value;
	void    *ptr;
	src     *next;
} srpacked;

struct srcstmt {
	srcop   op;
	char   *path;
	srbuf  *serialize;
	void  **result;
	void   *ptr;
	sr     *r;
} srpacked;

struct srcv {
	uint8_t  type;
	uint16_t namelen;
	uint32_t valuelen;
} srpacked;

static inline char*
sr_cvname(srcv *v) {
	return (char*)v + sizeof(srcv);
}

static inline char*
sr_cvvalue(srcv *v) {
	return sr_cvname(v) + v->namelen;
}

static inline void*
sr_cvnext(srcv *v) {
	return sr_cvvalue(v) + v->valuelen;
}

int sr_cserialize(src*, srcstmt*);
int sr_cset(src*, srcstmt*, char*);
int sr_cexecv(src*, srcstmt*, va_list);

static inline int
sr_cexec(src *c, srcstmt *stmt, ...)
{
	va_list args;
	va_start(args, stmt);
	int rc = sr_cexecv(c, stmt, args);
	va_end(args);
	return rc;
}

static inline src*
sr_c(src **cp, srcf func, char *name, uint8_t flags, void *v)
{
	src *c = *cp;
	c->function = func;
	c->name     = name;
	c->flags    = flags;
	c->value    = v;
	c->ptr      = NULL;
	c->next     = NULL;
	*cp = c + 1;
	return c;
}

static inline void sr_clink(src **prev, src *c) {
	if (srlikely(*prev))
		(*prev)->next = c;
	*prev = c;
}

static inline src*
sr_cptr(src *c, void *ptr) {
	c->ptr = ptr;
	return c;
}

#endif
#line 1 "sophia/rt/sr_iter.h"
#ifndef SR_ITER_H_
#define SR_ITER_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sriterif sriterif;
typedef struct sriter sriter;

struct sriterif {
	void  (*init)(sriter*);
	int   (*open)(sriter*, va_list);
	void  (*close)(sriter*);
	int   (*has)(sriter*);
	void *(*of)(sriter*);
	void  (*next)(sriter*);
};

struct sriter {
	sriterif *i;
	sr *r;
	char priv[90];
};

static inline void
sr_iterinit(sriter *i, sriterif *ii, sr *r)
{
	i->r = r;
	i->i = ii;
	i->i->init(i);
}

static inline int
sr_iteropen(sriter *i, ...)
{
	assert(i->i != NULL);
	va_list args;
	va_start(args, i);
	int rc = i->i->open(i, args);
	va_end(args);
	return rc;
}

static inline void
sr_iterclose(sriter *i) {
	i->i->close(i);
}

static inline int
sr_iterhas(sriter *i) {
	return i->i->has(i);
}

static inline void*
sr_iterof(sriter *i) {
	return i->i->of(i);
}

static inline void
sr_iternext(sriter *i) {
	i->i->next(i);
}

#endif
#line 1 "sophia/rt/sr_bufiter.h"
#ifndef SR_BUFITER_H_
#define SR_BUFITER_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

extern sriterif sr_bufiter;
extern sriterif sr_bufiterref;

#endif
#line 1 "sophia/rt/sr_mutex.h"
#ifndef SR_MUTEX_H_
#define SR_MUTEX_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct srmutex srmutex;

struct srmutex {
	pthread_mutex_t m;
};

static inline void
sr_mutexinit(srmutex *m) {
	pthread_mutex_init(&m->m, NULL);
}

static inline void
sr_mutexfree(srmutex *m) {
	pthread_mutex_destroy(&m->m);
}

static inline void
sr_mutexlock(srmutex *m) {
	pthread_mutex_lock(&m->m);
}

static inline void
sr_mutexunlock(srmutex *m) {
	pthread_mutex_unlock(&m->m);
}

#endif
#line 1 "sophia/rt/sr_cond.h"
#ifndef SR_COND_H_
#define SR_COND_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct srcond srcond;

struct srcond {
	pthread_cond_t c;
};

static inline void
sr_condinit(srcond *c) {
	pthread_cond_init(&c->c, NULL);
}

static inline void
sr_condfree(srcond *c) {
	pthread_cond_destroy(&c->c);
}

static inline void
sr_condsignal(srcond *c) {
	pthread_cond_signal(&c->c);
}

static inline void
sr_condwait(srcond *c, srmutex *m) {
	pthread_cond_wait(&c->c, &m->m);
}

#endif
#line 1 "sophia/rt/sr_thread.h"
#ifndef SR_THREAD_H_
#define SR_THREAD_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct srthread srthread;

typedef void *(*srthreadf)(void*);

struct srthread {
	pthread_t id;
	void *arg;
};

int sr_threadnew(srthread*, srthreadf, void*);
int sr_threadjoin(srthread*);

#endif
#line 1 "sophia/rt/sr_quota.h"
#ifndef SR_QUOTA_H_
#define SR_QUOTA_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct srquota srquota;

typedef enum srquotaop {
	SR_QADD,
	SR_QREMOVE
} srquotaop;

struct srquota {
	int enable;
	int wait;
	uint64_t limit;
	uint64_t used;
	srmutex lock;
	srcond cond;
};

int sr_quotainit(srquota*);
int sr_quotaset(srquota*, uint64_t);
int sr_quotaenable(srquota*, int);
int sr_quotafree(srquota*);
int sr_quota(srquota*, srquotaop, uint64_t);

static inline uint64_t
sr_quotaused(srquota *q)
{
	sr_mutexlock(&q->lock);
	uint64_t used = q->used;
	sr_mutexunlock(&q->lock);
	return used;
}

static inline int
sr_quotaused_percent(srquota *q)
{
	sr_mutexlock(&q->lock);
	int percent;
	if (q->limit == 0) {
		percent = 0;
	} else {
		percent = (q->used * 100) / q->limit;
	}
	sr_mutexunlock(&q->lock);
	return percent;
}

#endif
#line 1 "sophia/rt/sr_crc.h"
#ifndef SR_CRC_H_
#define SR_CRC_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

uint32_t sr_crc32c(uint32_t, const void*, int);

static inline uint32_t
sr_crcp(const void *p, int size, uint32_t crc)
{
	return sr_crc32c(crc, p, size);
}

static inline uint32_t
sr_crcs(const void *s, int size, uint32_t crc)
{
	return sr_crc32c(crc, (char*)s + sizeof(uint32_t),
	                 size - sizeof(uint32_t));
}

#endif
#line 1 "sophia/rt/sr_rb.h"
#ifndef SR_RB_H_
#define SR_RB_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct srrbnode srrbnode;
typedef struct srrb  srrb;

struct srrbnode {
	srrbnode *p, *l, *r;
	uint8_t color;
} srpacked;

struct srrb {
	srrbnode *root;
} srpacked;

static inline void
sr_rbinit(srrb *t) {
	t->root = NULL;
}

static inline void
sr_rbinitnode(srrbnode *n) {
	n->color = 2;
	n->p = NULL;
	n->l = NULL;
	n->r = NULL;
}

#define sr_rbget(name, compare) \
\
static inline int \
name(srrb *t, \
     srcomparator *cmp srunused, \
     void *key srunused, int keysize srunused, \
     srrbnode **match) \
{ \
	srrbnode *n = t->root; \
	*match = NULL; \
	int rc = 0; \
	while (n) { \
		*match = n; \
		switch ((rc = (compare))) { \
		case  0: return 0; \
		case -1: n = n->r; \
			break; \
		case  1: n = n->l; \
			break; \
		} \
	} \
	return rc; \
}

#define sr_rbtruncate(name, executable) \
\
static inline void \
name(srrbnode *n, void *arg) \
{ \
	if (n->l) \
		name(n->l, arg); \
	if (n->r) \
		name(n->r, arg); \
	executable; \
}

srrbnode *sr_rbmin(srrb*);
srrbnode *sr_rbmax(srrb*);
srrbnode *sr_rbnext(srrb*, srrbnode*);
srrbnode *sr_rbprev(srrb*, srrbnode*);

void sr_rbset(srrb*, srrbnode*, int, srrbnode*);
void sr_rbreplace(srrb*, srrbnode*, srrbnode*);
void sr_rbremove(srrb*, srrbnode*);

#endif
#line 1 "sophia/rt/sr_rq.h"
#ifndef SR_RQ_H_
#define SR_RQ_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

/* range queue */

typedef struct srrqnode srrqnode;
typedef struct srrqq srrqq;
typedef struct srrq srrq;

struct srrqnode {
	uint32_t q, v;
	srlist link;
};

struct srrqq {
	uint32_t count;
	uint32_t q;
	srlist list;
};

struct srrq {
	uint32_t range_count;
	uint32_t range;
	uint32_t last;
	srrqq *q;
};

static inline void
sr_rqinitnode(srrqnode *n) {
	sr_listinit(&n->link);
	n->q = UINT32_MAX;
	n->v = 0;
}

static inline int
sr_rqinit(srrq *q, sra *a, uint32_t range, uint32_t count)
{
	q->range_count = count + 1 /* zero */;
	q->range = range;
	q->q = sr_malloc(a, sizeof(srrqq) * q->range_count);
	if (srunlikely(q->q == NULL))
		return -1;
	uint32_t i = 0;
	while (i < q->range_count) {
		srrqq *p = &q->q[i];
		sr_listinit(&p->list);
		p->count = 0;
		p->q = i;
		i++;
	}
	q->last = 0;
	return 0;
}

static inline void
sr_rqfree(srrq *q, sra *a) {
	sr_free(a, q->q);
}

static inline void
sr_rqadd(srrq *q, srrqnode *n, uint32_t v)
{
	uint32_t pos;
	if (srunlikely(v == 0)) {
		pos = 0;
	} else {
		pos = (v / q->range) + 1;
		if (srunlikely(pos >= q->range_count))
			pos = q->range_count - 1;
	}
	srrqq *p = &q->q[pos];
	sr_listinit(&n->link);
	n->v = v;
	n->q = pos;
	sr_listappend(&p->list, &n->link);
	if (srunlikely(p->count == 0)) {
		if (pos > q->last)
			q->last = pos;
	}
	p->count++;
}

static inline void
sr_rqdelete(srrq *q, srrqnode *n)
{
	srrqq *p = &q->q[n->q];
	p->count--;
	sr_listunlink(&n->link);
	if (srunlikely(p->count == 0 && q->last == n->q))
	{
		int i = n->q - 1;
		while (i >= 0) {
			srrqq *p = &q->q[i];
			if (p->count > 0) {
				q->last = i;
				return;
			}
			i--;
		}
	}
}

static inline void
sr_rqupdate(srrq *q, srrqnode *n, uint32_t v)
{
	if (srlikely(n->q != UINT32_MAX))
		sr_rqdelete(q, n);
	sr_rqadd(q, n, v);
}

static inline srrqnode*
sr_rqprev(srrq *q, srrqnode *n)
{
	int pos;
	srrqq *p;
	if (srlikely(n)) {
		pos = n->q;
		p = &q->q[pos];
		if (n->link.next != (&p->list)) {
			return srcast(n->link.next, srrqnode, link);
		}
		pos--;
	} else {
		pos = q->last;
	}
	for (; pos >= 0; pos--) {
		p = &q->q[pos];
		if (srunlikely(p->count == 0))
			continue;
		return srcast(p->list.next, srrqnode, link);
	}
	return NULL;
}

#endif
#line 1 "sophia/rt/sr_path.h"
#ifndef SR_PATH_H_
#define SR_PATH_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct srpath srpath;

struct srpath {
	char path[PATH_MAX];
};

static inline void
sr_pathset(srpath *p, char *fmt, ...)
{
	va_list args;
	va_start(args, fmt);
	vsnprintf(p->path, sizeof(p->path), fmt, args);
	va_end(args);
}

static inline void
sr_pathA(srpath *p, char *dir, uint32_t id, char *ext)
{
	sr_pathset(p, "%s/%010"PRIu32"%s", dir, id, ext);
}

static inline void
sr_pathAB(srpath *p, char *dir, uint32_t a, uint32_t b, char *ext)
{
	sr_pathset(p, "%s/%010"PRIu32".%010"PRIu32"%s", dir, a, b, ext);
}

#endif
#line 1 "sophia/rt/sr_iov.h"
#ifndef SD_IOV_H_
#define SD_IOV_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sriov sriov;

struct sriov {
	struct iovec *v;
	int iovmax;
	int iovc;
};

static inline void
sr_iovinit(sriov *v, struct iovec *vp, int max)
{
	v->v = vp;
	v->iovc = 0;
	v->iovmax = max;
}

static inline int
sr_iovensure(sriov *v, int count) {
	return (v->iovc + count) < v->iovmax;
}

static inline int
sr_iovhas(sriov *v) {
	return v->iovc > 0;
}

static inline void
sr_iovreset(sriov *v) {
	v->iovc = 0;
}

static inline void
sr_iovadd(sriov *v, void *ptr, size_t size)
{
	assert(v->iovc < v->iovmax);
	v->v[v->iovc].iov_base = ptr;
	v->v[v->iovc].iov_len = size;
	v->iovc++;
}

#endif
#line 1 "sophia/rt/sr_file.h"
#ifndef SR_FILE_H_
#define SR_FILE_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct srfile srfile;

struct srfile {
	sra *a;
	int creat;
	uint64_t size;
	char *file;
	int fd;
};

static inline void
sr_fileinit(srfile *f, sra *a)
{
	memset(f, 0, sizeof(*f));
	f->a = a;
	f->fd = -1;
}

static inline uint64_t
sr_filesvp(srfile *f) {
	return f->size;
}

int sr_fileunlink(char*);
int sr_filemove(char*, char*);
int sr_fileexists(char*);
int sr_filemkdir(char*);
int sr_fileopen(srfile*, char*);
int sr_filenew(srfile*, char*);
int sr_filerename(srfile*, char*);
int sr_fileclose(srfile*);
int sr_filesync(srfile*);
int sr_fileresize(srfile*, uint64_t);
int sr_filepread(srfile*, uint64_t, void*, size_t);
int sr_filewrite(srfile*, void*, size_t);
int sr_filewritev(srfile*, sriov*);
int sr_fileseek(srfile*, uint64_t);
int sr_filelock(srfile*);
int sr_fileunlock(srfile*);
int sr_filerlb(srfile*, uint64_t);

#endif
#line 1 "sophia/rt/sr_dir.h"
#ifndef SR_DIR_H_
#define SR_DIR_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct srdirtype srdirtype;
typedef struct srdirid srdirid;

struct srdirtype {
	char *ext;
	uint32_t mask;
	int count;
};

struct srdirid {
	uint32_t mask;
	uint64_t id;
};

int sr_dirread(srbuf*, sra*, srdirtype*, char*);

#endif
#line 1 "sophia/rt/sr_map.h"
#ifndef SR_MAP_H_
#define SR_MAP_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct srmap srmap;

struct srmap {
	char *p;
	size_t size;
};

static inline void
sr_mapinit(srmap *m) {
	m->p = NULL;
	m->size = 0;
}

int sr_map(srmap*, int, uint64_t, int);
int sr_mapunmap(srmap*);

static inline int
sr_mapfile(srmap *map, srfile *f, int ro)
{
	return sr_map(map, f->fd, f->size, ro);
}

#endif
#line 1 "sophia/rt/sr_aslab.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/



typedef struct srsachunk srsachunk;
typedef struct srsa srsa;

struct srsachunk {
	srsachunk *next;
};

struct srsa {
	uint32_t chunk_max;
	uint32_t chunk_count;
	uint32_t chunk_used;
	uint32_t chunk_size;
	srsachunk *chunk;
	srpage *pu;
	srpager *pager;
} srpacked;

static inline int
sr_sagrow(srsa *s)
{
	register srpage *page = sr_pagerpop(s->pager);
	if (srunlikely(page == NULL))
		return -1;
	page->next = s->pu;
	s->pu = page;
	s->chunk_used = 0;
	return 0;
}

static inline int
sr_aslabclose(sra *a)
{
	srsa *s = (srsa*)a->priv;
	srpage *p_next, *p;
	p = s->pu;
	while (p) {
		p_next = p->next;
		sr_pagerpush(s->pager, p);
		p = p_next;
	}
	return 0;
}

static inline int
sr_aslabopen(sra *a, va_list args) {
	assert(sizeof(srsa) <= sizeof(a->priv));
	srsa *s = (srsa*)a->priv;
	memset(s, 0, sizeof(*s));
	s->pager       = va_arg(args, srpager*);
	s->chunk_size  = va_arg(args, uint32_t);
	s->chunk_count = 0;
	s->chunk_max   =
		(s->pager->page_size - sizeof(srpage)) /
	     (sizeof(srsachunk) + s->chunk_size);
	s->chunk_used  = 0;
	s->chunk       = NULL;
	s->pu          = NULL;
	int rc = sr_sagrow(s);
	if (srunlikely(rc == -1)) {
		sr_aslabclose(a);
		return -1;
	}
	return 0;
}

srhot static inline void*
sr_aslabmalloc(sra *a, int size srunused)
{
	srsa *s = (srsa*)a->priv;
	if (srlikely(s->chunk)) {
		register srsachunk *c = s->chunk;
		s->chunk = c->next;
		s->chunk_count++;
		c->next = NULL;
		return (char*)c + sizeof(srsachunk);
	}
	if (srunlikely(s->chunk_used == s->chunk_max)) {
		if (srunlikely(sr_sagrow(s) == -1))
			return NULL;
	}
	register int off = sizeof(srpage) +
		s->chunk_used * (sizeof(srsachunk) + s->chunk_size);
	register srsachunk *n =
		(srsachunk*)((char*)s->pu + off);
	s->chunk_used++;
	s->chunk_count++;
	n->next = NULL;
	return (char*)n + sizeof(srsachunk);
}

srhot static inline void
sr_aslabfree(sra *a, void *ptr)
{
	srsa *s = (srsa*)a->priv;
	register srsachunk *c =
		(srsachunk*)((char*)ptr - sizeof(srsachunk));
	c->next = s->chunk;
	s->chunk = c;
	s->chunk_count--;
}

sraif sr_aslab =
{
	.open    = sr_aslabopen,
	.close   = sr_aslabclose,
	.malloc  = sr_aslabmalloc,
	.realloc = NULL,
	.free    = sr_aslabfree 
};
#line 1 "sophia/rt/sr_astd.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/



static inline int
sr_astdopen(sra *a srunused, va_list args srunused) {
	return 0;
}

static inline int
sr_astdclose(sra *a srunused) {
	return 0;
}

static inline void*
sr_astdmalloc(sra *a srunused, int size) {
	return malloc(size);
}

static inline void*
sr_astdrealloc(sra *a srunused, void *ptr, int size) {
	return realloc(ptr,  size);
}

static inline void
sr_astdfree(sra *a srunused, void *ptr) {
	assert(ptr != NULL);
	free(ptr);
}

sraif sr_astd =
{
	.open    = sr_astdopen,
	.close   = sr_astdclose,
	.malloc  = sr_astdmalloc,
	.realloc = sr_astdrealloc,
	.free    = sr_astdfree 
};
#line 1 "sophia/rt/sr_bufiter.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/



typedef struct srbufiter srbufiter;

struct srbufiter {
	srbuf *buf;
	int vsize;
	void *v;
} srpacked;

static void
sr_bufiter_init(sriter *i)
{
	assert(sizeof(srbufiter) <= sizeof(i->priv));
	srbufiter *bi = (srbufiter*)i->priv;
	memset(bi, 0, sizeof(*bi));
}

static int
sr_bufiter_open(sriter *i, va_list args)
{
	srbufiter *bi = (srbufiter*)i->priv;
	bi->buf = va_arg(args, srbuf*);
	bi->vsize = va_arg(args, int);
	bi->v = bi->buf->s;
	if (srunlikely(bi->v == NULL))
		return 0;
	if (srunlikely(! sr_bufin(bi->buf, bi->v))) {
		bi->v = NULL;
		return 0;
	}
	return 1;
}

static void
sr_bufiter_close(sriter *i srunused)
{ }

static int
sr_bufiter_has(sriter *i)
{
	srbufiter *bi = (srbufiter*)i->priv;
	return bi->v != NULL;
}

static void*
sr_bufiter_of(sriter *i)
{
	srbufiter *bi = (srbufiter*)i->priv;
	return bi->v;
}

static void*
sr_bufiter_of_ref(sriter *i)
{
	srbufiter *bi = (srbufiter*)i->priv;
	if (srunlikely(bi->v == NULL))
		return NULL;
	return *(void**)bi->v;
}

static void
sr_bufiter_next(sriter *i)
{
	srbufiter *bi = (srbufiter*)i->priv;
	if (srunlikely(bi->v == NULL))
		return;
	bi->v = (char*)bi->v + bi->vsize;
	if (srunlikely(! sr_bufin(bi->buf, bi->v)))
		bi->v = NULL;
}

sriterif sr_bufiter =
{
	.init    = sr_bufiter_init,
	.open    = sr_bufiter_open,
	.close   = sr_bufiter_close,
	.has     = sr_bufiter_has,
	.of      = sr_bufiter_of,
	.next    = sr_bufiter_next
};

sriterif sr_bufiterref =
{
	.init    = sr_bufiter_init,
	.open    = sr_bufiter_open,
	.close   = sr_bufiter_close,
	.has     = sr_bufiter_has,
	.of      = sr_bufiter_of_ref,
	.next    = sr_bufiter_next
};
#line 1 "sophia/rt/sr_c.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/



static int
sr_cserializer(src *c, srcstmt *stmt, char *root, va_list args)
{
	char path[256];
	while (c) {
		if (root)
			snprintf(path, sizeof(path), "%s.%s", root, c->name);
		else
			snprintf(path, sizeof(path), "%s", c->name);
		int rc;
		int type = c->flags & ~SR_CRO;
		if (type == SR_CC) {
			rc = sr_cserializer(c->value, stmt, path, args);
			if (srunlikely(rc == -1))
				return -1;
		} else {
			stmt->path = path;
			rc = c->function(c, stmt, args);
			if (srunlikely(rc == -1))
				return -1;
			stmt->path = NULL;
		}
		c = c->next;
	}
	return 0;
}

int sr_cexecv(src *start, srcstmt *stmt, va_list args)
{
	if (stmt->op == SR_CSERIALIZE)
		return sr_cserializer(start, stmt, NULL, args);

	char path[256];
	snprintf(path, sizeof(path), "%s", stmt->path);
	char *ptr = NULL;
	char *token;
	token = strtok_r(path, ".", &ptr);
	if (srunlikely(token == NULL))
		return -1;
	src *c = start;
	while (c) {
		if (strcmp(token, c->name) != 0) {
			c = c->next;
			continue;
		}
		int type = c->flags & ~SR_CRO;
		switch (type) {
		case SR_CU32:
		case SR_CU64:
		case SR_CSZREF:
		case SR_CSZ:
		case SR_CVOID:
			token = strtok_r(NULL, ".", &ptr);
			if (srunlikely(token != NULL))
				goto error;
			return c->function(c, stmt, args);
		case SR_CC:
			token = strtok_r(NULL, ".", &ptr);
			if (srunlikely(token == NULL))
			{
				if (c->function)
					return c->function(c, stmt, args);
				/* not supported */
				goto error;
			}
			c = (src*)c->value;
			continue;
		}
		assert(0);
	}

error:
	sr_error(stmt->r->e, "bad ctl path: %s", stmt->path);
	return -1;
}

int sr_cserialize(src *c, srcstmt *stmt)
{
	void *value = NULL;
	int type = c->flags & ~SR_CRO;
	srcv v = {
		.type     = type,
		.namelen  = 0,
		.valuelen = 0
	};
	switch (type) {
	case SR_CU32:
		v.valuelen = sizeof(uint32_t);
		value = c->value;
		break;
	case SR_CU64:
		v.valuelen = sizeof(uint64_t);
		value = c->value;
		break;
	case SR_CSZREF: {
		char **sz = (char**)c->value;
		if (*sz)
			v.valuelen = strlen(*sz) + 1;
		value = *sz;
		v.type = SR_CSZ;
		break;
	}
	case SR_CSZ:
		value = c->value;
		if (value)
			v.valuelen = strlen(value) + 1;
		break;
	case SR_CVOID:
		v.valuelen = 0;
		break;
	default: assert(0);
	}
	char name[128];
	v.namelen  = snprintf(name, sizeof(name), "%s", stmt->path);
	v.namelen += 1;
	srbuf *buf = stmt->serialize;
	int size = sizeof(v) + v.namelen + v.valuelen;
	int rc = sr_bufensure(buf, stmt->r->a, size);
	if (srunlikely(rc == -1)) {
		sr_error(stmt->r->e, "%s", "memory allocation failed");
		return -1;
	}
	memcpy(buf->p, &v, sizeof(v));
	memcpy(buf->p + sizeof(v), name, v.namelen);
	memcpy(buf->p + sizeof(v) + v.namelen, value, v.valuelen);
	sr_bufadvance(buf, size);
	return 0;
}

static inline ssize_t sr_atoi(char *s)
{
	size_t v = 0;
	while (*s && *s != '.') {
		if (srunlikely(! isdigit(*s)))
			return -1;
		v = (v * 10) + *s - '0';
		s++;
	}
	return v;
}

int sr_cset(src *c, srcstmt *stmt, char *value)
{
	int type = c->flags & ~SR_CRO;
	if (c->flags & SR_CRO) {
		sr_error(stmt->r->e, "%s is read-only", stmt->path);
		return -1;
	}
	switch (type) {
	case SR_CU32:
		*((uint32_t*)c->value) = sr_atoi(value);
		break;
	case SR_CU64:
		*((uint64_t*)c->value) = sr_atoi(value);
		break;
	case SR_CSZREF: {
		char *nsz = NULL;
		if (value) {
			nsz = sr_strdup(stmt->r->a, value);
			if (srunlikely(nsz == NULL)) {
				sr_error(stmt->r->e, "%s", "memory allocation failed");
				return -1;
			}
		}
		char **sz = (char**)c->value;
		if (*sz)
			sr_free(stmt->r->a, *sz);
		*sz = nsz;
		break;
	}
	default: assert(0);
	}
	return 0;
}
#line 1 "sophia/rt/sr_cmp.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/



srhot int
sr_cmpu32(char *a, size_t asz, char *b, size_t bsz,
          void *arg srunused)
{
	(void)asz;
	(void)bsz;
	register uint32_t av = *(uint32_t*)a;
	register uint32_t bv = *(uint32_t*)b;
	if (av == bv)
		return 0;
	return (av > bv) ? 1 : -1;
}

srhot int
sr_cmpu64(char *a, size_t asz, char *b, size_t bsz,
          void *arg srunused)
{
	(void)asz;
	(void)bsz;
	register uint64_t av = *(uint64_t*)a;
	register uint64_t bv = *(uint64_t*)b;
	if (av == bv)
		return 0;
	return (av > bv) ? 1 : -1;
}

srhot int
sr_cmpstring(char *a, size_t asz, char *b, size_t bsz,
             void *arg srunused)
{
	register int size = (asz < bsz) ? asz : bsz;
	register int rc = memcmp(a, b, size);
	if (srunlikely(rc == 0)) {
		if (srlikely(asz == bsz))
			return 0;
		return (asz < bsz) ? -1 : 1;
	}
	return rc > 0 ? 1 : -1;
}

int sr_cmpset(srcomparator *c, char *name)
{
	if (strcmp(name, "u32") == 0) {
		c->cmp = sr_cmpu32;
		return 0;
	}
	if (strcmp(name, "u64") == 0) {
		c->cmp = sr_cmpu64;
		return 0;
	}
	if (strcmp(name, "string") == 0) {
		c->cmp = sr_cmpstring;
		return 0;
	}
	void *ptr = sr_triggerpointer_of(name);
	if (srunlikely(ptr == NULL))
		return -1;
	c->cmp = (srcmpf)(uintptr_t)ptr;
	return 0;
}

int sr_cmpsetarg(srcomparator *c, char *name)
{
	void *ptr = sr_triggerpointer_of(name);
	if (srunlikely(ptr == NULL))
		return -1;
	c->cmparg = ptr;
	return 0;
}
#line 1 "sophia/rt/sr_crc.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

/*
 * Copyright (c) 2008-2010 Massachusetts Institute of Technology
 * Copyright (c) 2004-2006 Intel Corporation
 *
 * This software program is licensed subject to the BSD License, 
 * available at http://www.opensource.org/licenses/bsd-license.html
*/



static const uint32_t crc_tableil8_o32[256] =
{
	0x00000000, 0xF26B8303, 0xE13B70F7, 0x1350F3F4, 0xC79A971F, 0x35F1141C, 0x26A1E7E8, 0xD4CA64EB,
	0x8AD958CF, 0x78B2DBCC, 0x6BE22838, 0x9989AB3B, 0x4D43CFD0, 0xBF284CD3, 0xAC78BF27, 0x5E133C24,
	0x105EC76F, 0xE235446C, 0xF165B798, 0x030E349B, 0xD7C45070, 0x25AFD373, 0x36FF2087, 0xC494A384,
	0x9A879FA0, 0x68EC1CA3, 0x7BBCEF57, 0x89D76C54, 0x5D1D08BF, 0xAF768BBC, 0xBC267848, 0x4E4DFB4B,
	0x20BD8EDE, 0xD2D60DDD, 0xC186FE29, 0x33ED7D2A, 0xE72719C1, 0x154C9AC2, 0x061C6936, 0xF477EA35,
	0xAA64D611, 0x580F5512, 0x4B5FA6E6, 0xB93425E5, 0x6DFE410E, 0x9F95C20D, 0x8CC531F9, 0x7EAEB2FA,
	0x30E349B1, 0xC288CAB2, 0xD1D83946, 0x23B3BA45, 0xF779DEAE, 0x05125DAD, 0x1642AE59, 0xE4292D5A,
	0xBA3A117E, 0x4851927D, 0x5B016189, 0xA96AE28A, 0x7DA08661, 0x8FCB0562, 0x9C9BF696, 0x6EF07595,
	0x417B1DBC, 0xB3109EBF, 0xA0406D4B, 0x522BEE48, 0x86E18AA3, 0x748A09A0, 0x67DAFA54, 0x95B17957,
	0xCBA24573, 0x39C9C670, 0x2A993584, 0xD8F2B687, 0x0C38D26C, 0xFE53516F, 0xED03A29B, 0x1F682198,
	0x5125DAD3, 0xA34E59D0, 0xB01EAA24, 0x42752927, 0x96BF4DCC, 0x64D4CECF, 0x77843D3B, 0x85EFBE38,
	0xDBFC821C, 0x2997011F, 0x3AC7F2EB, 0xC8AC71E8, 0x1C661503, 0xEE0D9600, 0xFD5D65F4, 0x0F36E6F7,
	0x61C69362, 0x93AD1061, 0x80FDE395, 0x72966096, 0xA65C047D, 0x5437877E, 0x4767748A, 0xB50CF789,
	0xEB1FCBAD, 0x197448AE, 0x0A24BB5A, 0xF84F3859, 0x2C855CB2, 0xDEEEDFB1, 0xCDBE2C45, 0x3FD5AF46,
	0x7198540D, 0x83F3D70E, 0x90A324FA, 0x62C8A7F9, 0xB602C312, 0x44694011, 0x5739B3E5, 0xA55230E6,
	0xFB410CC2, 0x092A8FC1, 0x1A7A7C35, 0xE811FF36, 0x3CDB9BDD, 0xCEB018DE, 0xDDE0EB2A, 0x2F8B6829,
	0x82F63B78, 0x709DB87B, 0x63CD4B8F, 0x91A6C88C, 0x456CAC67, 0xB7072F64, 0xA457DC90, 0x563C5F93,
	0x082F63B7, 0xFA44E0B4, 0xE9141340, 0x1B7F9043, 0xCFB5F4A8, 0x3DDE77AB, 0x2E8E845F, 0xDCE5075C,
	0x92A8FC17, 0x60C37F14, 0x73938CE0, 0x81F80FE3, 0x55326B08, 0xA759E80B, 0xB4091BFF, 0x466298FC,
	0x1871A4D8, 0xEA1A27DB, 0xF94AD42F, 0x0B21572C, 0xDFEB33C7, 0x2D80B0C4, 0x3ED04330, 0xCCBBC033,
	0xA24BB5A6, 0x502036A5, 0x4370C551, 0xB11B4652, 0x65D122B9, 0x97BAA1BA, 0x84EA524E, 0x7681D14D,
	0x2892ED69, 0xDAF96E6A, 0xC9A99D9E, 0x3BC21E9D, 0xEF087A76, 0x1D63F975, 0x0E330A81, 0xFC588982,
	0xB21572C9, 0x407EF1CA, 0x532E023E, 0xA145813D, 0x758FE5D6, 0x87E466D5, 0x94B49521, 0x66DF1622,
	0x38CC2A06, 0xCAA7A905, 0xD9F75AF1, 0x2B9CD9F2, 0xFF56BD19, 0x0D3D3E1A, 0x1E6DCDEE, 0xEC064EED,
	0xC38D26C4, 0x31E6A5C7, 0x22B65633, 0xD0DDD530, 0x0417B1DB, 0xF67C32D8, 0xE52CC12C, 0x1747422F,
	0x49547E0B, 0xBB3FFD08, 0xA86F0EFC, 0x5A048DFF, 0x8ECEE914, 0x7CA56A17, 0x6FF599E3, 0x9D9E1AE0,
	0xD3D3E1AB, 0x21B862A8, 0x32E8915C, 0xC083125F, 0x144976B4, 0xE622F5B7, 0xF5720643, 0x07198540,
	0x590AB964, 0xAB613A67, 0xB831C993, 0x4A5A4A90, 0x9E902E7B, 0x6CFBAD78, 0x7FAB5E8C, 0x8DC0DD8F,
	0xE330A81A, 0x115B2B19, 0x020BD8ED, 0xF0605BEE, 0x24AA3F05, 0xD6C1BC06, 0xC5914FF2, 0x37FACCF1,
	0x69E9F0D5, 0x9B8273D6, 0x88D28022, 0x7AB90321, 0xAE7367CA, 0x5C18E4C9, 0x4F48173D, 0xBD23943E,
	0xF36E6F75, 0x0105EC76, 0x12551F82, 0xE03E9C81, 0x34F4F86A, 0xC69F7B69, 0xD5CF889D, 0x27A40B9E,
	0x79B737BA, 0x8BDCB4B9, 0x988C474D, 0x6AE7C44E, 0xBE2DA0A5, 0x4C4623A6, 0x5F16D052, 0xAD7D5351
};

static const uint32_t crc_tableil8_o40[256] =
{
	0x00000000, 0x13A29877, 0x274530EE, 0x34E7A899, 0x4E8A61DC, 0x5D28F9AB, 0x69CF5132, 0x7A6DC945,
	0x9D14C3B8, 0x8EB65BCF, 0xBA51F356, 0xA9F36B21, 0xD39EA264, 0xC03C3A13, 0xF4DB928A, 0xE7790AFD,
	0x3FC5F181, 0x2C6769F6, 0x1880C16F, 0x0B225918, 0x714F905D, 0x62ED082A, 0x560AA0B3, 0x45A838C4,
	0xA2D13239, 0xB173AA4E, 0x859402D7, 0x96369AA0, 0xEC5B53E5, 0xFFF9CB92, 0xCB1E630B, 0xD8BCFB7C,
	0x7F8BE302, 0x6C297B75, 0x58CED3EC, 0x4B6C4B9B, 0x310182DE, 0x22A31AA9, 0x1644B230, 0x05E62A47,
	0xE29F20BA, 0xF13DB8CD, 0xC5DA1054, 0xD6788823, 0xAC154166, 0xBFB7D911, 0x8B507188, 0x98F2E9FF,
	0x404E1283, 0x53EC8AF4, 0x670B226D, 0x74A9BA1A, 0x0EC4735F, 0x1D66EB28, 0x298143B1, 0x3A23DBC6,
	0xDD5AD13B, 0xCEF8494C, 0xFA1FE1D5, 0xE9BD79A2, 0x93D0B0E7, 0x80722890, 0xB4958009, 0xA737187E,
	0xFF17C604, 0xECB55E73, 0xD852F6EA, 0xCBF06E9D, 0xB19DA7D8, 0xA23F3FAF, 0x96D89736, 0x857A0F41,
	0x620305BC, 0x71A19DCB, 0x45463552, 0x56E4AD25, 0x2C896460, 0x3F2BFC17, 0x0BCC548E, 0x186ECCF9,
	0xC0D23785, 0xD370AFF2, 0xE797076B, 0xF4359F1C, 0x8E585659, 0x9DFACE2E, 0xA91D66B7, 0xBABFFEC0,
	0x5DC6F43D, 0x4E646C4A, 0x7A83C4D3, 0x69215CA4, 0x134C95E1, 0x00EE0D96, 0x3409A50F, 0x27AB3D78,
	0x809C2506, 0x933EBD71, 0xA7D915E8, 0xB47B8D9F, 0xCE1644DA, 0xDDB4DCAD, 0xE9537434, 0xFAF1EC43,
	0x1D88E6BE, 0x0E2A7EC9, 0x3ACDD650, 0x296F4E27, 0x53028762, 0x40A01F15, 0x7447B78C, 0x67E52FFB,
	0xBF59D487, 0xACFB4CF0, 0x981CE469, 0x8BBE7C1E, 0xF1D3B55B, 0xE2712D2C, 0xD69685B5, 0xC5341DC2,
	0x224D173F, 0x31EF8F48, 0x050827D1, 0x16AABFA6, 0x6CC776E3, 0x7F65EE94, 0x4B82460D, 0x5820DE7A,
	0xFBC3FAF9, 0xE861628E, 0xDC86CA17, 0xCF245260, 0xB5499B25, 0xA6EB0352, 0x920CABCB, 0x81AE33BC,
	0x66D73941, 0x7575A136, 0x419209AF, 0x523091D8, 0x285D589D, 0x3BFFC0EA, 0x0F186873, 0x1CBAF004,
	0xC4060B78, 0xD7A4930F, 0xE3433B96, 0xF0E1A3E1, 0x8A8C6AA4, 0x992EF2D3, 0xADC95A4A, 0xBE6BC23D,
	0x5912C8C0, 0x4AB050B7, 0x7E57F82E, 0x6DF56059, 0x1798A91C, 0x043A316B, 0x30DD99F2, 0x237F0185,
	0x844819FB, 0x97EA818C, 0xA30D2915, 0xB0AFB162, 0xCAC27827, 0xD960E050, 0xED8748C9, 0xFE25D0BE,
	0x195CDA43, 0x0AFE4234, 0x3E19EAAD, 0x2DBB72DA, 0x57D6BB9F, 0x447423E8, 0x70938B71, 0x63311306,
	0xBB8DE87A, 0xA82F700D, 0x9CC8D894, 0x8F6A40E3, 0xF50789A6, 0xE6A511D1, 0xD242B948, 0xC1E0213F,
	0x26992BC2, 0x353BB3B5, 0x01DC1B2C, 0x127E835B, 0x68134A1E, 0x7BB1D269, 0x4F567AF0, 0x5CF4E287,
	0x04D43CFD, 0x1776A48A, 0x23910C13, 0x30339464, 0x4A5E5D21, 0x59FCC556, 0x6D1B6DCF, 0x7EB9F5B8,
	0x99C0FF45, 0x8A626732, 0xBE85CFAB, 0xAD2757DC, 0xD74A9E99, 0xC4E806EE, 0xF00FAE77, 0xE3AD3600,
	0x3B11CD7C, 0x28B3550B, 0x1C54FD92, 0x0FF665E5, 0x759BACA0, 0x663934D7, 0x52DE9C4E, 0x417C0439,
	0xA6050EC4, 0xB5A796B3, 0x81403E2A, 0x92E2A65D, 0xE88F6F18, 0xFB2DF76F, 0xCFCA5FF6, 0xDC68C781,
	0x7B5FDFFF, 0x68FD4788, 0x5C1AEF11, 0x4FB87766, 0x35D5BE23, 0x26772654, 0x12908ECD, 0x013216BA,
	0xE64B1C47, 0xF5E98430, 0xC10E2CA9, 0xD2ACB4DE, 0xA8C17D9B, 0xBB63E5EC, 0x8F844D75, 0x9C26D502,
	0x449A2E7E, 0x5738B609, 0x63DF1E90, 0x707D86E7, 0x0A104FA2, 0x19B2D7D5, 0x2D557F4C, 0x3EF7E73B,
	0xD98EEDC6, 0xCA2C75B1, 0xFECBDD28, 0xED69455F, 0x97048C1A, 0x84A6146D, 0xB041BCF4, 0xA3E32483
};

static const uint32_t crc_tableil8_o48[256] =
{
	0x00000000, 0xA541927E, 0x4F6F520D, 0xEA2EC073, 0x9EDEA41A, 0x3B9F3664, 0xD1B1F617, 0x74F06469,
	0x38513EC5, 0x9D10ACBB, 0x773E6CC8, 0xD27FFEB6, 0xA68F9ADF, 0x03CE08A1, 0xE9E0C8D2, 0x4CA15AAC,
	0x70A27D8A, 0xD5E3EFF4, 0x3FCD2F87, 0x9A8CBDF9, 0xEE7CD990, 0x4B3D4BEE, 0xA1138B9D, 0x045219E3,
	0x48F3434F, 0xEDB2D131, 0x079C1142, 0xA2DD833C, 0xD62DE755, 0x736C752B, 0x9942B558, 0x3C032726,
	0xE144FB14, 0x4405696A, 0xAE2BA919, 0x0B6A3B67, 0x7F9A5F0E, 0xDADBCD70, 0x30F50D03, 0x95B49F7D,
	0xD915C5D1, 0x7C5457AF, 0x967A97DC, 0x333B05A2, 0x47CB61CB, 0xE28AF3B5, 0x08A433C6, 0xADE5A1B8,
	0x91E6869E, 0x34A714E0, 0xDE89D493, 0x7BC846ED, 0x0F382284, 0xAA79B0FA, 0x40577089, 0xE516E2F7,
	0xA9B7B85B, 0x0CF62A25, 0xE6D8EA56, 0x43997828, 0x37691C41, 0x92288E3F, 0x78064E4C, 0xDD47DC32,
	0xC76580D9, 0x622412A7, 0x880AD2D4, 0x2D4B40AA, 0x59BB24C3, 0xFCFAB6BD, 0x16D476CE, 0xB395E4B0,
	0xFF34BE1C, 0x5A752C62, 0xB05BEC11, 0x151A7E6F, 0x61EA1A06, 0xC4AB8878, 0x2E85480B, 0x8BC4DA75,
	0xB7C7FD53, 0x12866F2D, 0xF8A8AF5E, 0x5DE93D20, 0x29195949, 0x8C58CB37, 0x66760B44, 0xC337993A,
	0x8F96C396, 0x2AD751E8, 0xC0F9919B, 0x65B803E5, 0x1148678C, 0xB409F5F2, 0x5E273581, 0xFB66A7FF,
	0x26217BCD, 0x8360E9B3, 0x694E29C0, 0xCC0FBBBE, 0xB8FFDFD7, 0x1DBE4DA9, 0xF7908DDA, 0x52D11FA4,
	0x1E704508, 0xBB31D776, 0x511F1705, 0xF45E857B, 0x80AEE112, 0x25EF736C, 0xCFC1B31F, 0x6A802161,
	0x56830647, 0xF3C29439, 0x19EC544A, 0xBCADC634, 0xC85DA25D, 0x6D1C3023, 0x8732F050, 0x2273622E,
	0x6ED23882, 0xCB93AAFC, 0x21BD6A8F, 0x84FCF8F1, 0xF00C9C98, 0x554D0EE6, 0xBF63CE95, 0x1A225CEB,
	0x8B277743, 0x2E66E53D, 0xC448254E, 0x6109B730, 0x15F9D359, 0xB0B84127, 0x5A968154, 0xFFD7132A,
	0xB3764986, 0x1637DBF8, 0xFC191B8B, 0x595889F5, 0x2DA8ED9C, 0x88E97FE2, 0x62C7BF91, 0xC7862DEF,
	0xFB850AC9, 0x5EC498B7, 0xB4EA58C4, 0x11ABCABA, 0x655BAED3, 0xC01A3CAD, 0x2A34FCDE, 0x8F756EA0,
	0xC3D4340C, 0x6695A672, 0x8CBB6601, 0x29FAF47F, 0x5D0A9016, 0xF84B0268, 0x1265C21B, 0xB7245065,
	0x6A638C57, 0xCF221E29, 0x250CDE5A, 0x804D4C24, 0xF4BD284D, 0x51FCBA33, 0xBBD27A40, 0x1E93E83E,
	0x5232B292, 0xF77320EC, 0x1D5DE09F, 0xB81C72E1, 0xCCEC1688, 0x69AD84F6, 0x83834485, 0x26C2D6FB,
	0x1AC1F1DD, 0xBF8063A3, 0x55AEA3D0, 0xF0EF31AE, 0x841F55C7, 0x215EC7B9, 0xCB7007CA, 0x6E3195B4,
	0x2290CF18, 0x87D15D66, 0x6DFF9D15, 0xC8BE0F6B, 0xBC4E6B02, 0x190FF97C, 0xF321390F, 0x5660AB71,
	0x4C42F79A, 0xE90365E4, 0x032DA597, 0xA66C37E9, 0xD29C5380, 0x77DDC1FE, 0x9DF3018D, 0x38B293F3,
	0x7413C95F, 0xD1525B21, 0x3B7C9B52, 0x9E3D092C, 0xEACD6D45, 0x4F8CFF3B, 0xA5A23F48, 0x00E3AD36,
	0x3CE08A10, 0x99A1186E, 0x738FD81D, 0xD6CE4A63, 0xA23E2E0A, 0x077FBC74, 0xED517C07, 0x4810EE79,
	0x04B1B4D5, 0xA1F026AB, 0x4BDEE6D8, 0xEE9F74A6, 0x9A6F10CF, 0x3F2E82B1, 0xD50042C2, 0x7041D0BC,
	0xAD060C8E, 0x08479EF0, 0xE2695E83, 0x4728CCFD, 0x33D8A894, 0x96993AEA, 0x7CB7FA99, 0xD9F668E7,
	0x9557324B, 0x3016A035, 0xDA386046, 0x7F79F238, 0x0B899651, 0xAEC8042F, 0x44E6C45C, 0xE1A75622,
	0xDDA47104, 0x78E5E37A, 0x92CB2309, 0x378AB177, 0x437AD51E, 0xE63B4760, 0x0C158713, 0xA954156D,
	0xE5F54FC1, 0x40B4DDBF, 0xAA9A1DCC, 0x0FDB8FB2, 0x7B2BEBDB, 0xDE6A79A5, 0x3444B9D6, 0x91052BA8
};

static const uint32_t crc_tableil8_o56[256] =
{
	0x00000000, 0xDD45AAB8, 0xBF672381, 0x62228939, 0x7B2231F3, 0xA6679B4B, 0xC4451272, 0x1900B8CA,
	0xF64463E6, 0x2B01C95E, 0x49234067, 0x9466EADF, 0x8D665215, 0x5023F8AD, 0x32017194, 0xEF44DB2C,
	0xE964B13D, 0x34211B85, 0x560392BC, 0x8B463804, 0x924680CE, 0x4F032A76, 0x2D21A34F, 0xF06409F7,
	0x1F20D2DB, 0xC2657863, 0xA047F15A, 0x7D025BE2, 0x6402E328, 0xB9474990, 0xDB65C0A9, 0x06206A11,
	0xD725148B, 0x0A60BE33, 0x6842370A, 0xB5079DB2, 0xAC072578, 0x71428FC0, 0x136006F9, 0xCE25AC41,
	0x2161776D, 0xFC24DDD5, 0x9E0654EC, 0x4343FE54, 0x5A43469E, 0x8706EC26, 0xE524651F, 0x3861CFA7,
	0x3E41A5B6, 0xE3040F0E, 0x81268637, 0x5C632C8F, 0x45639445, 0x98263EFD, 0xFA04B7C4, 0x27411D7C,
	0xC805C650, 0x15406CE8, 0x7762E5D1, 0xAA274F69, 0xB327F7A3, 0x6E625D1B, 0x0C40D422, 0xD1057E9A,
	0xABA65FE7, 0x76E3F55F, 0x14C17C66, 0xC984D6DE, 0xD0846E14, 0x0DC1C4AC, 0x6FE34D95, 0xB2A6E72D,
	0x5DE23C01, 0x80A796B9, 0xE2851F80, 0x3FC0B538, 0x26C00DF2, 0xFB85A74A, 0x99A72E73, 0x44E284CB,
	0x42C2EEDA, 0x9F874462, 0xFDA5CD5B, 0x20E067E3, 0x39E0DF29, 0xE4A57591, 0x8687FCA8, 0x5BC25610,
	0xB4868D3C, 0x69C32784, 0x0BE1AEBD, 0xD6A40405, 0xCFA4BCCF, 0x12E11677, 0x70C39F4E, 0xAD8635F6,
	0x7C834B6C, 0xA1C6E1D4, 0xC3E468ED, 0x1EA1C255, 0x07A17A9F, 0xDAE4D027, 0xB8C6591E, 0x6583F3A6,
	0x8AC7288A, 0x57828232, 0x35A00B0B, 0xE8E5A1B3, 0xF1E51979, 0x2CA0B3C1, 0x4E823AF8, 0x93C79040,
	0x95E7FA51, 0x48A250E9, 0x2A80D9D0, 0xF7C57368, 0xEEC5CBA2, 0x3380611A, 0x51A2E823, 0x8CE7429B,
	0x63A399B7, 0xBEE6330F, 0xDCC4BA36, 0x0181108E, 0x1881A844, 0xC5C402FC, 0xA7E68BC5, 0x7AA3217D,
	0x52A0C93F, 0x8FE56387, 0xEDC7EABE, 0x30824006, 0x2982F8CC, 0xF4C75274, 0x96E5DB4D, 0x4BA071F5,
	0xA4E4AAD9, 0x79A10061, 0x1B838958, 0xC6C623E0, 0xDFC69B2A, 0x02833192, 0x60A1B8AB, 0xBDE41213,
	0xBBC47802, 0x6681D2BA, 0x04A35B83, 0xD9E6F13B, 0xC0E649F1, 0x1DA3E349, 0x7F816A70, 0xA2C4C0C8,
	0x4D801BE4, 0x90C5B15C, 0xF2E73865, 0x2FA292DD, 0x36A22A17, 0xEBE780AF, 0x89C50996, 0x5480A32E,
	0x8585DDB4, 0x58C0770C, 0x3AE2FE35, 0xE7A7548D, 0xFEA7EC47, 0x23E246FF, 0x41C0CFC6, 0x9C85657E,
	0x73C1BE52, 0xAE8414EA, 0xCCA69DD3, 0x11E3376B, 0x08E38FA1, 0xD5A62519, 0xB784AC20, 0x6AC10698,
	0x6CE16C89, 0xB1A4C631, 0xD3864F08, 0x0EC3E5B0, 0x17C35D7A, 0xCA86F7C2, 0xA8A47EFB, 0x75E1D443,
	0x9AA50F6F, 0x47E0A5D7, 0x25C22CEE, 0xF8878656, 0xE1873E9C, 0x3CC29424, 0x5EE01D1D, 0x83A5B7A5,
	0xF90696D8, 0x24433C60, 0x4661B559, 0x9B241FE1, 0x8224A72B, 0x5F610D93, 0x3D4384AA, 0xE0062E12,
	0x0F42F53E, 0xD2075F86, 0xB025D6BF, 0x6D607C07, 0x7460C4CD, 0xA9256E75, 0xCB07E74C, 0x16424DF4,
	0x106227E5, 0xCD278D5D, 0xAF050464, 0x7240AEDC, 0x6B401616, 0xB605BCAE, 0xD4273597, 0x09629F2F,
	0xE6264403, 0x3B63EEBB, 0x59416782, 0x8404CD3A, 0x9D0475F0, 0x4041DF48, 0x22635671, 0xFF26FCC9,
	0x2E238253, 0xF36628EB, 0x9144A1D2, 0x4C010B6A, 0x5501B3A0, 0x88441918, 0xEA669021, 0x37233A99,
	0xD867E1B5, 0x05224B0D, 0x6700C234, 0xBA45688C, 0xA345D046, 0x7E007AFE, 0x1C22F3C7, 0xC167597F,
	0xC747336E, 0x1A0299D6, 0x782010EF, 0xA565BA57, 0xBC65029D, 0x6120A825, 0x0302211C, 0xDE478BA4,
	0x31035088, 0xEC46FA30, 0x8E647309, 0x5321D9B1, 0x4A21617B, 0x9764CBC3, 0xF54642FA, 0x2803E842
};

static const uint32_t crc_tableil8_o64[256] =
{
	0x00000000, 0x38116FAC, 0x7022DF58, 0x4833B0F4, 0xE045BEB0, 0xD854D11C, 0x906761E8, 0xA8760E44,
	0xC5670B91, 0xFD76643D, 0xB545D4C9, 0x8D54BB65, 0x2522B521, 0x1D33DA8D, 0x55006A79, 0x6D1105D5,
	0x8F2261D3, 0xB7330E7F, 0xFF00BE8B, 0xC711D127, 0x6F67DF63, 0x5776B0CF, 0x1F45003B, 0x27546F97,
	0x4A456A42, 0x725405EE, 0x3A67B51A, 0x0276DAB6, 0xAA00D4F2, 0x9211BB5E, 0xDA220BAA, 0xE2336406,
	0x1BA8B557, 0x23B9DAFB, 0x6B8A6A0F, 0x539B05A3, 0xFBED0BE7, 0xC3FC644B, 0x8BCFD4BF, 0xB3DEBB13,
	0xDECFBEC6, 0xE6DED16A, 0xAEED619E, 0x96FC0E32, 0x3E8A0076, 0x069B6FDA, 0x4EA8DF2E, 0x76B9B082,
	0x948AD484, 0xAC9BBB28, 0xE4A80BDC, 0xDCB96470, 0x74CF6A34, 0x4CDE0598, 0x04EDB56C, 0x3CFCDAC0,
	0x51EDDF15, 0x69FCB0B9, 0x21CF004D, 0x19DE6FE1, 0xB1A861A5, 0x89B90E09, 0xC18ABEFD, 0xF99BD151,
	0x37516AAE, 0x0F400502, 0x4773B5F6, 0x7F62DA5A, 0xD714D41E, 0xEF05BBB2, 0xA7360B46, 0x9F2764EA,
	0xF236613F, 0xCA270E93, 0x8214BE67, 0xBA05D1CB, 0x1273DF8F, 0x2A62B023, 0x625100D7, 0x5A406F7B,
	0xB8730B7D, 0x806264D1, 0xC851D425, 0xF040BB89, 0x5836B5CD, 0x6027DA61, 0x28146A95, 0x10050539,
	0x7D1400EC, 0x45056F40, 0x0D36DFB4, 0x3527B018, 0x9D51BE5C, 0xA540D1F0, 0xED736104, 0xD5620EA8,
	0x2CF9DFF9, 0x14E8B055, 0x5CDB00A1, 0x64CA6F0D, 0xCCBC6149, 0xF4AD0EE5, 0xBC9EBE11, 0x848FD1BD,
	0xE99ED468, 0xD18FBBC4, 0x99BC0B30, 0xA1AD649C, 0x09DB6AD8, 0x31CA0574, 0x79F9B580, 0x41E8DA2C,
	0xA3DBBE2A, 0x9BCAD186, 0xD3F96172, 0xEBE80EDE, 0x439E009A, 0x7B8F6F36, 0x33BCDFC2, 0x0BADB06E,
	0x66BCB5BB, 0x5EADDA17, 0x169E6AE3, 0x2E8F054F, 0x86F90B0B, 0xBEE864A7, 0xF6DBD453, 0xCECABBFF,
	0x6EA2D55C, 0x56B3BAF0, 0x1E800A04, 0x269165A8, 0x8EE76BEC, 0xB6F60440, 0xFEC5B4B4, 0xC6D4DB18,
	0xABC5DECD, 0x93D4B161, 0xDBE70195, 0xE3F66E39, 0x4B80607D, 0x73910FD1, 0x3BA2BF25, 0x03B3D089,
	0xE180B48F, 0xD991DB23, 0x91A26BD7, 0xA9B3047B, 0x01C50A3F, 0x39D46593, 0x71E7D567, 0x49F6BACB,
	0x24E7BF1E, 0x1CF6D0B2, 0x54C56046, 0x6CD40FEA, 0xC4A201AE, 0xFCB36E02, 0xB480DEF6, 0x8C91B15A,
	0x750A600B, 0x4D1B0FA7, 0x0528BF53, 0x3D39D0FF, 0x954FDEBB, 0xAD5EB117, 0xE56D01E3, 0xDD7C6E4F,
	0xB06D6B9A, 0x887C0436, 0xC04FB4C2, 0xF85EDB6E, 0x5028D52A, 0x6839BA86, 0x200A0A72, 0x181B65DE,
	0xFA2801D8, 0xC2396E74, 0x8A0ADE80, 0xB21BB12C, 0x1A6DBF68, 0x227CD0C4, 0x6A4F6030, 0x525E0F9C,
	0x3F4F0A49, 0x075E65E5, 0x4F6DD511, 0x777CBABD, 0xDF0AB4F9, 0xE71BDB55, 0xAF286BA1, 0x9739040D,
	0x59F3BFF2, 0x61E2D05E, 0x29D160AA, 0x11C00F06, 0xB9B60142, 0x81A76EEE, 0xC994DE1A, 0xF185B1B6,
	0x9C94B463, 0xA485DBCF, 0xECB66B3B, 0xD4A70497, 0x7CD10AD3, 0x44C0657F, 0x0CF3D58B, 0x34E2BA27,
	0xD6D1DE21, 0xEEC0B18D, 0xA6F30179, 0x9EE26ED5, 0x36946091, 0x0E850F3D, 0x46B6BFC9, 0x7EA7D065,
	0x13B6D5B0, 0x2BA7BA1C, 0x63940AE8, 0x5B856544, 0xF3F36B00, 0xCBE204AC, 0x83D1B458, 0xBBC0DBF4,
	0x425B0AA5, 0x7A4A6509, 0x3279D5FD, 0x0A68BA51, 0xA21EB415, 0x9A0FDBB9, 0xD23C6B4D, 0xEA2D04E1,
	0x873C0134, 0xBF2D6E98, 0xF71EDE6C, 0xCF0FB1C0, 0x6779BF84, 0x5F68D028, 0x175B60DC, 0x2F4A0F70,
	0xCD796B76, 0xF56804DA, 0xBD5BB42E, 0x854ADB82, 0x2D3CD5C6, 0x152DBA6A, 0x5D1E0A9E, 0x650F6532,
	0x081E60E7, 0x300F0F4B, 0x783CBFBF, 0x402DD013, 0xE85BDE57, 0xD04AB1FB, 0x9879010F, 0xA0686EA3
};

static const uint32_t crc_tableil8_o72[256] =
{
	0x00000000, 0xEF306B19, 0xDB8CA0C3, 0x34BCCBDA, 0xB2F53777, 0x5DC55C6E, 0x697997B4, 0x8649FCAD,
	0x6006181F, 0x8F367306, 0xBB8AB8DC, 0x54BAD3C5, 0xD2F32F68, 0x3DC34471, 0x097F8FAB, 0xE64FE4B2,
	0xC00C303E, 0x2F3C5B27, 0x1B8090FD, 0xF4B0FBE4, 0x72F90749, 0x9DC96C50, 0xA975A78A, 0x4645CC93,
	0xA00A2821, 0x4F3A4338, 0x7B8688E2, 0x94B6E3FB, 0x12FF1F56, 0xFDCF744F, 0xC973BF95, 0x2643D48C,
	0x85F4168D, 0x6AC47D94, 0x5E78B64E, 0xB148DD57, 0x370121FA, 0xD8314AE3, 0xEC8D8139, 0x03BDEA20,
	0xE5F20E92, 0x0AC2658B, 0x3E7EAE51, 0xD14EC548, 0x570739E5, 0xB83752FC, 0x8C8B9926, 0x63BBF23F,
	0x45F826B3, 0xAAC84DAA, 0x9E748670, 0x7144ED69, 0xF70D11C4, 0x183D7ADD, 0x2C81B107, 0xC3B1DA1E,
	0x25FE3EAC, 0xCACE55B5, 0xFE729E6F, 0x1142F576, 0x970B09DB, 0x783B62C2, 0x4C87A918, 0xA3B7C201,
	0x0E045BEB, 0xE13430F2, 0xD588FB28, 0x3AB89031, 0xBCF16C9C, 0x53C10785, 0x677DCC5F, 0x884DA746,
	0x6E0243F4, 0x813228ED, 0xB58EE337, 0x5ABE882E, 0xDCF77483, 0x33C71F9A, 0x077BD440, 0xE84BBF59,
	0xCE086BD5, 0x213800CC, 0x1584CB16, 0xFAB4A00F, 0x7CFD5CA2, 0x93CD37BB, 0xA771FC61, 0x48419778,
	0xAE0E73CA, 0x413E18D3, 0x7582D309, 0x9AB2B810, 0x1CFB44BD, 0xF3CB2FA4, 0xC777E47E, 0x28478F67,
	0x8BF04D66, 0x64C0267F, 0x507CEDA5, 0xBF4C86BC, 0x39057A11, 0xD6351108, 0xE289DAD2, 0x0DB9B1CB,
	0xEBF65579, 0x04C63E60, 0x307AF5BA, 0xDF4A9EA3, 0x5903620E, 0xB6330917, 0x828FC2CD, 0x6DBFA9D4,
	0x4BFC7D58, 0xA4CC1641, 0x9070DD9B, 0x7F40B682, 0xF9094A2F, 0x16392136, 0x2285EAEC, 0xCDB581F5,
	0x2BFA6547, 0xC4CA0E5E, 0xF076C584, 0x1F46AE9D, 0x990F5230, 0x763F3929, 0x4283F2F3, 0xADB399EA,
	0x1C08B7D6, 0xF338DCCF, 0xC7841715, 0x28B47C0C, 0xAEFD80A1, 0x41CDEBB8, 0x75712062, 0x9A414B7B,
	0x7C0EAFC9, 0x933EC4D0, 0xA7820F0A, 0x48B26413, 0xCEFB98BE, 0x21CBF3A7, 0x1577387D, 0xFA475364,
	0xDC0487E8, 0x3334ECF1, 0x0788272B, 0xE8B84C32, 0x6EF1B09F, 0x81C1DB86, 0xB57D105C, 0x5A4D7B45,
	0xBC029FF7, 0x5332F4EE, 0x678E3F34, 0x88BE542D, 0x0EF7A880, 0xE1C7C399, 0xD57B0843, 0x3A4B635A,
	0x99FCA15B, 0x76CCCA42, 0x42700198, 0xAD406A81, 0x2B09962C, 0xC439FD35, 0xF08536EF, 0x1FB55DF6,
	0xF9FAB944, 0x16CAD25D, 0x22761987, 0xCD46729E, 0x4B0F8E33, 0xA43FE52A, 0x90832EF0, 0x7FB345E9,
	0x59F09165, 0xB6C0FA7C, 0x827C31A6, 0x6D4C5ABF, 0xEB05A612, 0x0435CD0B, 0x308906D1, 0xDFB96DC8,
	0x39F6897A, 0xD6C6E263, 0xE27A29B9, 0x0D4A42A0, 0x8B03BE0D, 0x6433D514, 0x508F1ECE, 0xBFBF75D7,
	0x120CEC3D, 0xFD3C8724, 0xC9804CFE, 0x26B027E7, 0xA0F9DB4A, 0x4FC9B053, 0x7B757B89, 0x94451090,
	0x720AF422, 0x9D3A9F3B, 0xA98654E1, 0x46B63FF8, 0xC0FFC355, 0x2FCFA84C, 0x1B736396, 0xF443088F,
	0xD200DC03, 0x3D30B71A, 0x098C7CC0, 0xE6BC17D9, 0x60F5EB74, 0x8FC5806D, 0xBB794BB7, 0x544920AE,
	0xB206C41C, 0x5D36AF05, 0x698A64DF, 0x86BA0FC6, 0x00F3F36B, 0xEFC39872, 0xDB7F53A8, 0x344F38B1,
	0x97F8FAB0, 0x78C891A9, 0x4C745A73, 0xA344316A, 0x250DCDC7, 0xCA3DA6DE, 0xFE816D04, 0x11B1061D,
	0xF7FEE2AF, 0x18CE89B6, 0x2C72426C, 0xC3422975, 0x450BD5D8, 0xAA3BBEC1, 0x9E87751B, 0x71B71E02,
	0x57F4CA8E, 0xB8C4A197, 0x8C786A4D, 0x63480154, 0xE501FDF9, 0x0A3196E0, 0x3E8D5D3A, 0xD1BD3623,
	0x37F2D291, 0xD8C2B988, 0xEC7E7252, 0x034E194B, 0x8507E5E6, 0x6A378EFF, 0x5E8B4525, 0xB1BB2E3C
};

static const uint32_t crc_tableil8_o80[256] =
{
	0x00000000, 0x68032CC8, 0xD0065990, 0xB8057558, 0xA5E0C5D1, 0xCDE3E919, 0x75E69C41, 0x1DE5B089,
	0x4E2DFD53, 0x262ED19B, 0x9E2BA4C3, 0xF628880B, 0xEBCD3882, 0x83CE144A, 0x3BCB6112, 0x53C84DDA,
	0x9C5BFAA6, 0xF458D66E, 0x4C5DA336, 0x245E8FFE, 0x39BB3F77, 0x51B813BF, 0xE9BD66E7, 0x81BE4A2F,
	0xD27607F5, 0xBA752B3D, 0x02705E65, 0x6A7372AD, 0x7796C224, 0x1F95EEEC, 0xA7909BB4, 0xCF93B77C,
	0x3D5B83BD, 0x5558AF75, 0xED5DDA2D, 0x855EF6E5, 0x98BB466C, 0xF0B86AA4, 0x48BD1FFC, 0x20BE3334,
	0x73767EEE, 0x1B755226, 0xA370277E, 0xCB730BB6, 0xD696BB3F, 0xBE9597F7, 0x0690E2AF, 0x6E93CE67,
	0xA100791B, 0xC90355D3, 0x7106208B, 0x19050C43, 0x04E0BCCA, 0x6CE39002, 0xD4E6E55A, 0xBCE5C992,
	0xEF2D8448, 0x872EA880, 0x3F2BDDD8, 0x5728F110, 0x4ACD4199, 0x22CE6D51, 0x9ACB1809, 0xF2C834C1,
	0x7AB7077A, 0x12B42BB2, 0xAAB15EEA, 0xC2B27222, 0xDF57C2AB, 0xB754EE63, 0x0F519B3B, 0x6752B7F3,
	0x349AFA29, 0x5C99D6E1, 0xE49CA3B9, 0x8C9F8F71, 0x917A3FF8, 0xF9791330, 0x417C6668, 0x297F4AA0,
	0xE6ECFDDC, 0x8EEFD114, 0x36EAA44C, 0x5EE98884, 0x430C380D, 0x2B0F14C5, 0x930A619D, 0xFB094D55,
	0xA8C1008F, 0xC0C22C47, 0x78C7591F, 0x10C475D7, 0x0D21C55E, 0x6522E996, 0xDD279CCE, 0xB524B006,
	0x47EC84C7, 0x2FEFA80F, 0x97EADD57, 0xFFE9F19F, 0xE20C4116, 0x8A0F6DDE, 0x320A1886, 0x5A09344E,
	0x09C17994, 0x61C2555C, 0xD9C72004, 0xB1C40CCC, 0xAC21BC45, 0xC422908D, 0x7C27E5D5, 0x1424C91D,
	0xDBB77E61, 0xB3B452A9, 0x0BB127F1, 0x63B20B39, 0x7E57BBB0, 0x16549778, 0xAE51E220, 0xC652CEE8,
	0x959A8332, 0xFD99AFFA, 0x459CDAA2, 0x2D9FF66A, 0x307A46E3, 0x58796A2B, 0xE07C1F73, 0x887F33BB,
	0xF56E0EF4, 0x9D6D223C, 0x25685764, 0x4D6B7BAC, 0x508ECB25, 0x388DE7ED, 0x808892B5, 0xE88BBE7D,
	0xBB43F3A7, 0xD340DF6F, 0x6B45AA37, 0x034686FF, 0x1EA33676, 0x76A01ABE, 0xCEA56FE6, 0xA6A6432E,
	0x6935F452, 0x0136D89A, 0xB933ADC2, 0xD130810A, 0xCCD53183, 0xA4D61D4B, 0x1CD36813, 0x74D044DB,
	0x27180901, 0x4F1B25C9, 0xF71E5091, 0x9F1D7C59, 0x82F8CCD0, 0xEAFBE018, 0x52FE9540, 0x3AFDB988,
	0xC8358D49, 0xA036A181, 0x1833D4D9, 0x7030F811, 0x6DD54898, 0x05D66450, 0xBDD31108, 0xD5D03DC0,
	0x8618701A, 0xEE1B5CD2, 0x561E298A, 0x3E1D0542, 0x23F8B5CB, 0x4BFB9903, 0xF3FEEC5B, 0x9BFDC093,
	0x546E77EF, 0x3C6D5B27, 0x84682E7F, 0xEC6B02B7, 0xF18EB23E, 0x998D9EF6, 0x2188EBAE, 0x498BC766,
	0x1A438ABC, 0x7240A674, 0xCA45D32C, 0xA246FFE4, 0xBFA34F6D, 0xD7A063A5, 0x6FA516FD, 0x07A63A35,
	0x8FD9098E, 0xE7DA2546, 0x5FDF501E, 0x37DC7CD6, 0x2A39CC5F, 0x423AE097, 0xFA3F95CF, 0x923CB907,
	0xC1F4F4DD, 0xA9F7D815, 0x11F2AD4D, 0x79F18185, 0x6414310C, 0x0C171DC4, 0xB412689C, 0xDC114454,
	0x1382F328, 0x7B81DFE0, 0xC384AAB8, 0xAB878670, 0xB66236F9, 0xDE611A31, 0x66646F69, 0x0E6743A1,
	0x5DAF0E7B, 0x35AC22B3, 0x8DA957EB, 0xE5AA7B23, 0xF84FCBAA, 0x904CE762, 0x2849923A, 0x404ABEF2,
	0xB2828A33, 0xDA81A6FB, 0x6284D3A3, 0x0A87FF6B, 0x17624FE2, 0x7F61632A, 0xC7641672, 0xAF673ABA,
	0xFCAF7760, 0x94AC5BA8, 0x2CA92EF0, 0x44AA0238, 0x594FB2B1, 0x314C9E79, 0x8949EB21, 0xE14AC7E9,
	0x2ED97095, 0x46DA5C5D, 0xFEDF2905, 0x96DC05CD, 0x8B39B544, 0xE33A998C, 0x5B3FECD4, 0x333CC01C,
	0x60F48DC6, 0x08F7A10E, 0xB0F2D456, 0xD8F1F89E, 0xC5144817, 0xAD1764DF, 0x15121187, 0x7D113D4F
};

static const uint32_t crc_tableil8_o88[256] =
{
	0x00000000, 0x493C7D27, 0x9278FA4E, 0xDB448769, 0x211D826D, 0x6821FF4A, 0xB3657823, 0xFA590504,
	0x423B04DA, 0x0B0779FD, 0xD043FE94, 0x997F83B3, 0x632686B7, 0x2A1AFB90, 0xF15E7CF9, 0xB86201DE,
	0x847609B4, 0xCD4A7493, 0x160EF3FA, 0x5F328EDD, 0xA56B8BD9, 0xEC57F6FE, 0x37137197, 0x7E2F0CB0,
	0xC64D0D6E, 0x8F717049, 0x5435F720, 0x1D098A07, 0xE7508F03, 0xAE6CF224, 0x7528754D, 0x3C14086A,
	0x0D006599, 0x443C18BE, 0x9F789FD7, 0xD644E2F0, 0x2C1DE7F4, 0x65219AD3, 0xBE651DBA, 0xF759609D,
	0x4F3B6143, 0x06071C64, 0xDD439B0D, 0x947FE62A, 0x6E26E32E, 0x271A9E09, 0xFC5E1960, 0xB5626447,
	0x89766C2D, 0xC04A110A, 0x1B0E9663, 0x5232EB44, 0xA86BEE40, 0xE1579367, 0x3A13140E, 0x732F6929,
	0xCB4D68F7, 0x827115D0, 0x593592B9, 0x1009EF9E, 0xEA50EA9A, 0xA36C97BD, 0x782810D4, 0x31146DF3,
	0x1A00CB32, 0x533CB615, 0x8878317C, 0xC1444C5B, 0x3B1D495F, 0x72213478, 0xA965B311, 0xE059CE36,
	0x583BCFE8, 0x1107B2CF, 0xCA4335A6, 0x837F4881, 0x79264D85, 0x301A30A2, 0xEB5EB7CB, 0xA262CAEC,
	0x9E76C286, 0xD74ABFA1, 0x0C0E38C8, 0x453245EF, 0xBF6B40EB, 0xF6573DCC, 0x2D13BAA5, 0x642FC782,
	0xDC4DC65C, 0x9571BB7B, 0x4E353C12, 0x07094135, 0xFD504431, 0xB46C3916, 0x6F28BE7F, 0x2614C358,
	0x1700AEAB, 0x5E3CD38C, 0x857854E5, 0xCC4429C2, 0x361D2CC6, 0x7F2151E1, 0xA465D688, 0xED59ABAF,
	0x553BAA71, 0x1C07D756, 0xC743503F, 0x8E7F2D18, 0x7426281C, 0x3D1A553B, 0xE65ED252, 0xAF62AF75,
	0x9376A71F, 0xDA4ADA38, 0x010E5D51, 0x48322076, 0xB26B2572, 0xFB575855, 0x2013DF3C, 0x692FA21B,
	0xD14DA3C5, 0x9871DEE2, 0x4335598B, 0x0A0924AC, 0xF05021A8, 0xB96C5C8F, 0x6228DBE6, 0x2B14A6C1,
	0x34019664, 0x7D3DEB43, 0xA6796C2A, 0xEF45110D, 0x151C1409, 0x5C20692E, 0x8764EE47, 0xCE589360,
	0x763A92BE, 0x3F06EF99, 0xE44268F0, 0xAD7E15D7, 0x572710D3, 0x1E1B6DF4, 0xC55FEA9D, 0x8C6397BA,
	0xB0779FD0, 0xF94BE2F7, 0x220F659E, 0x6B3318B9, 0x916A1DBD, 0xD856609A, 0x0312E7F3, 0x4A2E9AD4,
	0xF24C9B0A, 0xBB70E62D, 0x60346144, 0x29081C63, 0xD3511967, 0x9A6D6440, 0x4129E329, 0x08159E0E,
	0x3901F3FD, 0x703D8EDA, 0xAB7909B3, 0xE2457494, 0x181C7190, 0x51200CB7, 0x8A648BDE, 0xC358F6F9,
	0x7B3AF727, 0x32068A00, 0xE9420D69, 0xA07E704E, 0x5A27754A, 0x131B086D, 0xC85F8F04, 0x8163F223,
	0xBD77FA49, 0xF44B876E, 0x2F0F0007, 0x66337D20, 0x9C6A7824, 0xD5560503, 0x0E12826A, 0x472EFF4D,
	0xFF4CFE93, 0xB67083B4, 0x6D3404DD, 0x240879FA, 0xDE517CFE, 0x976D01D9, 0x4C2986B0, 0x0515FB97,
	0x2E015D56, 0x673D2071, 0xBC79A718, 0xF545DA3F, 0x0F1CDF3B, 0x4620A21C, 0x9D642575, 0xD4585852,
	0x6C3A598C, 0x250624AB, 0xFE42A3C2, 0xB77EDEE5, 0x4D27DBE1, 0x041BA6C6, 0xDF5F21AF, 0x96635C88,
	0xAA7754E2, 0xE34B29C5, 0x380FAEAC, 0x7133D38B, 0x8B6AD68F, 0xC256ABA8, 0x19122CC1, 0x502E51E6,
	0xE84C5038, 0xA1702D1F, 0x7A34AA76, 0x3308D751, 0xC951D255, 0x806DAF72, 0x5B29281B, 0x1215553C,
	0x230138CF, 0x6A3D45E8, 0xB179C281, 0xF845BFA6, 0x021CBAA2, 0x4B20C785, 0x906440EC, 0xD9583DCB,
	0x613A3C15, 0x28064132, 0xF342C65B, 0xBA7EBB7C, 0x4027BE78, 0x091BC35F, 0xD25F4436, 0x9B633911,
	0xA777317B, 0xEE4B4C5C, 0x350FCB35, 0x7C33B612, 0x866AB316, 0xCF56CE31, 0x14124958, 0x5D2E347F,
	0xE54C35A1, 0xAC704886, 0x7734CFEF, 0x3E08B2C8, 0xC451B7CC, 0x8D6DCAEB, 0x56294D82, 0x1F1530A5
};

uint32_t sr_crc32c(uint32_t crc, const void *buf, int len)
{
	const char *p_buf = (const char*)buf;

	int initial_bytes = (sizeof(int32_t) - (intptr_t)p_buf) & (sizeof(int32_t) - 1);
	if (len < initial_bytes)
		initial_bytes = len;
	int li;
	for (li = 0; li < initial_bytes; li++)
		crc = crc_tableil8_o32[(crc ^ *p_buf++) & 0x000000FF] ^ (crc >> 8);

	len -= initial_bytes;
	int running_len = len & ~(sizeof(uint64_t) - 1);
	int end_bytes = len - running_len; 

	for (li = 0; li < running_len / 8; li++) {
		crc ^= *(uint32_t*)p_buf;
		p_buf += 4;
		uint32_t term1 = crc_tableil8_o88[(crc) & 0x000000FF] ^
		                 crc_tableil8_o80[(crc >> 8) & 0x000000FF];
		uint32_t term2 = crc >> 16;
		crc = term1 ^
		      crc_tableil8_o72[term2 & 0x000000FF] ^ 
		      crc_tableil8_o64[(term2 >> 8) & 0x000000FF];
		term1 = crc_tableil8_o56[(*(uint32_t*)p_buf) & 0x000000FF] ^
		        crc_tableil8_o48[((*(uint32_t*)p_buf) >> 8) & 0x000000FF];
		term2 = (*(uint32_t*)p_buf) >> 16;
		crc = crc ^ term1 ^
		      crc_tableil8_o40[term2 & 0x000000FF] ^
		      crc_tableil8_o32[(term2 >> 8) & 0x000000FF];
		p_buf += 4;
	}

    for (li = 0; li < end_bytes; li++)
        crc = crc_tableil8_o32[(crc ^ *p_buf++) & 0x000000FF] ^ (crc >> 8);
    return crc;
}
#line 1 "sophia/rt/sr_dir.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/



static inline ssize_t sr_diridof(char *s)
{
	size_t v = 0;
	while (*s && *s != '.') {
		if (srunlikely(!isdigit(*s)))
			return -1;
		v = (v * 10) + *s - '0';
		s++;
	}
	return v;
}

static inline srdirid*
sr_dirmatch(srbuf *list, uint64_t id)
{
	if (srunlikely(sr_bufused(list) == 0))
		return NULL;
	srdirid *n = (srdirid*)list->s;
	while ((char*)n < list->p) {
		if (n->id == id)
			return n;
		n++;
	}
	return NULL;
}

static inline srdirtype*
sr_dirtypeof(srdirtype *types, char *ext)
{
	srdirtype *p = &types[0];
	int n = 0;
	while (p[n].ext != NULL) {
		if (strcmp(p[n].ext, ext) == 0)
			return &p[n];
		n++;
	}
	return NULL;
}

static int
sr_dircmp(const void *p1, const void *p2)
{
	srdirid *a = (srdirid*)p1;
	srdirid *b = (srdirid*)p2;
	assert(a->id != b->id);
	return (a->id > b->id)? 1: -1;
}

int sr_dirread(srbuf *list, sra *a, srdirtype *types, char *dir)
{
	DIR *d = opendir(dir);
	if (srunlikely(d == NULL))
		return -1;

	struct dirent *de;
	while ((de = readdir(d))) {
		if (srunlikely(de->d_name[0] == '.'))
			continue;
		ssize_t id = sr_diridof(de->d_name);
		if (srunlikely(id == -1))
			goto error;
		char *ext = strstr(de->d_name, ".");
		if (srunlikely(ext == NULL))
			goto error;
		ext++;
		srdirtype *type = sr_dirtypeof(types, ext);
		if (srunlikely(type == NULL))
			continue;
		srdirid *n = sr_dirmatch(list, id);
		if (n) {
			n->mask |= type->mask;
			type->count++;
			continue;
		}
		int rc = sr_bufensure(list, a, sizeof(srdirid));
		if (srunlikely(rc == -1))
			goto error;
		n = (srdirid*)list->p;
		sr_bufadvance(list, sizeof(srdirid));
		n->id  = id;
		n->mask = type->mask;
		type->count++;
	}
	closedir(d);

	if (srunlikely(sr_bufused(list) == 0))
		return 0;

	int n = sr_bufused(list) / sizeof(srdirid);
	qsort(list->s, n, sizeof(srdirid), sr_dircmp);
	return n;

error:
	closedir(d);
	return -1;
}
#line 1 "sophia/rt/sr_file.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/



int sr_fileunlink(char *path)
{
	return unlink(path);
}

int sr_filemove(char *a, char *b)
{
	return rename(a, b);
}

int sr_fileexists(char *path)
{
	struct stat st;
	int rc = lstat(path, &st);
	return rc == 0;
}

int sr_filemkdir(char *path)
{
	return mkdir(path, 0750);
}

static inline int
sr_fileopenas(srfile *f, char *path, int flags)
{
	f->creat = (flags & O_CREAT ? 1 : 0);
	f->fd = open(path, flags, 0644);
	if (srunlikely(f->fd == -1))
		return -1;
	f->file = sr_strdup(f->a, path);
	if (srunlikely(f->file == NULL))
		goto err;
	f->size = 0;
	if (f->creat)
		return 0;
	struct stat st;
	int rc = lstat(path, &st);
	if (srunlikely(rc == -1))
		goto err;
	f->size = st.st_size;
	return 0;
err:
	if (f->file) {
		sr_free(f->a, f->file);
		f->file = NULL;
	}
	close(f->fd);
	f->fd = -1;
	return -1;
}

int sr_fileopen(srfile *f, char *path)
{
	return sr_fileopenas(f, path, O_RDWR);
}

int sr_filenew(srfile *f, char *path)
{
	return sr_fileopenas(f, path, O_RDWR|O_CREAT);
}

int sr_filerename(srfile *f, char *path)
{
	char *p = sr_strdup(f->a, path);
	if (srunlikely(p == NULL))
		return -1;
	int rc = sr_filemove(f->file, p);
	if (srunlikely(rc == -1)) {
		sr_free(f->a, p);
		return -1;
	}
	sr_free(f->a, f->file);
	f->file = p;
	return 0;
}

int sr_fileclose(srfile *f)
{
	if (srlikely(f->file)) {
		sr_free(f->a, f->file);
		f->file = NULL;
	}
	int rc;
	if (srunlikely(f->fd != -1)) {
		rc = close(f->fd);
		if (srunlikely(rc == -1))
			return -1;
		f->fd = -1;
	}
	return 0;
}

int sr_filesync(srfile *f)
{
#if defined(__APPLE__)
	return fcntl(f->fd, F_FULLFSYNC);
#else
	return fdatasync(f->fd);
#endif
}

int sr_fileresize(srfile *f, uint64_t size)
{
	int rc = ftruncate(f->fd, size);
	if (srunlikely(rc == -1))
		return -1;
	f->size = size;
	return 0;
}

int sr_filepread(srfile *f, uint64_t off, void *buf, size_t size)
{
	size_t n = 0;
	do {
		ssize_t r;
		do {
			r = pread(f->fd, (char*)buf + n, size - n, off + n);
		} while (r == -1 && errno == EINTR);
		if (r <= 0)
			return -1;
		n += r;
	} while (n != size);

	return 0;
}

int sr_filewrite(srfile *f, void *buf, size_t size)
{
	size_t n = 0;
	do {
		ssize_t r;
		do {
			r = write(f->fd, (char*)buf + n, size - n);
		} while (r == -1 && errno == EINTR);
		if (r <= 0)
			return -1;
		n += r;
	} while (n != size);
	f->size += size;
	return 0;
}

int sr_filewritev(srfile *f, sriov *iv)
{
	struct iovec *v = iv->v;
	int n = iv->iovc;
	uint64_t size = 0;
	do {
		int r;
		do {
			r = writev(f->fd, v, n);
		} while (r == -1 && errno == EINTR);
		if (r < 0)
			return -1;
		size += r;
		while (n > 0) {
			if (v->iov_len > (size_t)r) {
				v->iov_base = (char*)v->iov_base + r;
				v->iov_len -= r;
				break;
			} else {
				r -= v->iov_len;
				v++;
				n--;
			}
		}
	} while (n > 0);
	f->size += size;
	return 0;
}

int sr_fileseek(srfile *f, uint64_t off)
{
	return lseek(f->fd, off, SEEK_SET);
}

#if 0
int sr_filelock(srfile *f)
{
	struct flock l;
	memset(&l, 0, sizeof(l));
	l.l_whence = SEEK_SET;
	l.l_start = 0;
	l.l_len = 0;
	l.l_type = F_WRLCK;
	return fcntl(f->fd, F_SETLK, &l);
}

int sr_fileunlock(srfile *f)
{
	if (srunlikely(f->fd == -1))
		return 0;
	struct flock l;
	memset(&l, 0, sizeof(l));
	l.l_whence = SEEK_SET;
	l.l_start = 0;
	l.l_len = 0;
	l.l_type = F_UNLCK;
	return fcntl(f->fd, F_SETLK, &l);
}
#endif

int sr_filerlb(srfile *f, uint64_t svp)
{
	if (srunlikely(f->size == svp))
		return 0;
	int rc = ftruncate(f->fd, svp);
	if (srunlikely(rc == -1))
		return -1;
	f->size = svp;
	rc = sr_fileseek(f, f->size);
	if (srunlikely(rc == -1))
		return -1;
	return 0;
}
#line 1 "sophia/rt/sr_map.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/



int sr_map(srmap *m, int fd, uint64_t size, int ro)
{
	int flags = PROT_READ;
	if (! ro)
		flags |= PROT_WRITE;
	m->p = mmap(NULL, size, flags, MAP_SHARED, fd, 0);
	if (m->p == MAP_FAILED) {
		m->p = NULL;
		return -1;
	}
	m->size = size;
	return 0;
}

int sr_mapunmap(srmap *m)
{
	if (srunlikely(m->p == NULL))
		return 0;
	int rc = munmap(m->p, m->size);
	m->p = NULL;
	return rc;
}
#line 1 "sophia/rt/sr_pager.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/



void sr_pagerinit(srpager *p, uint32_t pool_count, uint32_t page_size)
{
	p->page_size  = sizeof(srpage) + page_size;
	p->pool_count = pool_count;
	p->pool_size  = sizeof(srpagepool) + pool_count * p->page_size;
	p->pools      = 0;
	p->pp         = NULL;
	p->p          = NULL;
}

void sr_pagerfree(srpager *p)
{
	srpagepool *pp_next, *pp = p->pp;
	while (pp) {
		pp_next = pp->next;
		munmap(pp, p->pool_size);
		pp = pp_next;
	}
}

static inline void
sr_pagerprefetch(srpager *p, srpagepool *pp)
{
	register srpage *start =
		(srpage*)((char*)pp + sizeof(srpagepool));
	register srpage *prev = start;
	register uint32_t i = 1;
	start->pool = pp;
	while (i < p->pool_count) {
		srpage *page =
			(srpage*)((char*)start + i * p->page_size);
		page->pool = pp;
		prev->next = page;
		prev = page;
		i++;
	}
	prev->next = NULL;
	p->p = start;
}

int sr_pageradd(srpager *p)
{
	srpagepool *pp =
		mmap(NULL, p->pool_size, PROT_READ|PROT_WRITE|PROT_EXEC,
	         MAP_PRIVATE|MAP_ANON, -1, 0);
	if (srunlikely(p == MAP_FAILED))
		return -1;
	pp->used = 0;
	pp->next = p->pp;
	p->pp = pp;
	p->pools++;
	sr_pagerprefetch(p, pp);
	return 0;
}

void *sr_pagerpop(srpager *p)
{
	if (p->p)
		goto fetch;
	if (srunlikely(sr_pageradd(p) == -1))
		return NULL;
fetch:;
	srpage *page = p->p;
	p->p = page->next;
	page->pool->used++;
	return page;
}

void sr_pagerpush(srpager *p, srpage *page)
{
	page->pool->used--;
	page->next = p->p;
	p->p = page;
}
#line 1 "sophia/rt/sr_quota.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/



int sr_quotainit(srquota *q)
{
	q->enable = 0;
	q->wait   = 0;
	q->limit  = 0;
	q->used   = 0;
	sr_mutexinit(&q->lock);
	sr_condinit(&q->cond);
	return 0;
}

int sr_quotaset(srquota *q, uint64_t limit)
{
	q->limit = limit;
	return 0;
}

int sr_quotaenable(srquota *q, int v)
{
	q->enable = v;
	return 0;
}

int sr_quotafree(srquota *q)
{
	sr_mutexfree(&q->lock);
	sr_condfree(&q->cond);
	return 0;
}

int sr_quota(srquota *q, srquotaop op, uint64_t v)
{
	sr_mutexlock(&q->lock);
	switch (op) {
	case SR_QADD:
		if (srunlikely(!q->enable || q->limit == 0)) {
			/* .. */
		} else {
			if (srunlikely((q->used + v) >= q->limit)) {
				q->wait++;
				sr_condwait(&q->cond, &q->lock);
			}
		}
		q->used += v;
		break;
	case SR_QREMOVE:
		q->used -= v;
		if (srunlikely(q->wait)) {
			q->wait--;
			sr_condsignal(&q->cond);
		}
		break;
	}
	sr_mutexunlock(&q->lock);
	return 0;
}
#line 1 "sophia/rt/sr_rb.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/



#define SR_RBBLACK 0
#define SR_RBRED   1
#define SR_RBUNDEF 2

srrbnode *sr_rbmin(srrb *t)
{
	srrbnode *n = t->root;
	if (srunlikely(n == NULL))
		return NULL;
	while (n->l)
		n = n->l;
	return n;
}

srrbnode *sr_rbmax(srrb *t)
{
	srrbnode *n = t->root;
	if (srunlikely(n == NULL))
		return NULL;
	while (n->r)
		n = n->r;
	return n;
}

srrbnode *sr_rbnext(srrb *t, srrbnode *n)
{
	if (srunlikely(n == NULL))
		return sr_rbmin(t);
	if (n->r) {
		n = n->r;
		while (n->l)
			n = n->l;
		return n;
	}
	srrbnode *p;
	while ((p = n->p) && p->r == n)
		n = p;
	return p;
}

srrbnode *sr_rbprev(srrb *t, srrbnode *n)
{
	if (srunlikely(n == NULL))
		return sr_rbmax(t);
	if (n->l) {
		n = n->l;
		while (n->r)
			n = n->r;
		return n;
	}
	srrbnode *p;
	while ((p = n->p) && p->l == n)
		n = p;
	return p;
}

static inline void
sr_rbrotate_left(srrb *t, srrbnode *n)
{
	srrbnode *p = n;
	srrbnode *q = n->r;
	srrbnode *parent = n->p;
	if (srlikely(p->p != NULL)) {
		if (parent->l == p)
			parent->l = q;
		else
			parent->r = q;
	} else {
		t->root = q;
	}
	q->p = parent;
	p->p = q;
	p->r = q->l;
	if (p->r)
		p->r->p = p;
	q->l = p;
}

static inline void
sr_rbrotate_right(srrb *t, srrbnode *n)
{
	srrbnode *p = n;
	srrbnode *q = n->l;
	srrbnode *parent = n->p;
	if (srlikely(p->p != NULL)) {
		if (parent->l == p)
			parent->l = q;
		else
			parent->r = q;
	} else {
		t->root = q;
	}
	q->p = parent;
	p->p = q;
	p->l = q->r;
	if (p->l)
		p->l->p = p;
	q->r = p;
}

static inline void
sr_rbset_fixup(srrb *t, srrbnode *n)
{
	srrbnode *p;
	while ((p = n->p) && (p->color == SR_RBRED))
	{
		srrbnode *g = p->p;
		if (p == g->l) {
			srrbnode *u = g->r;
			if (u && u->color == SR_RBRED) {
				g->color = SR_RBRED;
				p->color = SR_RBBLACK;
				u->color = SR_RBBLACK;
				n = g;
			} else {
				if (n == p->r) {
					sr_rbrotate_left(t, p);
					n = p;
					p = n->p;
				}
				g->color = SR_RBRED;
				p->color = SR_RBBLACK;
				sr_rbrotate_right(t, g);
			}
		} else {
			srrbnode *u = g->l;
			if (u && u->color == SR_RBRED) {
				g->color = SR_RBRED;
				p->color = SR_RBBLACK;
				u->color = SR_RBBLACK;
				n = g;
			} else {
				if (n == p->l) {
					sr_rbrotate_right(t, p);
					n = p;
					p = n->p;
				}
				g->color = SR_RBRED;
				p->color = SR_RBBLACK;
				sr_rbrotate_left(t, g);
			}
		}
	}
	t->root->color = SR_RBBLACK;
}

void sr_rbset(srrb *t, srrbnode *p, int prel, srrbnode *n)
{
	n->color = SR_RBRED;
	n->p     = p;
	n->l     = NULL;
	n->r     = NULL;
	if (srlikely(p)) {
		assert(prel != 0);
		if (prel > 0)
			p->l = n;
		else
			p->r = n;
	} else {
		t->root = n;
	}
	sr_rbset_fixup(t, n);
}

void sr_rbreplace(srrb *t, srrbnode *o, srrbnode *n)
{
	srrbnode *p = o->p;
	if (p) {
		if (p->l == o) {
			p->l = n;
		} else {
			p->r = n;
		}
	} else {
		t->root = n;
	}
	if (o->l)
		o->l->p = n;
	if (o->r)
		o->r->p = n;
	*n = *o;
}

void sr_rbremove(srrb *t, srrbnode *n)
{
	if (srunlikely(n->color == SR_RBUNDEF))
		return;
	srrbnode *l = n->l;
	srrbnode *r = n->r;
	srrbnode *x = NULL;
	if (l == NULL) {
		x = r;
	} else
	if (r == NULL) {
		x = l;
	} else {
		x = r;
		while (x->l)
			x = x->l;
	}
	srrbnode *p = n->p;
	if (p) {
		if (p->l == n) {
			p->l = x;
		} else {
			p->r = x;
		}
	} else {
		t->root = x;
	}
	uint8_t color;
	if (l && r) {
		color    = x->color;
		x->color = n->color;
		x->l     = l;
		l->p     = x;
		if (x != r) {
			p    = x->p;
			x->p = n->p;
			n    = x->r;
			p->l = n;
			x->r = r;
			r->p = x;
		} else {
			x->p = p;
			p    = x;
			n    = x->r;
		}
	} else {
		color = n->color;
		n     = x;
	}
	if (n)
		n->p = p;

	if (color == SR_RBRED)
		return;
	if (n && n->color == SR_RBRED) {
		n->color = SR_RBBLACK;
		return;
	}

	srrbnode *s;
	do {
		if (srunlikely(n == t->root))
			break;

		if (n == p->l) {
			s = p->r;
			if (s->color == SR_RBRED)
			{
				s->color = SR_RBBLACK;
				p->color = SR_RBRED;
				sr_rbrotate_left(t, p);
				s = p->r;
			}
			if ((!s->l || (s->l->color == SR_RBBLACK)) &&
			    (!s->r || (s->r->color == SR_RBBLACK)))
			{
				s->color = SR_RBRED;
				n = p;
				p = p->p;
				continue;
			}
			if ((!s->r || (s->r->color == SR_RBBLACK)))
			{
				s->l->color = SR_RBBLACK;
				s->color    = SR_RBRED;
				sr_rbrotate_right(t, s);
				s = p->r;
			}
			s->color    = p->color;
			p->color    = SR_RBBLACK;
			s->r->color = SR_RBBLACK;
			sr_rbrotate_left(t, p);
			n = t->root;
			break;
		} else {
			s = p->l;
			if (s->color == SR_RBRED)
			{
				s->color = SR_RBBLACK;
				p->color = SR_RBRED;
				sr_rbrotate_right(t, p);
				s = p->l;
			}
			if ((!s->l || (s->l->color == SR_RBBLACK)) &&
				(!s->r || (s->r->color == SR_RBBLACK)))
			{
				s->color = SR_RBRED;
				n = p;
				p = p->p;
				continue;
			}
			if ((!s->l || (s->l->color == SR_RBBLACK)))
			{
				s->r->color = SR_RBBLACK;
				s->color    = SR_RBRED;
				sr_rbrotate_left(t, s);
				s = p->l;
			}
			s->color    = p->color;
			p->color    = SR_RBBLACK;
			s->l->color = SR_RBBLACK;
			sr_rbrotate_right(t, p);
			n = t->root;
			break;
		}
	} while (n->color == SR_RBBLACK);
	if (n)
		n->color = SR_RBBLACK;
}
#line 1 "sophia/rt/sr_thread.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/



int sr_threadnew(srthread *t, srthreadf f, void *arg)
{
	t->arg = arg;
	return pthread_create(&t->id, NULL, f, t);
}

int sr_threadjoin(srthread *t)
{
	return pthread_join(t->id, NULL);
}
#line 1 "sophia/rt/sr_time.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/



void sr_sleep(uint64_t ns)
{
	struct timespec ts;
	ts.tv_sec  = 0;
	ts.tv_nsec = ns;
	nanosleep(&ts, NULL);
}

uint64_t sr_utime(void)
{
	struct timeval t;
	gettimeofday(&t, NULL);
	return t.tv_sec * 1000000ULL + t.tv_usec;
}
#line 1 "sophia/rt/sr_trigger.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/



void sr_triggerinit(srtrigger *t)
{
	t->func = NULL;
	t->arg = NULL;
}

void *sr_triggerpointer_of(char *name)
{
	if (strncmp(name, "pointer:", 8) != 0)
		return NULL;
	name += 8;
	errno = 0;
	char *end;
	unsigned long long int pointer = strtoull(name, &end, 16);
	if (pointer == 0 && end == name) {
		return NULL;
	} else
	if (pointer == ULLONG_MAX && errno) {
		return NULL;
	}
	return (void*)(uintptr_t)pointer;
}

int sr_triggerset(srtrigger *t, char *name)
{
	void *ptr = sr_triggerpointer_of(name);
	if (srunlikely(ptr == NULL))
		return -1;
	t->func = (srtriggerf)(uintptr_t)ptr;
	return 0;
}

int sr_triggersetarg(srtrigger *t, char *name)
{
	void *ptr = sr_triggerpointer_of(name);
	if (srunlikely(ptr == NULL))
		return -1;
	t->arg = ptr;
	return 0;
}
#line 1 "sophia/version/sv.h"
#ifndef SV_H_
#define SV_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

#define SVNONE   0
#define SVSET    1
#define SVDELETE 2
#define SVDUP    4
#define SVABORT  8
#define SVBEGIN  16

typedef struct svif svif;
typedef struct sv sv;

struct svif {
	uint8_t   (*flags)(sv*);
	void      (*flagsadd)(sv*, uint32_t);
	void      (*lsnset)(sv*, uint64_t);
	uint64_t  (*lsn)(sv*);
	char     *(*key)(sv*);
	uint16_t  (*keysize)(sv*);
	char     *(*value)(sv*);
	uint32_t  (*valuesize)(sv*);
	uint64_t  (*valueoffset)(sv*);
	char     *(*raw)(sv*);
	uint32_t  (*rawsize)(sv*);
	void      (*ref)(sv*);
	void      (*unref)(sv*, sra*);
};

struct sv {
	svif *i;
	void *v, *arg;
} srpacked;

static inline void
svinit(sv *v, svif *i, void *vptr, void *arg) {
	v->i   = i;
	v->v   = vptr;
	v->arg = arg;
}

static inline uint8_t
svflags(sv *v) {
	return v->i->flags(v);
}

static inline void
svflagsadd(sv *v, uint32_t flags) {
	v->i->flagsadd(v, flags);
}

static inline uint64_t
svlsn(sv *v) {
	return v->i->lsn(v);
}

static inline void
svlsnset(sv *v, uint64_t lsn) {
	v->i->lsnset(v, lsn);
}

static inline char*
svkey(sv *v) {
	return v->i->key(v);
}

static inline uint16_t
svkeysize(sv *v) {
	return v->i->keysize(v);
}

static inline char*
svvalue(sv *v) {
	return v->i->value(v);
}

static inline uint32_t
svvaluesize(sv *v) {
	return v->i->valuesize(v);
}

static inline uint64_t
svvalueoffset(sv *v) {
	return v->i->valueoffset(v);
}

static inline char*
svraw(sv *v) {
	return v->i->raw(v);
}

static inline uint32_t
svrawsize(sv *v) {
	return v->i->rawsize(v);
}

static inline void
svref(sv *v) {
	v->i->ref(v);
}

static inline void
svunref(sv *v, sra *a) {
	v->i->unref(v, a);
}

static inline int
svcompare(sv *a, sv *b, srcomparator *c) {
	return sr_compare(c, svkey(a), svkeysize(a),
	                     svkey(b), svkeysize(b));
}

#endif
#line 1 "sophia/version/sv_local.h"
#ifndef SV_LOCAL_H_
#define SV_LOCAL_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct svlocal svlocal;

struct svlocal {
	uint64_t lsn;
	uint8_t  flags;
	uint16_t keysize;
	uint32_t valuesize;
	void *key;
	void *value;
};

extern svif sv_localif;

static inline svlocal*
sv_copy(sra *a, sv *v)
{
	int keysize = svkeysize(v);
	int valuesize = svvaluesize(v);
	int size = sizeof(svlocal) + keysize + valuesize;
	svlocal *l = sr_malloc(a, size);
	if (srunlikely(l == NULL))
		return NULL;
	char *key = (char*)l + sizeof(svlocal);
	l->lsn       = svlsn(v);
	l->flags     = svflags(v);
	l->key       = key;
	l->keysize   = keysize; 
	l->value     = key + keysize;
	l->valuesize = valuesize;
	memcpy(key, svkey(v), l->keysize);
	memcpy(key + keysize, svvalue(v), valuesize);
	return l;
}

#endif
#line 1 "sophia/version/sv_log.h"
#ifndef SV_LOG_H_
#define SV_LOG_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct svlogindex svlogindex;
typedef struct svlogv svlogv;
typedef struct svlog svlog;

struct svlogindex {
	uint32_t id;
	uint32_t head, tail;
	uint32_t count;
	void *ptr;
} srpacked;

struct svlogv {
	sv v;
	uint32_t id;
	uint32_t next;
} srpacked;

struct svlog {
	svlogindex reserve_i[4];
	svlogv reserve_v[16];
	srbuf index;
	srbuf buf;
};

static inline void
sv_loginit(svlog *l)
{
	sr_bufinit_reserve(&l->index, l->reserve_i, sizeof(l->reserve_i));
	sr_bufinit_reserve(&l->buf, l->reserve_v, sizeof(l->reserve_v));
}

static inline void
sv_logfree(svlog *l, sra *a)
{
	sr_buffree(&l->buf, a);
	sr_buffree(&l->index, a);
}

static inline int
sv_logcount(svlog *l) {
	return sr_bufused(&l->buf) / sizeof(svlogv);
}

static inline svlogv*
sv_logat(svlog *l, int pos) {
	return sr_bufat(&l->buf, sizeof(svlogv), pos);
}

static inline int
sv_logadd(svlog *l, sra *a, svlogv *v, void *ptr)
{
	uint32_t n = sv_logcount(l);
	int rc = sr_bufadd(&l->buf, a, v, sizeof(svlogv));
	if (srunlikely(rc == -1))
		return -1;
	svlogindex *i = (svlogindex*)l->index.s;
	while ((char*)i < l->index.p) {
		if (srlikely(i->id == v->id)) {
			svlogv *tail = sv_logat(l, i->tail);
			tail->next = n;
			i->tail = n;
			i->count++;
			return 0;
		}
		i++;
	}
	rc = sr_bufensure(&l->index, a, sizeof(svlogindex));
	if (srunlikely(rc == -1)) {
		l->buf.p -= sizeof(svlogv);
		return -1;
	}
	i = (svlogindex*)l->index.p;
	i->id    = v->id;
	i->head  = n;
	i->tail  = n;
	i->ptr   = ptr;
	i->count = 1;
	sr_bufadvance(&l->index, sizeof(svlogindex));
	return 0;
}

static inline void
sv_logreplace(svlog *l, int n, svlogv *v)
{
	sr_bufset(&l->buf, sizeof(svlogv), n, (char*)v, sizeof(svlogv));
}

#endif
#line 1 "sophia/version/sv_mergeiter.h"
#ifndef SV_MERGEITER_H_
#define SV_MERGEITER_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct svmergesrc svmergesrc;
typedef struct svmerge svmerge;

struct svmergesrc {
	sriter *i, src;
	uint8_t dup;
	void *ptr;
} srpacked;

struct svmerge {
	srbuf buf;
};

static inline void
sv_mergeinit(svmerge *m) {
	sr_bufinit(&m->buf);
}

static inline int
sv_mergeprepare(svmerge *m, sr *r, int count) {
	int rc = sr_bufensure(&m->buf, r->a, sizeof(svmergesrc) * count);
	if (srunlikely(rc == -1))
		return sr_error(r->e, "%s", "memory allocation failed");
	return 0;
}

static inline void
sv_mergefree(svmerge *m, sra *a) {
	sr_buffree(&m->buf, a);
}

static inline void
sv_mergereset(svmerge *m) {
	m->buf.p = m->buf.s;
}

static inline svmergesrc*
sv_mergeadd(svmerge *m, sriter *i)
{
	assert(m->buf.p < m->buf.e);
	svmergesrc *s = (svmergesrc*)m->buf.p;
	s->dup = 0;
	s->i = i;
	s->ptr = NULL;
	if (i == NULL)
		s->i = &s->src;
	sr_bufadvance(&m->buf, sizeof(svmergesrc));
	return s;
}

static inline svmergesrc*
sv_mergenextof(svmergesrc *src) {
	return (svmergesrc*)((char*)src + sizeof(svmergesrc));
}

uint32_t sv_mergeisdup(sriter*);

extern sriterif sv_mergeiter;

#endif
#line 1 "sophia/version/sv_readiter.h"
#ifndef SV_READITER_H_
#define SV_READITER_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

extern sriterif sv_readiter;

#endif
#line 1 "sophia/version/sv_writeiter.h"
#ifndef SV_WRITEITER_H_
#define SV_WRITEITER_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

extern sriterif sv_writeiter;

int      sv_writeiter_resume(sriter*);
uint32_t sv_writeiter_total(sriter*);

#endif
#line 1 "sophia/version/sv_v.h"
#ifndef SV_V_H_
#define SV_V_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct svv svv;

struct svv {
	uint64_t  lsn;
	uint32_t  valuesize;
	uint16_t  keysize;
	uint8_t   flags;
	void     *log;
	svv      *next;
	srrbnode node;
} srpacked;

extern svif sv_vif;

static inline char*
sv_vkey(svv *v) {
	return (char*)(v) + sizeof(svv);
}

static inline void*
sv_vvalue(svv *v) {
	return (char*)(v) + sizeof(svv) + v->keysize;
}

static inline svv*
sv_valloc(sra *a, sv *v)
{
	int keysize = svkeysize(v);
	int valuesize = svvaluesize(v);
	int size = sizeof(svv) + keysize + valuesize;
	svv *vv = sr_malloc(a, size);
	if (srunlikely(vv == NULL))
		return NULL;
	vv->keysize   = keysize; 
	vv->valuesize = valuesize;
	vv->flags     = svflags(v);
	vv->lsn       = svlsn(v);
	vv->next      = NULL;
	vv->log       = NULL;
	memset(&vv->node, 0, sizeof(vv->node));
	char *key = sv_vkey(vv);
	memcpy(key, svkey(v), keysize);
	memcpy(key + keysize, svvalue(v), valuesize);
	return vv;
}

static inline void
sv_vfree(sra *a, svv *v)
{
	while (v) {
		svv *n = v->next;
		sr_free(a, v);
		v = n;
	}
}

static inline svv*
sv_visible(svv *v, uint64_t vlsn) {
	while (v && v->lsn > vlsn)
		v = v->next;
	return v;
}

static inline uint32_t
sv_vsize(svv *v) {
	return sizeof(svv) + v->keysize + v->valuesize;
}

static inline uint32_t
sv_vsizeof(sv *v) {
	return sizeof(svv) + svkeysize(v) + svvaluesize(v);
}

#endif
#line 1 "sophia/version/sv_index.h"
#ifndef SC_INDEX_H_
#define SC_INDEX_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct svindex svindex;

struct svindex {
	srrb i;
	uint32_t count;
	uint32_t used;
	uint16_t keymax;
	uint64_t lsnmin;
} srpacked;

sr_rbget(sv_indexmatch,
         sr_compare(cmp, sv_vkey(srcast(n, svv, node)),
                    (srcast(n, svv, node))->keysize,
                    key, keysize))

int sv_indexinit(svindex*);
int sv_indexfree(svindex*, sr*);
int sv_indexset(svindex*, sr*, uint64_t, svv*, svv**);

static inline uint32_t
sv_indexused(svindex *i) {
	return i->count * sizeof(svv) + i->used;
}

#endif
#line 1 "sophia/version/sv_indexiter.h"
#ifndef SV_INDEXITER_H_
#define SV_INDEXITER_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

extern sriterif sv_indexiter;
extern sriterif sv_indexiterraw;

#endif
#line 1 "sophia/version/sv_index.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/




sr_rbtruncate(sv_indextruncate,
              sv_vfree((sra*)arg, srcast(n, svv, node)))

int sv_indexinit(svindex *i)
{
	i->keymax = 0;
	i->lsnmin = UINT64_MAX;
	i->count  = 0;
	i->used   = 0;
	sr_rbinit(&i->i);
	return 0;
}

int sv_indexfree(svindex *i, sr *r)
{
	if (i->i.root)
		sv_indextruncate(i->i.root, r->a);
	sr_rbinit(&i->i);
	return 0;
}

static inline svv*
sv_vset(svv *head, svv *v)
{
	/* default */
	if (srlikely(head->lsn < v->lsn)) {
		v->next = head;
		head->flags |= SVDUP;
		return v;
	}
	/* redistribution (starting from highest lsn) */
	svv *prev = head;
	svv *c = head->next;
	while (c) {
		assert(c->lsn != v->lsn);
		if (c->lsn < v->lsn)
			break;
		prev = c;
		c = c->next;
	}
	prev->next = v;
	v->next = c;
	v->flags |= SVDUP;
	return head;
}

#if 0
static inline svv*
sv_vgc(svv *v, uint64_t vlsn)
{
	svv *prev = v;
	svv *c = v->next;
	while (c) {
		if (c->lsn < vlsn) {
			prev->next = NULL;
			return c;
		}
		prev = c;
		c = c->next;
	}
	return NULL;
}

static inline uint32_t
sv_vstat(svv *v, uint32_t *count) {
	uint32_t size = 0;
	*count = 0;
	while (v) {
		size += v->keysize + v->valuesize;
		(*count)++;
		v = v->next;
	}
	return size;
}
#endif

int sv_indexset(svindex *i, sr *r, uint64_t vlsn srunused,
                svv  *v,
                svv **gc srunused)
{
	srrbnode *n = NULL;
	svv *head = NULL;
	if (v->lsn < i->lsnmin)
		i->lsnmin = v->lsn;
	int rc = sv_indexmatch(&i->i, r->cmp, sv_vkey(v), v->keysize, &n);
	if (rc == 0 && n) {
		head = srcast(n, svv, node);
		svv *update = sv_vset(head, v);
		if (head != update)
			sr_rbreplace(&i->i, n, &update->node);
#if 0
		*gc = sv_vgc(update, vlsn);
		if (*gc) {
			uint32_t count = 0;
			i->used  -= sv_vstat(*gc, &count);
			i->count -= count;
		}
#endif
	} else {
		sr_rbset(&i->i, n, rc, &v->node);
	}
	i->count++;
	i->used += v->keysize + v->valuesize;
	if (srunlikely(v->keysize > i->keymax))
		i->keymax = v->keysize;
	return 0;
}
#line 1 "sophia/version/sv_indexiter.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/




typedef struct svindexiter svindexiter;

struct svindexiter {
	svindex *index;
	srrbnode *v;
	svv *vcur;
	sv current;
	srorder order;
	void *key;
	int keysize;
	uint64_t vlsn;
} srpacked;

static void
sv_indexiter_init(sriter *i)
{
	assert(sizeof(svindexiter) <= sizeof(i->priv));

	svindexiter *ii = (svindexiter*)i->priv;
	memset(ii, 0, sizeof(*ii));
}

static inline void
sv_indexiter_fwd(svindexiter *i)
{
	while (i->v) {
		svv *v = srcast(i->v, svv, node);
		i->vcur = sv_visible(v, i->vlsn);
		if (srlikely(i->vcur))
			return;
		i->v = sr_rbnext(&i->index->i, i->v);
	}
}

static inline void
sv_indexiter_bkw(svindexiter *i)
{
	while (i->v) {
		svv *v = srcast(i->v, svv, node);
		i->vcur = sv_visible(v, i->vlsn);
		if (srlikely(i->vcur))
			return;
		i->v = sr_rbprev(&i->index->i, i->v);
	}
}

static int
sv_indexiter_open(sriter *i, va_list args)
{
	svindexiter *ii = (svindexiter*)i->priv;
	ii->index   = va_arg(args, svindex*);
	ii->order   = va_arg(args, srorder);
	ii->key     = va_arg(args, void*);
	ii->keysize = va_arg(args, int);
	ii->vlsn    = va_arg(args, uint64_t);
	srrbnode *n = NULL;
	int eq = 0;
	int rc;
	switch (ii->order) {
	case SR_LT:
	case SR_LTE:
	case SR_EQ:
		if (srunlikely(ii->key == NULL)) {
			ii->v = sr_rbmax(&ii->index->i);
			sv_indexiter_bkw(ii);
			break;
		}
		rc = sv_indexmatch(&ii->index->i, i->r->cmp, ii->key, ii->keysize, &ii->v);
		if (ii->v == NULL)
			break;
		switch (rc) {
		case 0:
			eq = 1;
			if (ii->order == SR_LT)
				ii->v = sr_rbprev(&ii->index->i, ii->v);
			break;
		case 1:
			ii->v = sr_rbprev(&ii->index->i, ii->v);
			break;
		}
		n = ii->v;
		sv_indexiter_bkw(ii);
		break;
	case SR_GT:
	case SR_GTE:
		if (srunlikely(ii->key == NULL)) {
			ii->v = sr_rbmin(&ii->index->i);
			sv_indexiter_fwd(ii);
			break;
		}
		rc = sv_indexmatch(&ii->index->i, i->r->cmp, ii->key, ii->keysize, &ii->v);
		if (ii->v == NULL)
			break;
		switch (rc) {
		case  0:
			eq = 1;
			if (ii->order == SR_GT)
				ii->v = sr_rbnext(&ii->index->i, ii->v);
			break;
		case -1:
			ii->v = sr_rbnext(&ii->index->i, ii->v);
			break;
		}
		n = ii->v;
		sv_indexiter_fwd(ii);
		break;
	case SR_RANDOM: {
		assert(ii->key != NULL);
		if (srunlikely(ii->index->count == 0)) {
			ii->v = NULL;
			ii->vcur = NULL;
			break;
		}
		uint32_t rnd = *(uint32_t*)ii->key;
		rnd %= ii->index->count;
		ii->v = sr_rbmin(&ii->index->i);
		uint32_t pos = 0;
		while (pos != rnd) {
			ii->v = sr_rbnext(&ii->index->i, ii->v);
			pos++;
		}
		svv *v = srcast(ii->v, svv, node);
		ii->vcur = v;
		break;
	}
	case SR_UPDATE:
		rc = sv_indexmatch(&ii->index->i, i->r->cmp, ii->key, ii->keysize, &ii->v);
		if (rc == 0 && ii->v) {
			svv *v = srcast(ii->v, svv, node);
			ii->vcur = v;
			return v->lsn > ii->vlsn;
		}
		return 0;
	default: assert(0);
	}
	return eq && (n == ii->v);
}

static void
sv_indexiter_close(sriter *i srunused)
{}

static int
sv_indexiter_has(sriter *i)
{
	svindexiter *ii = (svindexiter*)i->priv;
	return ii->v != NULL;
}

static void*
sv_indexiter_of(sriter *i)
{
	svindexiter *ii = (svindexiter*)i->priv;
	if (srunlikely(ii->v == NULL))
		return NULL;
	assert(ii->vcur != NULL);
	svinit(&ii->current, &sv_vif, ii->vcur, NULL);
	return &ii->current;
}

static void
sv_indexiter_next(sriter *i)
{
	svindexiter *ii = (svindexiter*)i->priv;
	if (srunlikely(ii->v == NULL))
		return;
	switch (ii->order) {
	case SR_LT:
	case SR_LTE:
		ii->v = sr_rbprev(&ii->index->i, ii->v);
		ii->vcur = NULL;
		sv_indexiter_bkw(ii);
		break;
	case SR_RANDOM:
	case SR_GT:
	case SR_GTE:
		ii->v = sr_rbnext(&ii->index->i, ii->v);
		ii->vcur = NULL;
		sv_indexiter_fwd(ii);
		break;
	default: assert(0);
	}
}

sriterif sv_indexiter =
{
	.init    = sv_indexiter_init,
	.open    = sv_indexiter_open,
	.close   = sv_indexiter_close,
	.has     = sv_indexiter_has,
	.of      = sv_indexiter_of,
	.next    = sv_indexiter_next
};

typedef struct svindexiterraw svindexiterraw;

struct svindexiterraw {
	svindex *index;
	srrbnode *v;
	svv *vcur;
	sv current;
} srpacked;

static void
sv_indexiterraw_init(sriter *i)
{
	assert(sizeof(svindexiterraw) <= sizeof(i->priv));

	svindexiterraw *ii = (svindexiterraw*)i->priv;
	memset(ii, 0, sizeof(*ii));
}

static int
sv_indexiterraw_open(sriter *i, va_list args)
{
	svindexiterraw *ii = (svindexiterraw*)i->priv;
	ii->index = va_arg(args, svindex*);
	ii->v = sr_rbmin(&ii->index->i);
	ii->vcur = NULL;
	if (ii->v) {
		ii->vcur = srcast(ii->v, svv, node);
	}
	return 0;
}

static void
sv_indexiterraw_close(sriter *i srunused)
{}

static int
sv_indexiterraw_has(sriter *i)
{
	svindexiterraw *ii = (svindexiterraw*)i->priv;
	return ii->v != NULL;
}

static void*
sv_indexiterraw_of(sriter *i)
{
	svindexiterraw *ii = (svindexiterraw*)i->priv;
	if (srunlikely(ii->v == NULL))
		return NULL;
	assert(ii->vcur != NULL);
	svinit(&ii->current, &sv_vif, ii->vcur, NULL);
	return &ii->current;
}

static void
sv_indexiterraw_next(sriter *i)
{
	svindexiterraw *ii = (svindexiterraw*)i->priv;
	if (srunlikely(ii->v == NULL))
		return;
	assert(ii->vcur != NULL);
	svv *v = ii->vcur->next;
	if (v) {
		ii->vcur = v;
		return;
	}
	ii->v = sr_rbnext(&ii->index->i, ii->v);
	ii->vcur = NULL;
	if (ii->v) {
		ii->vcur = srcast(ii->v, svv, node);
	}
}

sriterif sv_indexiterraw =
{
	.init    = sv_indexiterraw_init,
	.open    = sv_indexiterraw_open,
	.close   = sv_indexiterraw_close,
	.has     = sv_indexiterraw_has,
	.of      = sv_indexiterraw_of,
	.next    = sv_indexiterraw_next
};
#line 1 "sophia/version/sv_local.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/




static uint8_t
sv_localifflags(sv *v) {
	return ((svlocal*)v->v)->flags;
}

static void
sv_localifflagsadd(sv *v, uint32_t flags) {
	((svlocal*)v->v)->flags |= flags;
}

static uint64_t
sv_localiflsn(sv *v) {
	return ((svlocal*)v->v)->lsn;
}

static void
sv_localiflsnset(sv *v, uint64_t lsn) {
	((svlocal*)v->v)->lsn = lsn;
}

static char*
sv_localifkey(sv *v) {
	return ((svlocal*)v->v)->key;
}

static uint16_t
sv_localifkeysize(sv *v) {
	return ((svlocal*)v->v)->keysize;
}

static char*
sv_localifvalue(sv *v)
{
	svlocal *lv = v->v;
	return lv->value;
}

static uint32_t
sv_localifvaluesize(sv *v) {
	return ((svlocal*)v->v)->valuesize;
}

static uint64_t
sv_localifoffset(sv *v srunused) {
	return 0;
}

svif sv_localif =
{
	.flags       = sv_localifflags,
	.flagsadd    = sv_localifflagsadd,
	.lsn         = sv_localiflsn,
	.lsnset      = sv_localiflsnset,
	.key         = sv_localifkey,
	.keysize     = sv_localifkeysize,
	.value       = sv_localifvalue,
	.valuesize   = sv_localifvaluesize,
	.valueoffset = sv_localifoffset,
	.raw         = NULL,
	.rawsize     = NULL,
	.ref         = NULL,
	.unref       = NULL
};
#line 1 "sophia/version/sv_mergeiter.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

/*
 * Merge serveral sorted streams into one.
 * Track duplicates.
 *
 * Merger does not recognize duplicates from
 * a single stream, assumed that they are tracked
 * by the incoming data sources.
*/




typedef struct svmergeiter svmergeiter;

struct svmergeiter {
	srorder order;
	svmerge *merge;
	svmergesrc *src, *end;
	svmergesrc *v;
} srpacked;

static void
sv_mergeiter_init(sriter *i)
{
	assert(sizeof(svmergeiter) <= sizeof(i->priv));
	svmergeiter *im = (svmergeiter*)i->priv;
	memset(im, 0, sizeof(*im));
}

static void sv_mergeiter_next(sriter*);

static int
sv_mergeiter_open(sriter *i, va_list args)
{
	svmergeiter *im = (svmergeiter*)i->priv;
	im->merge = va_arg(args, svmerge*);
	im->order = va_arg(args, srorder);
	im->src   = (svmergesrc*)(im->merge->buf.s);
	im->end   = (svmergesrc*)(im->merge->buf.p);
	im->v     = NULL;
	sv_mergeiter_next(i);
	return 0;
}

static void
sv_mergeiter_close(sriter *i srunused)
{ }

static int
sv_mergeiter_has(sriter *i)
{
	svmergeiter *im = (svmergeiter*)i->priv;
	return im->v != NULL;
}

static void*
sv_mergeiter_of(sriter *i)
{
	svmergeiter *im = (svmergeiter*)i->priv;
	if (srunlikely(im->v == NULL))
		return NULL;
	return sr_iterof(im->v->i);
}

static inline void
sv_mergeiter_dupreset(svmergeiter *im, svmergesrc *pos)
{
	svmergesrc *v = im->src;
	while (v != pos) {
		v->dup = 0;
		v = sv_mergenextof(v);
	}
}

static void
sv_mergeiter_gt(sriter *it)
{
	svmergeiter *im = (svmergeiter*)it->priv;
	if (im->v) {
		im->v->dup = 0;
		sr_iternext(im->v->i);
	}
	im->v = NULL;
	svmergesrc *min, *src;
	sv *minv;
	minv = NULL;
	min  = NULL;
	src  = im->src;
	for (; src < im->end; src = sv_mergenextof(src))
	{
		sv *v = sr_iterof(src->i);
		if (v == NULL)
			continue;
		if (min == NULL) {
			minv = v;
			min = src;
			continue;
		}
		int rc = svcompare(minv, v, it->r->cmp);
		switch (rc) {
		case 0:
			assert(svlsn(v) < svlsn(minv));
			src->dup = 1;
			break;
		case 1:
			sv_mergeiter_dupreset(im, src);
			minv = v;
			min = src;
			break;
		}
	}
	if (srunlikely(min == NULL))
		return;
	im->v = min;
}

static void
sv_mergeiter_lt(sriter *it)
{
	svmergeiter *im = (svmergeiter*)it->priv;
	if (im->v) {
		im->v->dup = 0;
		sr_iternext(im->v->i);
	}
	im->v = NULL;
	svmergesrc *max, *src;
	sv *maxv;
	maxv = NULL;
	max  = NULL;
	src  = im->src;
	for (; src < im->end; src = sv_mergenextof(src))
	{
		sv *v = sr_iterof(src->i);
		if (v == NULL)
			continue;
		if (max == NULL) {
			maxv = v;
			max = src;
			continue;
		}
		int rc = svcompare(maxv, v, it->r->cmp);
		switch (rc) {
		case  0:
			assert(svlsn(v) < svlsn(maxv));
			src->dup = 1;
			break;
		case -1:
			sv_mergeiter_dupreset(im, src);
			maxv = v;
			max = src;
			break;
		}
	}
	if (srunlikely(max == NULL))
		return;
	im->v = max;
}

static void
sv_mergeiter_next(sriter *it)
{
	svmergeiter *im = (svmergeiter*)it->priv;
	switch (im->order) {
	case SR_RANDOM:
	case SR_GT:
	case SR_GTE:
		sv_mergeiter_gt(it);
		break;
	case SR_LT:
	case SR_LTE:
		sv_mergeiter_lt(it);
		break;
	default: assert(0);
	}
}

sriterif sv_mergeiter =
{
	.init    = sv_mergeiter_init,
	.open    = sv_mergeiter_open,
	.close   = sv_mergeiter_close,
	.has     = sv_mergeiter_has,
	.of      = sv_mergeiter_of,
	.next    = sv_mergeiter_next
};

uint32_t sv_mergeisdup(sriter *i)
{
	svmergeiter *im = (svmergeiter*)i->priv;
	assert(im->v != NULL);
	if (im->v->dup)
		return SVDUP;
	return 0;
}
#line 1 "sophia/version/sv_readiter.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/




typedef struct svreaditer svreaditer;

struct svreaditer {
	sriter *merge;
	uint64_t vlsn;
	int next;
	int nextdup;
	sv *v;
} srpacked;

static void
sv_readiter_init(sriter *i)
{
	assert(sizeof(svreaditer) <= sizeof(i->priv));
	svreaditer *im = (svreaditer*)i->priv;
	memset(im, 0, sizeof(*im));
}

static void sv_readiter_next(sriter*);

static int
sv_readiter_open(sriter *i, va_list args)
{
	svreaditer *im = (svreaditer*)i->priv;
	im->merge = va_arg(args, sriter*);
	im->vlsn  = va_arg(args, uint64_t);
	assert(im->merge->i == &sv_mergeiter);
	/* iteration can start from duplicate */
	sv_readiter_next(i);
	return 0;
}

static void
sv_readiter_close(sriter *i srunused)
{ }

static int
sv_readiter_has(sriter *i)
{
	svreaditer *im = (svreaditer*)i->priv;
	return im->v != NULL;
}

static void*
sv_readiter_of(sriter *i)
{
	svreaditer *im = (svreaditer*)i->priv;
	if (srunlikely(im->v == NULL))
		return NULL;
	return im->v;
}

static void
sv_readiter_next(sriter *i)
{
	svreaditer *im = (svreaditer*)i->priv;
	if (im->next)
		sr_iternext(im->merge);
	im->next = 0;
	im->v = NULL;
	for (; sr_iterhas(im->merge); sr_iternext(im->merge))
	{
		sv *v = sr_iterof(im->merge);
		/* distinguish duplicates between merge
		 * streams only */
		int dup = sv_mergeisdup(im->merge);
		if (im->nextdup) {
			if (dup)
				continue;
			else
				im->nextdup = 0;
		}
		/* assume that iteration sources are
		 * version aware */
		assert(svlsn(v) <= im->vlsn);
		im->nextdup = 1;
		int del = (svflags(v) & SVDELETE) > 0;
		if (srunlikely(del))
			continue;
		im->v = v;
		im->next = 1;
		break;
	}
}

sriterif sv_readiter =
{
	.init    = sv_readiter_init,
	.open    = sv_readiter_open,
	.close   = sv_readiter_close,
	.has     = sv_readiter_has,
	.of      = sv_readiter_of,
	.next    = sv_readiter_next
};
#line 1 "sophia/version/sv_v.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/




static uint8_t
sv_vifflags(sv *v) {
	return ((svv*)v->v)->flags;
}

static void
sv_vifflagsadd(sv *v, uint32_t flags) {
	((svv*)v->v)->flags |= flags;
}

static uint64_t
sv_viflsn(sv *v) {
	return ((svv*)v->v)->lsn;
}

static void
sv_viflsnset(sv *v, uint64_t lsn) {
	((svv*)v->v)->lsn = lsn;
}

static char*
sv_vifkey(sv *v) {
	return sv_vkey(((svv*)v->v));
}

static uint16_t
sv_vifkeysize(sv *v) {
	return ((svv*)v->v)->keysize;
}

static char*
sv_vifvalue(sv *v)
{
	svv *vv = v->v;
	if (vv->valuesize == 0)
		return NULL;
	return sv_vvalue(vv);
}

static uint32_t
sv_vifvaluesize(sv *v) {
	return ((svv*)v->v)->valuesize;
}

svif sv_vif =
{
	.flags       = sv_vifflags,
	.flagsadd    = sv_vifflagsadd,
	.lsn         = sv_viflsn,
	.lsnset      = sv_viflsnset,
	.key         = sv_vifkey,
	.keysize     = sv_vifkeysize,
	.value       = sv_vifvalue,
	.valuesize   = sv_vifvaluesize,
	.valueoffset = NULL,
	.raw         = NULL,
	.rawsize     = NULL,
	.ref         = NULL,
	.unref       = NULL
};
#line 1 "sophia/version/sv_writeiter.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/




typedef struct svwriteiter svwriteiter;

struct svwriteiter {
	sriter *merge;
	uint64_t limit; 
	uint64_t size;
	uint32_t sizev;
	uint32_t total; /* kv */
	uint64_t vlsn;
	int save_delete;
	int next;
	uint64_t prevlsn;
	sv *v;
} srpacked;

static void
sv_writeiter_init(sriter *i)
{
	assert(sizeof(svwriteiter) <= sizeof(i->priv));
	svwriteiter *im = (svwriteiter*)i->priv;
	memset(im, 0, sizeof(*im));
}

static void sv_writeiter_next(sriter*);

static int
sv_writeiter_open(sriter *i, va_list args)
{
	svwriteiter *im = (svwriteiter*)i->priv;
	im->merge = va_arg(args, sriter*);
	im->limit = va_arg(args, uint64_t);
	im->sizev = va_arg(args, uint32_t);
	im->vlsn  = va_arg(args, uint64_t);
	im->save_delete = va_arg(args, int);
	assert(im->merge->i == &sv_mergeiter);
	sv_writeiter_next(i);
	return 0;
}

static void
sv_writeiter_close(sriter *i srunused)
{ }

static int
sv_writeiter_has(sriter *i)
{
	svwriteiter *im = (svwriteiter*)i->priv;
	return im->v != NULL;
}

static void*
sv_writeiter_of(sriter *i)
{
	svwriteiter *im = (svwriteiter*)i->priv;
	if (srunlikely(im->v == NULL))
		return NULL;
	return im->v;
}

static void
sv_writeiter_next(sriter *i)
{
	svwriteiter *im = (svwriteiter*)i->priv;
	if (im->next)
		sr_iternext(im->merge);
	im->next = 0;
	im->v = NULL;
	for (; sr_iterhas(im->merge); sr_iternext(im->merge))
	{
		sv *v = sr_iterof(im->merge);
		int dup = (svflags(v) & SVDUP) | sv_mergeisdup(im->merge);
		if (im->size >= im->limit) {
			if (! dup)
				break;
		}
		uint64_t lsn = svlsn(v);
		int kv = svkeysize(v) + svvaluesize(v);
		im->total += kv;
		if (srunlikely(dup)) {
			/* keep atleast one visible version for <= vlsn */
			if (im->prevlsn <= im->vlsn)
				continue;
		} else {
			/* branched or stray deletes */
			if (! im->save_delete) {
				int del = (svflags(v) & SVDELETE) > 0;
				if (srunlikely(del && (lsn <= im->vlsn))) {
					im->prevlsn = lsn;
					continue;
				}
			}
			im->size += im->sizev + kv;
		}
		im->prevlsn = lsn;
		im->v = v;
		im->next = 1;
		break;
	}
}

sriterif sv_writeiter =
{
	.init    = sv_writeiter_init,
	.open    = sv_writeiter_open,
	.close   = sv_writeiter_close,
	.has     = sv_writeiter_has,
	.of      = sv_writeiter_of,
	.next    = sv_writeiter_next
};

int sv_writeiter_resume(sriter *i)
{
	svwriteiter *im = (svwriteiter*)i->priv;
	im->v    = sr_iterof(im->merge);
	if (srunlikely(im->v == NULL))
		return 0;
	im->next = 1;
	im->size = im->sizev + svkeysize(im->v) +
	           svvaluesize(im->v);
	return 1;
}

uint32_t sv_writeiter_total(sriter *i)
{
	svwriteiter *im = (svwriteiter*)i->priv;
	return im->total;
}
#line 1 "sophia/transaction/sx_v.h"
#ifndef SX_V_H_
#define SX_V_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sxv sxv;

struct sxv {
	uint32_t id, lo;
	void *index;
	svv *v;
	sxv *next;
	sxv *prev;
	srrbnode node;
} srpacked;

extern svif sx_vif;

static inline sxv*
sx_valloc(sra *asxv, svv *v)
{
	sxv *vv = sr_malloc(asxv, sizeof(sxv));
	if (srunlikely(vv == NULL))
		return NULL;
	vv->index = NULL;
	vv->id    = 0;
	vv->lo    = 0;
	vv->v     = v;
	vv->next  = NULL;
	vv->prev  = NULL;
	memset(&vv->node, 0, sizeof(vv->node));
	return vv;
}

static inline void
sx_vfree(sra *a, sra *asxv, sxv *v)
{
	sr_free(a, v->v);
	sr_free(asxv, v);
}

static inline sxv*
sx_vmatch(sxv *head, uint32_t id) {
	sxv *c = head;
	while (c) {
		if (c->id == id)
			break;
		c = c->next;
	}
	return c;
}

static inline void
sx_vreplace(sxv *v, sxv *n) {
	if (v->prev)
		v->prev->next = n;
	if (v->next)
		v->next->prev = n;
	n->next = v->next;
	n->prev = v->prev;
}

static inline void
sx_vlink(sxv *head, sxv *v) {
	sxv *c = head;
	while (c->next)
		c = c->next;
	c->next = v;
	v->prev = c;
	v->next = NULL;
}

static inline void
sx_vunlink(sxv *v) {
	if (v->prev)
		v->prev->next = v->next;
	if (v->next)
		v->next->prev = v->prev;
	v->prev = NULL;
	v->next = NULL;
}

static inline void
sx_vabortwaiters(sxv *v) {
	sxv *c = v->next;
	while (c) {
		c->v->flags |= SVABORT;
		c = c->next;
	}
}

#endif
#line 1 "sophia/transaction/sx.h"
#ifndef SX_H_
#define SX_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sxmanager sxmanager;
typedef struct sxindex sxindex;
typedef struct sx sx;

typedef enum {
	SXUNDEF,
	SXREADY,
	SXCOMMIT,
	SXPREPARE,
	SXROLLBACK,
	SXLOCK
} sxstate;

typedef sxstate (*sxpreparef)(sx*, sv*, void*, void*);

struct sxindex {
	srrb i;
	uint32_t count;
	uint32_t dsn;
	srcomparator *cmp;
	void *ptr;
};

struct sx {
	uint32_t id;
	sxstate s;
	uint64_t vlsn;
	svlog log;
	srlist deadlock;
	sxmanager *manager;
	srrbnode node;
};

struct sxmanager {
	srspinlock lock;
	srrb i;
	uint32_t count;
	sra *asxv;
	sr *r;
};

int       sx_init(sxmanager*, sr*, sra*);
int       sx_free(sxmanager*);
int       sx_indexinit(sxindex*, void*);
int       sx_indexset(sxindex*, uint32_t, srcomparator*);
int       sx_indexfree(sxindex*, sxmanager*);
sx       *sx_find(sxmanager*, uint32_t);
sxstate   sx_begin(sxmanager*, sx*, uint64_t);
sxstate   sx_end(sx*);
sxstate   sx_prepare(sx*, sxpreparef, void*);
sxstate   sx_commit(sx*);
sxstate   sx_rollback(sx*);
int       sx_set(sx*, sxindex*, svv*);
int       sx_get(sx*, sxindex*, sv*, sv*);
uint64_t  sx_vlsn(sxmanager*);
sxstate   sx_setstmt(sxmanager*, sxindex*, sv*);
sxstate   sx_getstmt(sxmanager*, sxindex*);

#endif
#line 1 "sophia/transaction/sx_deadlock.h"
#ifndef SX_DEADLOCK_H_
#define SX_DEADLOCK_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

int sx_deadlock(sx*);

#endif
#line 1 "sophia/transaction/sx.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/





int sx_init(sxmanager *m, sr *r, sra *asxv)
{
	sr_rbinit(&m->i);
	m->count = 0;
	sr_spinlockinit(&m->lock);
	m->asxv = asxv;
	m->r = r;
	return 0;
}

int sx_free(sxmanager *m)
{
	/* rollback active transactions */

	sr_spinlockfree(&m->lock);
	return 0;
}

int sx_indexinit(sxindex *i, void *ptr)
{
	sr_rbinit(&i->i);
	i->count = 0;
	i->cmp = NULL;
	i->ptr = ptr;
	return 0;
}

int sx_indexset(sxindex *i, uint32_t dsn, srcomparator *cmp)
{
	i->dsn = dsn;
	i->cmp = cmp;
	return 0;
}

sr_rbtruncate(sx_truncate,
              sx_vfree(((sra**)arg)[0],
                       ((sra**)arg)[1], srcast(n, sxv, node)))

int sx_indexfree(sxindex *i, sxmanager *m)
{
	sra *allocators[2] = { m->r->a, m->asxv };
	if (i->i.root)
		sx_truncate(i->i.root, allocators);
	return 0;
}

uint64_t sx_vlsn(sxmanager *m)
{
	sr_spinlock(&m->lock);
	uint64_t vlsn;
	if (m->count) {
		srrbnode *node = sr_rbmin(&m->i);
		sx *min = srcast(node, sx, node);
		vlsn = min->vlsn;
	} else {
		vlsn = sr_seq(m->r->seq, SR_LSN);
	}
	sr_spinunlock(&m->lock);
	return vlsn;
}

sr_rbget(sx_matchtx,
         sr_cmpu32((char*)&(srcast(n, sx, node))->id, sizeof(uint32_t),
                   (char*)key, sizeof(uint32_t), NULL))

sx *sx_find(sxmanager *m, uint32_t id)
{
	srrbnode *n = NULL;
	int rc = sx_matchtx(&m->i, NULL, (char*)&id, sizeof(id), &n);
	if (rc == 0 && n)
		return  srcast(n, sx, node);
	return NULL;
}

sxstate sx_begin(sxmanager *m, sx *t, uint64_t vlsn)
{
	t->s = SXREADY; 
	t->manager = m;
	sr_seqlock(m->r->seq);
	t->id = sr_seqdo(m->r->seq, SR_TSNNEXT);
	if (srlikely(vlsn == 0))
		t->vlsn = sr_seqdo(m->r->seq, SR_LSN);
	else
		t->vlsn = vlsn;
	sr_sequnlock(m->r->seq);
	sv_loginit(&t->log);
	sr_listinit(&t->deadlock);
	sr_spinlock(&m->lock);
	srrbnode *n = NULL;
	int rc = sx_matchtx(&m->i, NULL, (char*)&t->id, sizeof(t->id), &n);
	if (rc == 0 && n) {
		assert(0);
	} else {
		sr_rbset(&m->i, n, rc, &t->node);
	}
	m->count++;
	sr_spinunlock(&m->lock);
	return SXREADY;
}

sxstate sx_end(sx *t)
{
	sxmanager *m = t->manager;
	assert(t->s != SXUNDEF);
	sr_spinlock(&m->lock);
	sr_rbremove(&m->i, &t->node);
	t->s = SXUNDEF;
	m->count--;
	sr_spinunlock(&m->lock);
	sv_logfree(&t->log, m->r->a);
	return SXUNDEF;
}

sxstate sx_prepare(sx *t, sxpreparef prepare, void *arg)
{
	sriter i;
	sr_iterinit(&i, &sr_bufiter, NULL);
	sr_iteropen(&i, &t->log.buf, sizeof(svlogv));
	sxstate s;
	for (; sr_iterhas(&i); sr_iternext(&i))
	{
		svlogv *lv = sr_iterof(&i);
		sxv *v = lv->v.v;
		/* cancelled by a concurrent commited
		 * transaction */
		if (v->v->flags & SVABORT)
			return SXROLLBACK;
		/* concurrent update in progress */
		if (v->prev != NULL)
			return SXLOCK;
		/* check that new key has not been committed by
		 * a concurrent transaction */
		if (prepare) {
			sxindex *i = v->index;
			s = prepare(t, &lv->v, arg, i->ptr);
			if (srunlikely(s != SXPREPARE))
				return s;
		}
	}
	s = SXPREPARE;
	t->s = s;
	return s;
}

sxstate sx_commit(sx *t)
{
	assert(t->s == SXPREPARE);
	sxmanager *m = t->manager;
	sriter i;
	sr_iterinit(&i, &sr_bufiter, NULL);
	sr_iteropen(&i, &t->log.buf, sizeof(svlogv));
	for (; sr_iterhas(&i); sr_iternext(&i))
	{
		svlogv *lv = sr_iterof(&i);
		sxv *v = lv->v.v;
		/* mark waiters as aborted */
		sx_vabortwaiters(v);
		/* remove from concurrent index and replace
		 * head with a first waiter */
		sxindex *i = v->index;
		if (v->next == NULL)
			sr_rbremove(&i->i, &v->node);
		else
			sr_rbreplace(&i->i, &v->node, &v->next->node);
		/* unlink version */
		sx_vunlink(v);
		/* translate log version from sxv to svv */
		svinit(&lv->v, &sv_vif, v->v, NULL);
		sr_free(m->asxv, v);
	}
	t->s = SXCOMMIT;
	return SXCOMMIT;
}

sxstate sx_rollback(sx *t)
{
	sxmanager *m = t->manager;
	sriter i;
	sr_iterinit(&i, &sr_bufiter, NULL);
	sr_iteropen(&i, &t->log.buf, sizeof(svlogv));
	for (; sr_iterhas(&i); sr_iternext(&i))
	{
		svlogv *lv = sr_iterof(&i);
		sxv *v = lv->v.v;
		/* remove from index and replace head with
		 * a first waiter */
		if (v->prev)
			goto unlink;
		sxindex *i = v->index;
		if (v->next == NULL)
			sr_rbremove(&i->i, &v->node);
		else
			sr_rbreplace(&i->i, &v->node, &v->next->node);
unlink:
		sx_vunlink(v);
		sx_vfree(m->r->a, m->asxv, v);
	}
	t->s = SXROLLBACK;
	return SXROLLBACK;
}

sr_rbget(sx_match,
         sr_compare(cmp, sv_vkey((srcast(n, sxv, node))->v),
                    (srcast(n, sxv, node))->v->keysize,
                    key, keysize))

int sx_set(sx *t, sxindex *index, svv *version)
{
	sxmanager *m = t->manager;
	/* allocate mvcc container */
	sxv *v = sx_valloc(m->asxv, version);
	if (srunlikely(v == NULL))
		return -1;
	v->id = t->id;
	v->index = index;
	svlogv lv;
	lv.id   = index->dsn;
	lv.next = 0;
	svinit(&lv.v, &sx_vif, v, NULL);
	/* update concurrent index */
	srrbnode *n = NULL;
	int rc = sx_match(&index->i, index->cmp,
	                  sv_vkey(version), version->keysize, &n);
	if (rc == 0 && n) {
		/* exists */
	} else {
		/* unique */
		v->lo = sv_logcount(&t->log);
		if (srunlikely(sv_logadd(&t->log, m->r->a, &lv, index->ptr) == -1))
			return sr_error(m->r->e, "%s", "memory allocation failed");
		sr_rbset(&index->i, n, rc, &v->node);
		return 0;
	}
	sxv *head = srcast(n, sxv, node);
	/* match previous update made by current
	 * transaction */
	sxv *own = sx_vmatch(head, t->id);
	if (srunlikely(own)) {
		/* replace old object with the new one */
		v->lo = own->lo;
		sx_vreplace(own, v);
		if (srlikely(head == own))
			sr_rbreplace(&index->i, &own->node, &v->node);
		/* update log */
		sv_logreplace(&t->log, v->lo, &lv);
		sx_vfree(m->r->a, m->asxv, own);
		return 0;
	}
	/* update log */
	rc = sv_logadd(&t->log, m->r->a, &lv, index->ptr);
	if (srunlikely(rc == -1)) {
		sx_vfree(m->r->a, m->asxv, v);
		return sr_error(m->r->e, "%s", "memory allocation failed");
	}
	/* add version */
	sx_vlink(head, v);
	return 0;
}

int sx_get(sx *t, sxindex *index, sv *key, sv *result)
{
	sxmanager *m = t->manager;
	srrbnode *n = NULL;
	int rc = sx_match(&index->i, index->cmp, svkey(key),
	                  svkeysize(key), &n);
	if (! (rc == 0 && n))
		return 0;
	sxv *head = srcast(n, sxv, node);
	sxv *v = sx_vmatch(head, t->id);
	if (v == NULL)
		return 0;
	if (srunlikely((v->v->flags & SVDELETE) > 0))
		return 2;
	sv vv;
	svinit(&vv, &sv_vif, v->v, NULL);
	svv *ret = sv_valloc(m->r->a, &vv);
	if (srunlikely(ret == NULL))
		return sr_error(m->r->e, "%s", "memory allocation failed");
	svinit(result, &sv_vif, ret, NULL);
	return 1;
}

sxstate sx_setstmt(sxmanager *m, sxindex *index, sv *v)
{
	sr_seq(m->r->seq, SR_TSNNEXT);
	srrbnode *n = NULL;
	int rc = sx_match(&index->i, index->cmp, svkey(v), svkeysize(v), &n);
	if (rc == 0 && n)
		return SXLOCK;
	return SXCOMMIT;
}

sxstate sx_getstmt(sxmanager *m, sxindex *index srunused)
{
	sr_seq(m->r->seq, SR_TSNNEXT);
	return SXCOMMIT;
}
#line 1 "sophia/transaction/sx_deadlock.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/





static inline int
sx_deadlock_in(sxmanager *m, srlist *mark, sx *t, sx *p)
{
	if (p->deadlock.next != &p->deadlock)
		return 0;
	sr_listappend(mark, &p->deadlock);
	sriter i;
	sr_iterinit(&i, &sr_bufiter, m->r);
	sr_iteropen(&i, &p->log.buf, sizeof(svlogv));
	for (; sr_iterhas(&i); sr_iternext(&i))
	{
		svlogv *lv = sr_iterof(&i);
		sxv *v = lv->v.v;
		if (v->prev == NULL)
			continue;
		do {
			sx *n = sx_find(m, v->id);
			assert(n != NULL);
			if (srunlikely(n == t))
				return 1;
			int rc = sx_deadlock_in(m, mark, t, n);
			if (srunlikely(rc == 1))
				return 1;
			v = v->prev;
		} while (v);
	}
	return 0;
}

static inline void
sx_deadlock_unmark(srlist *mark)
{
	srlist *i, *n;
	sr_listforeach_safe(mark, i, n) {
		sx *t = srcast(i, sx, deadlock);
		sr_listinit(&t->deadlock);
	}
}

int sx_deadlock(sx *t)
{
	sxmanager *m = t->manager;
	srlist mark;
	sr_listinit(&mark);
	sriter i;
	sr_iterinit(&i, &sr_bufiter, m->r);
	sr_iteropen(&i, &t->log.buf, sizeof(svlogv));
	for (; sr_iterhas(&i); sr_iternext(&i))
	{
		svlogv *lv = sr_iterof(&i);
		sxv *v = lv->v.v;
		if (v->prev == NULL)
			continue;
		sx *p = sx_find(m, v->prev->id);
		assert(p != NULL);
		int rc = sx_deadlock_in(m, &mark, t, p);
		if (srunlikely(rc)) {
			sx_deadlock_unmark(&mark);
			return 1;
		}
	}
	sx_deadlock_unmark(&mark);
	return 0;
}
#line 1 "sophia/transaction/sx_v.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/





static uint8_t
sx_vifflags(sv *v) {
	return ((sxv*)v->v)->v->flags;
}

static void
sx_vifflagsadd(sv *v, uint32_t flags) {
	((sxv*)v->v)->v->flags |= flags;
}

static uint64_t
sx_viflsn(sv *v) {
	return ((sxv*)v->v)->v->lsn;
}

static void
sx_viflsnset(sv *v, uint64_t lsn) {
	((sxv*)v->v)->v->lsn = lsn;
}

static char*
sx_vifkey(sv *v) {
	return sv_vkey(((sxv*)v->v)->v);
}

static uint16_t
sx_vifkeysize(sv *v) {
	return ((sxv*)v->v)->v->keysize;
}

static char*
sx_vifvalue(sv *v)
{
	sxv *vv = v->v;
	if (vv->v->valuesize == 0)
		return NULL;
	return sv_vvalue(vv->v);
}

static uint32_t
sx_vifvaluesize(sv *v) {
	return ((sxv*)v->v)->v->valuesize;
}

svif sx_vif =
{
	.flags       = sx_vifflags,
	.flagsadd    = sx_vifflagsadd,
	.lsn         = sx_viflsn,
	.lsnset      = sx_viflsnset,
	.key         = sx_vifkey,
	.keysize     = sx_vifkeysize,
	.value       = sx_vifvalue,
	.valuesize   = sx_vifvaluesize,
	.valueoffset = NULL,
	.raw         = NULL,
	.rawsize     = NULL,
	.ref         = NULL,
	.unref       = NULL
};
#line 1 "sophia/log/sl_conf.h"
#ifndef SL_CONF_H_
#define SL_CONF_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct slconf slconf;

struct slconf {
	int   enable;
	char *path;
	int   sync_on_rotate;
	int   sync_on_write;
	int   rotatewm;
};

#endif
#line 1 "sophia/log/sl_v.h"
#ifndef SL_V_H_
#define SL_V_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct slv slv;

struct slv {
	uint32_t crc;
	uint64_t lsn;
	uint32_t dsn;
	uint32_t valuesize;
	uint8_t  flags;
	uint16_t keysize;
	uint64_t reserve;
} srpacked;

extern svif sl_vif;

static inline uint32_t
sl_vdsn(sv *v) {
	return ((slv*)v->v)->dsn;
}

#endif
#line 1 "sophia/log/sl.h"
#ifndef SL_H_
#define SL_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sl sl;
typedef struct slpool slpool;
typedef struct sltx sltx;

struct sl {
	uint32_t id;
	srgc gc;
	srmutex filelock;
	srfile file;
	slpool *p;
	srlist link;
	srlist linkcopy;
};

struct slpool {
	srspinlock lock;
	slconf *conf;
	srlist list;
	int gc;
	int n;
	sriov iov;
	sr *r;
};

struct sltx {
	slpool *p;
	sl *l;
	uint64_t svp;
};

int sl_poolinit(slpool*, sr*);
int sl_poolopen(slpool*, slconf*);
int sl_poolrotate(slpool*);
int sl_poolrotate_ready(slpool*, int);
int sl_poolshutdown(slpool*);
int sl_poolgc_enable(slpool*, int);
int sl_poolgc(slpool*);
int sl_poolfiles(slpool*);
int sl_poolcopy(slpool*, char*, srbuf*);

int sl_begin(slpool*, sltx*);
int sl_prepare(slpool*, svlog*, uint64_t);
int sl_commit(sltx*);
int sl_rollback(sltx*);
int sl_write(sltx*, svlog*);

#endif
#line 1 "sophia/log/sl_iter.h"
#ifndef SL_ITER_H_
#define SL_ITER_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

extern sriterif sl_iter;

int sl_itererror(sriter*);
int sl_itercontinue(sriter*);

#endif
#line 1 "sophia/log/sl.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/





static inline sl*
sl_alloc(slpool *p, uint32_t id)
{
	sl *l = sr_malloc(p->r->a, sizeof(*l));
	if (srunlikely(l == NULL)) {
		sr_malfunction(p->r->e, "%s", "memory allocation failed");
		return NULL;
	}
	l->id   = id;
	l->p    = NULL;
	sr_gcinit(&l->gc);
	sr_mutexinit(&l->filelock);
	sr_fileinit(&l->file, p->r->a);
	sr_listinit(&l->link);
	sr_listinit(&l->linkcopy);
	return l;
}

static inline int
sl_close(slpool *p, sl *l)
{
	int rc = sr_fileclose(&l->file);
	if (srunlikely(rc == -1)) {
		sr_malfunction(p->r->e, "log file '%s' close error: %s",
		               l->file.file, strerror(errno));
	}
	sr_mutexfree(&l->filelock);
	sr_gcfree(&l->gc);
	sr_free(p->r->a, l);
	return rc;
}

static inline sl*
sl_open(slpool *p, uint32_t id)
{
	sl *l = sl_alloc(p, id);
	if (srunlikely(l == NULL))
		return NULL;
	srpath path;
	sr_pathA(&path, p->conf->path, id, ".log");
	int rc = sr_fileopen(&l->file, path.path);
	if (srunlikely(rc == -1)) {
		sr_malfunction(p->r->e, "log file '%s' open error: %s",
		               l->file.file, strerror(errno));
		goto error;
	}
	return l;
error:
	sl_close(p, l);
	return NULL;
}

static inline sl*
sl_new(slpool *p, uint32_t id)
{
	sl *l = sl_alloc(p, id);
	if (srunlikely(l == NULL))
		return NULL;
	srpath path;
	sr_pathA(&path, p->conf->path, id, ".log");
	int rc = sr_filenew(&l->file, path.path);
	if (srunlikely(rc == -1)) {
		sr_malfunction(p->r->e, "log file '%s' create error: %s",
		               path.path, strerror(errno));
		goto error;
	}
	srversion v;
	sr_version(&v);
	rc = sr_filewrite(&l->file, &v, sizeof(v));
	if (srunlikely(rc == -1)) {
		sr_malfunction(p->r->e, "log file '%s' header write error: %s",
		               l->file.file, strerror(errno));
		goto error;
	}
	return l;
error:
	sl_close(p, l);
	return NULL;
}

int sl_poolinit(slpool *p, sr *r)
{
	sr_spinlockinit(&p->lock);
	sr_listinit(&p->list);
	p->n    = 0;
	p->r    = r;
	p->gc   = 1;
	p->conf = NULL;
	struct iovec *iov =
		sr_malloc(r->a, sizeof(struct iovec) * 1021);
	if (srunlikely(iov == NULL))
		return sr_malfunction(r->e, "%s", "memory allocation failed");
	sr_iovinit(&p->iov, iov, 1021);
	return 0;
}

static inline int
sl_poolcreate(slpool *p)
{
	int rc;
	rc = sr_filemkdir(p->conf->path);
	if (srunlikely(rc == -1))
		return sr_malfunction(p->r->e, "log directory '%s' create error: %s",
		                      p->conf->path, strerror(errno));
	return 1;
}

static inline int
sl_poolrecover(slpool *p)
{
	srbuf list;
	sr_bufinit(&list);
	srdirtype types[] =
	{
		{ "log", 1, 0 },
		{ NULL,  0, 0 }
	};
	int rc = sr_dirread(&list, p->r->a, types, p->conf->path);
	if (srunlikely(rc == -1))
		return sr_malfunction(p->r->e, "log directory '%s' open error",
		                      p->conf->path);
	sriter i;
	sr_iterinit(&i, &sr_bufiter, p->r);
	sr_iteropen(&i, &list, sizeof(srdirid));
	while(sr_iterhas(&i)) {
		srdirid *id = sr_iterof(&i);
		sl *l = sl_open(p, id->id);
		if (srunlikely(l == NULL)) {
			sr_buffree(&list, p->r->a);
			return -1;
		}
		sr_listappend(&p->list, &l->link);
		p->n++;
		sr_iternext(&i);
	}
	sr_buffree(&list, p->r->a);
	if (p->n) {
		sl *last = srcast(p->list.prev, sl, link);
		p->r->seq->lfsn = last->id;
		p->r->seq->lfsn++;
	}
	return 0;
}

int sl_poolopen(slpool *p, slconf *conf)
{
	p->conf = conf;
	if (srunlikely(! p->conf->enable))
		return 0;
	int exists = sr_fileexists(p->conf->path);
	int rc;
	if (! exists)
		rc = sl_poolcreate(p);
	else
		rc = sl_poolrecover(p);
	if (srunlikely(rc == -1))
		return -1;
	return 0;
}

int sl_poolrotate(slpool *p)
{
	if (srunlikely(! p->conf->enable))
		return 0;
	uint32_t lfsn = sr_seq(p->r->seq, SR_LFSNNEXT);
	sl *l = sl_new(p, lfsn);
	if (srunlikely(l == NULL))
		return -1;
	sl *log = NULL;
	sr_spinlock(&p->lock);
	if (p->n) {
		log = srcast(p->list.prev, sl, link);
		sr_gccomplete(&log->gc);
	}
	sr_listappend(&p->list, &l->link);
	p->n++;
	sr_spinunlock(&p->lock);
	if (log) {
		if (p->conf->sync_on_rotate) {
			int rc = sr_filesync(&log->file);
			if (srunlikely(rc == -1)) {
				sr_malfunction(p->r->e, "log file '%s' sync error: %s",
				               log->file.file, strerror(errno));
				return -1;
			}
		}
	}
	return 0;
}

int sl_poolrotate_ready(slpool *p, int wm)
{
	if (srunlikely(! p->conf->enable))
		return 0;
	sr_spinlock(&p->lock);
	assert(p->n > 0);
	sl *l = srcast(p->list.prev, sl, link);
	int ready = sr_gcrotateready(&l->gc, wm);
	sr_spinunlock(&p->lock);
	return ready;
}

int sl_poolshutdown(slpool *p)
{
	int rcret = 0;
	int rc;
	if (p->n) {
		srlist *i, *n;
		sr_listforeach_safe(&p->list, i, n) {
			sl *l = srcast(i, sl, link);
			rc = sl_close(p, l);
			if (srunlikely(rc == -1))
				rcret = -1;
		}
	}
	if (p->iov.v)
		sr_free(p->r->a, p->iov.v);
	sr_spinlockfree(&p->lock);
	return rcret;
}

static inline int
sl_gc(slpool *p, sl *l)
{
	int rc;
	rc = sr_fileunlink(l->file.file);
	if (srunlikely(rc == -1)) {
		return sr_malfunction(p->r->e, "log file '%s' unlink error: %s",
		                      l->file.file, strerror(errno));
	}
	rc = sl_close(p, l);
	if (srunlikely(rc == -1))
		return -1;
	return 1;
}

int sl_poolgc_enable(slpool *p, int enable)
{
	sr_spinlock(&p->lock);
	p->gc = enable;
	sr_spinunlock(&p->lock);
	return 0;
}

int sl_poolgc(slpool *p)
{
	if (srunlikely(! p->conf->enable))
		return 0;
	for (;;) {
		sr_spinlock(&p->lock);
		if (srunlikely(! p->gc)) {
			sr_spinunlock(&p->lock);
			return 0;
		}
		sl *current = NULL;
		srlist *i;
		sr_listforeach(&p->list, i) {
			sl *l = srcast(i, sl, link);
			if (srlikely(! sr_gcgarbage(&l->gc)))
				continue;
			sr_listunlink(&l->link);
			p->n--;
			current = l;
			break;
		}
		sr_spinunlock(&p->lock);
		if (current) {
			int rc = sl_gc(p, current);
			if (srunlikely(rc == -1))
				return -1;
		} else {
			break;
		}
	}
	return 0;
}

int sl_poolfiles(slpool *p)
{
	sr_spinlock(&p->lock);
	int n = p->n;
	sr_spinunlock(&p->lock);
	return n;
}

int sl_poolcopy(slpool *p, char *dest, srbuf *buf)
{
	srlist list;
	sr_listinit(&list);
	sr_spinlock(&p->lock);
	srlist *i;
	sr_listforeach(&p->list, i) {
		sl *l = srcast(i, sl, link);
		if (sr_gcinprogress(&l->gc))
			break;
		sr_listappend(&list, &l->linkcopy);
	}
	sr_spinunlock(&p->lock);

	sr_bufinit(buf);
	srlist *n;
	sr_listforeach_safe(&list, i, n)
	{
		sl *l = srcast(i, sl, linkcopy);
		sr_listinit(&l->linkcopy);
		srpath path;
		sr_pathA(&path, dest, l->id, ".log");
		srfile file;
		sr_fileinit(&file, p->r->a);
		int rc = sr_filenew(&file, path.path);
		if (srunlikely(rc == -1)) {
			sr_malfunction(p->r->e, "log file '%s' create error: %s",
			               path.path, strerror(errno));
			return -1;
		}
		rc = sr_bufensure(buf, p->r->a, l->file.size);
		if (srunlikely(rc == -1)) {
			sr_malfunction(p->r->e, "%s", "memory allocation failed");
			sr_fileclose(&file);
			return -1;
		}
		rc = sr_filepread(&l->file, 0, buf->s, l->file.size);
		if (srunlikely(rc == -1)) {
			sr_malfunction(p->r->e, "log file '%s' read error: %s",
			               l->file.file, strerror(errno));
			sr_fileclose(&file);
			return -1;
		}
		sr_bufadvance(buf, l->file.size);
		rc = sr_filewrite(&file, buf->s, l->file.size);
		if (srunlikely(rc == -1)) {
			sr_malfunction(p->r->e, "log file '%s' write error: %s",
			               path.path, strerror(errno));
			sr_fileclose(&file);
			return -1;
		}
		/* sync? */
		rc = sr_fileclose(&file);
		if (srunlikely(rc == -1)) {
			sr_malfunction(p->r->e, "log file '%s' close error: %s",
			               path.path, strerror(errno));
			return -1;
		}
		sr_bufreset(buf);
	}
	return 0;
}

int sl_begin(slpool *p, sltx *t)
{
	memset(t, 0, sizeof(*t));
	sr_spinlock(&p->lock);
	t->p = p;
	if (! p->conf->enable)
		return 0;
	assert(p->n > 0);
	sl *l = srcast(p->list.prev, sl, link);
	sr_mutexlock(&l->filelock);
	t->svp = sr_filesvp(&l->file);
	t->l = l;
	t->p = p;
	return 0;
}

int sl_commit(sltx *t)
{
	if (t->p->conf->enable)
		sr_mutexunlock(&t->l->filelock);
	sr_spinunlock(&t->p->lock);
	return 0;
}

int sl_rollback(sltx *t)
{
	int rc = 0;
	if (t->p->conf->enable) {
		rc = sr_filerlb(&t->l->file, t->svp);
		if (srunlikely(rc == -1))
			sr_malfunction(t->p->r->e, "log file '%s' truncate error: %s",
			               t->l->file.file, strerror(errno));
		sr_mutexunlock(&t->l->filelock);
	}
	sr_spinunlock(&t->p->lock);
	return rc;
}

static inline int
sl_follow(slpool *p, uint64_t lsn)
{
	sr_seqlock(p->r->seq);
	if (lsn > p->r->seq->lsn)
		p->r->seq->lsn = lsn;
	sr_sequnlock(p->r->seq);
	return 0;
}

int sl_prepare(slpool *p, svlog *vlog, uint64_t lsn)
{
	if (srlikely(lsn == 0))
		lsn = sr_seq(p->r->seq, SR_LSNNEXT);
	else
		sl_follow(p, lsn);
	sriter i;
	sr_iterinit(&i, &sr_bufiter, NULL);
	sr_iteropen(&i, &vlog->buf, sizeof(svlogv));
	for (; sr_iterhas(&i); sr_iternext(&i)) {
		svlogv *v = sr_iterof(&i);
		svlsnset(&v->v, lsn);
	}
	return 0;
}

static inline void
sl_write_prepare(slpool *p, sltx *t, slv *lv, svlogv *logv)
{
	sv *v = &logv->v;
	lv->lsn       = svlsn(v);
	lv->dsn       = logv->id;
	lv->flags     = svflags(v);
	lv->valuesize = svvaluesize(v);
	lv->keysize   = svkeysize(v);
	lv->reserve   = 0;
	lv->crc       = sr_crcp(svkey(v), lv->keysize, 0);
	lv->crc       = sr_crcp(svvalue(v), lv->valuesize, lv->crc);
	lv->crc       = sr_crcs(lv, sizeof(slv), lv->crc);
	sr_iovadd(&p->iov, lv, sizeof(slv));
	sr_iovadd(&p->iov, svkey(v), lv->keysize);
	sr_iovadd(&p->iov, svvalue(v), lv->valuesize);
	((svv*)v->v)->log = t->l;
}

static inline int
sl_write_stmt(sltx *t, svlog *vlog)
{
	slpool *p = t->p;
	slv lv;
	svlogv *logv = (svlogv*)vlog->buf.s;
	sl_write_prepare(t->p, t, &lv, logv);
	int rc = sr_filewritev(&t->l->file, &p->iov);
	if (srunlikely(rc == -1)) {
		sr_malfunction(p->r->e, "log file '%s' write error: %s",
		               t->l->file.file, strerror(errno));
		return -1;
	}
	sr_gcmark(&t->l->gc, 1);
	sr_iovreset(&p->iov);
	return 0;
}

static int
sl_write_multi_stmt(sltx *t, svlog *vlog, uint64_t lsn)
{
	slpool *p = t->p;
	sl *l = t->l;
	slv lvbuf[341]; /* 1 + 340 per syscall */
	int lvp;
	int rc;
	lvp = 0;
	/* transaction header */
	slv *lv = &lvbuf[0];
	lv->lsn       = lsn;
	lv->dsn       = 0;
	lv->flags     = SVBEGIN;
	lv->valuesize = sv_logcount(vlog);
	lv->keysize   = 0;
	lv->reserve   = 0;
	lv->crc       = sr_crcs(lv, sizeof(slv), 0);
	sr_iovadd(&p->iov, lv, sizeof(slv));
	lvp++;
	/* body */
	sriter i;
	sr_iterinit(&i, &sr_bufiter, p->r);
	sr_iteropen(&i, &vlog->buf, sizeof(svlogv));
	for (; sr_iterhas(&i); sr_iternext(&i))
	{
		if (srunlikely(! sr_iovensure(&p->iov, 3))) {
			rc = sr_filewritev(&l->file, &p->iov);
			if (srunlikely(rc == -1)) {
				sr_malfunction(p->r->e, "log file '%s' write error: %s",
				               l->file.file, strerror(errno));
				return -1;
			}
			sr_iovreset(&p->iov);
			lvp = 0;
		}
		svlogv *logv = sr_iterof(&i);
		assert(logv->v.i == &sv_vif);
		lv = &lvbuf[lvp];
		sl_write_prepare(p, t, lv, logv);
		lvp++;
	}
	if (srlikely(sr_iovhas(&p->iov))) {
		rc = sr_filewritev(&l->file, &p->iov);
		if (srunlikely(rc == -1)) {
			sr_malfunction(p->r->e, "log file '%s' write error: %s",
			               l->file.file, strerror(errno));
			return -1;
		}
		sr_iovreset(&p->iov);
	}
	sr_gcmark(&l->gc, sv_logcount(vlog));
	return 0;
}

int sl_write(sltx *t, svlog *vlog)
{
	/* assume transaction log is prepared
	 * (lsn set) */
	if (srunlikely(! t->p->conf->enable))
		return 0;
	int count = sv_logcount(vlog);
	int rc;
	if (srlikely(count == 1)) {
		rc = sl_write_stmt(t, vlog);
	} else {
		svlogv *lv = (svlogv*)vlog->buf.s;
		uint64_t lsn = svlsn(&lv->v);
		rc = sl_write_multi_stmt(t, vlog, lsn);
	}
	if (srunlikely(rc == -1))
		return -1;
	/* sync */
	if (t->p->conf->enable && t->p->conf->sync_on_write) {
		rc = sr_filesync(&t->l->file);
		if (srunlikely(rc == -1)) {
			sr_malfunction(t->p->r->e, "log file '%s' sync error: %s",
			               t->l->file.file, strerror(errno));
			return -1;
		}
	}
	return 0;
}
#line 1 "sophia/log/sl_iter.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/





typedef struct sliter sliter;

struct sliter {
	int validate;
	int error;
	srfile *log;
	srmap map;
	slv *v;
	slv *next;
	uint32_t count;
	uint32_t pos;
	sv current;
} srpacked;

static void
sl_iterinit(sriter *i)
{
	assert(sizeof(sliter) <= sizeof(i->priv));
	sliter *li = (sliter*)i->priv;
	memset(li, 0, sizeof(*li));
}

static void
sl_iterseterror(sliter *i)
{
	i->error = 1;
	i->v     = NULL;
	i->next  = NULL;
}

static int
sl_iternext_of(sriter *i, slv *next, int validate)
{
	sliter *li = (sliter*)i->priv;
	if (next == NULL)
		return 0;
	char *eof   = (char*)li->map.p + li->map.size;
	char *start = (char*)next;

	/* eof */
	if (srunlikely(start == eof)) {
		if (li->count != li->pos) {
			sr_malfunction(i->r->e, "corrupted log file '%s': transaction is incomplete",
			               li->log->file);
			sl_iterseterror(li);
			return -1;
		}
		li->v = NULL;
		li->next = NULL;
		return 0;
	}

	char *end = start + next->keysize + next->valuesize;
	if (srunlikely((start > eof || (end > eof)))) {
		sr_malfunction(i->r->e, "corrupted log file '%s': bad record size",
		               li->log->file);
		sl_iterseterror(li);
		return -1;
	}
	if (validate && li->validate)
	{
		uint32_t crc = 0;
		if (! (next->flags & SVBEGIN)) {
			crc = sr_crcp(start + sizeof(slv), next->keysize, 0);
			crc = sr_crcp(start + sizeof(slv) + next->keysize,
			              next->valuesize, crc);
		}
		crc = sr_crcs(start, sizeof(slv), crc);
		if (srunlikely(crc != next->crc)) {
			sr_malfunction(i->r->e, "corrupted log file '%s': bad record crc",
			               li->log->file);
			sl_iterseterror(li);
			return -1;
		}
	}
	li->pos++;
	if (li->pos > li->count) {
		/* next transaction */
		li->v     = NULL;
		li->pos   = 0;
		li->count = 0;
		li->next  = next;
		return 0;
	}
	li->v = next;
	svinit(&li->current, &sl_vif, li->v, NULL);
	return 1;
}

int sl_itercontinue_of(sriter *i)
{
	sliter *li = (sliter*)i->priv;
	if (srunlikely(li->error))
		return -1;
	if (srunlikely(li->v))
		return 1;
	if (srunlikely(li->next == NULL))
		return 0;
	int validate = 0;
	li->pos   = 0;
	li->count = 0;
	slv *v = li->next;
	if (v->flags & SVBEGIN) {
		validate = 1;
		li->count = v->valuesize;
		v = (slv*)((char*)li->next + sizeof(slv));
	} else {
		li->count = 1;
		v = li->next;
	}
	return sl_iternext_of(i, v, validate);
}

static inline int
sl_iterprepare(sriter *i)
{
	sliter *li = (sliter*)i->priv;
	srversion *ver = (srversion*)li->map.p;
	if (! sr_versioncheck(ver))
		return sr_malfunction(i->r->e, "bad log file '%s' version",
		                      li->log->file);
	if (srunlikely(li->log->size < (sizeof(srversion))))
		return sr_malfunction(i->r->e, "corrupted log file '%s': bad size",
		                      li->log->file);
	slv *next = (slv*)((char*)li->map.p + sizeof(srversion));
	int rc = sl_iternext_of(i, next, 1);
	if (srunlikely(rc == -1))
		return -1;
	if (srlikely(li->next))
		return sl_itercontinue_of(i);
	return 0;
}

static int
sl_iteropen(sriter *i, va_list args)
{
	sliter *li = (sliter*)i->priv;
	li->log      = va_arg(args, srfile*);
	li->validate = va_arg(args, int);
	li->v        = NULL;
	li->next     = NULL;
	li->pos      = 0;
	li->count    = 0;
	if (srunlikely(li->log->size < sizeof(srversion))) {
		sr_malfunction(i->r->e, "corrupted log file '%s': bad size",
		               li->log->file);
		return -1;
	}
	if (srunlikely(li->log->size == sizeof(srversion)))
		return 0;
	int rc = sr_map(&li->map, li->log->fd, li->log->size, 1);
	if (srunlikely(rc == -1)) {
		sr_malfunction(i->r->e, "failed to mmap log file '%s': %s",
		               li->log->file, strerror(errno));
		return -1;
	}
	rc = sl_iterprepare(i);
	if (srunlikely(rc == -1))
		sr_mapunmap(&li->map);
	return 0;
}

static void
sl_iterclose(sriter *i srunused)
{
	sliter *li = (sliter*)i->priv;
	sr_mapunmap(&li->map);
}

static int
sl_iterhas(sriter *i)
{
	sliter *li = (sliter*)i->priv;
	return li->v != NULL;
}

static void*
sl_iterof(sriter *i)
{
	sliter *li = (sliter*)i->priv;
	if (srunlikely(li->v == NULL))
		return NULL;
	return &li->current;
}

static void
sl_iternext(sriter *i)
{
	sliter *li = (sliter*)i->priv;
	if (srunlikely(li->v == NULL))
		return;
	slv *next =
		(slv*)((char*)li->v + sizeof(slv) +
	           li->v->keysize +
	           li->v->valuesize);
	sl_iternext_of(i, next, 1);
}

sriterif sl_iter =
{
	.init    = sl_iterinit,
	.open    = sl_iteropen,
	.close   = sl_iterclose,
	.has     = sl_iterhas,
	.of      = sl_iterof,
	.next    = sl_iternext
};

int sl_itererror(sriter *i)
{
	sliter *li = (sliter*)i->priv;
	return li->error;
}

int sl_itercontinue(sriter *i)
{
	return sl_itercontinue_of(i);
}
#line 1 "sophia/log/sl_v.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/





static uint8_t
sl_vifflags(sv *v) {
	return ((slv*)v->v)->flags;
}

static void
sl_vifflagsadd(sv *v, uint32_t flags) {
	((slv*)v->v)->flags |= flags;
}

static uint64_t
sl_viflsn(sv *v) {
	return ((slv*)v->v)->lsn;
}

static char*
sl_vifkey(sv *v) {
	return (char*)v->v + sizeof(slv);
}

static uint16_t
sl_vifkeysize(sv *v) {
	return ((slv*)v->v)->keysize;
}

static char*
sl_vifvalue(sv *v)
{
	return (char*)v->v + sizeof(slv) +
	       ((slv*)v->v)->keysize;
}

static uint32_t
sl_vifvaluesize(sv *v) {
	return ((slv*)v->v)->valuesize;
}

svif sl_vif =
{
	.flags       = sl_vifflags,
	.flagsadd    = sl_vifflagsadd,
	.lsn         = sl_viflsn,
	.lsnset      = NULL,
	.key         = sl_vifkey,
	.keysize     = sl_vifkeysize,
	.value       = sl_vifvalue,
	.valuesize   = sl_vifvaluesize,
	.valueoffset = NULL,
	.raw         = NULL,
	.rawsize     = NULL,
	.ref         = NULL,
	.unref       = NULL 
};
#line 1 "sophia/database/sd_id.h"
#ifndef SD_ID_H_
#define SD_ID_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sdid sdid;

#define SD_IDBRANCH 1

struct sdid {
	uint32_t parent;
	uint32_t id;
	uint8_t  flags;
} srpacked;

static inline void
sd_idinit(sdid *i, uint32_t id, uint32_t parent, uint32_t flags)
{
	i->id     = id;
	i->parent = parent;
	i->flags  = flags;
}

#endif
#line 1 "sophia/database/sd_v.h"
#ifndef SD_V_H_
#define SD_V_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sdv sdv;

struct sdv {
	uint32_t crc;
	uint64_t lsn;
	uint32_t timestamp;
	uint8_t  flags;
	uint16_t keysize;
	uint32_t keyoffset;
	uint32_t valuesize;
	uint32_t valueoffset;
	uint64_t reserve;
} srpacked;

extern svif sd_vif;

#endif
#line 1 "sophia/database/sd_page.h"
#ifndef SD_PAGE_H_
#define SD_PAGE_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sdpageheader sdpageheader;
typedef struct sdpage sdpage;

struct sdpageheader {
	uint32_t crc;
	uint32_t count;
	uint32_t countdup;
	uint32_t size;
	uint32_t tsmin;
	uint64_t lsnmin;
	uint64_t lsnmindup;
	uint64_t lsnmax;
	char     reserve[16];
} srpacked;

struct sdpage {
	sdpageheader *h;
};

static inline void
sd_pageinit(sdpage *p, sdpageheader *h) {
	p->h = h;
}

static inline sdv*
sd_pagev(sdpage *p, uint32_t pos) {
	assert(pos < p->h->count);
	return (sdv*)((char*)p->h + sizeof(sdpageheader) + sizeof(sdv) * pos);
}

static inline void*
sd_pagekey(sdpage *p, sdv *v) {
	assert((sizeof(sdv) * p->h->count) + v->keyoffset <= p->h->size);
	return ((char*)p->h + sizeof(sdpageheader) +
	         sizeof(sdv) * p->h->count) + v->keyoffset;
}

static inline void*
sd_pagevalue(sdpage *p, sdv *v) {
	assert((sizeof(sdv) * p->h->count) + v->valueoffset <= p->h->size);
	return ((char*)p->h + sizeof(sdpageheader) +
	         sizeof(sdv) * p->h->count) + v->valueoffset;
}

static inline sdv*
sd_pagemin(sdpage *p) {
	return sd_pagev(p, 0);
}

static inline sdv*
sd_pagemax(sdpage *p) {
	return sd_pagev(p, p->h->count - 1);
}

#endif
#line 1 "sophia/database/sd_pageiter.h"
#ifndef SD_PAGEITER_H_
#define SD_PAGEITER_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

extern sriterif sd_pageiter;
extern sriterif sd_pageiterraw;

#endif
#line 1 "sophia/database/sd_index.h"
#ifndef SD_INDEX_H_
#define SD_INDEX_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sdindexheader sdindexheader;
typedef struct sdindexpage sdindexpage;
typedef struct sdindex sdindex;

struct sdindexheader {
	uint32_t  crc;
	srversion version;
	sdid      id;
	uint64_t  offset;
	uint16_t  block;
	uint32_t  count;
	uint32_t  keys;
	uint64_t  total;
	uint64_t  lsnmin;
	uint64_t  lsnmax;
	uint32_t  tsmin;
	uint32_t  dupkeys;
	uint64_t  dupmin;
	uint32_t  extension;
	char      reserve[32];
} srpacked;

struct sdindexpage {
	uint64_t offset;
	uint32_t size;
	uint16_t sizemin;
	uint16_t sizemax;
	uint64_t lsnmin;
	uint64_t lsnmax;
	char     reserve[16];
} srpacked;

struct sdindex {
	srbuf i;
	sdindexheader *h;
};

static inline char*
sd_indexpage_min(sdindexpage *p) {
	return (char*)p + sizeof(sdindexpage);
}

static inline char*
sd_indexpage_max(sdindexpage *p) {
	return (char*)p + sizeof(sdindexpage) + p->sizemin;
}

static inline void
sd_indexinit(sdindex *i) {
	sr_bufinit(&i->i);
	i->h = NULL;
}

static inline void
sd_indexfree(sdindex *i, sr *r) {
	sr_buffree(&i->i, r->a);
}

static inline sdindexheader*
sd_indexheader(sdindex *i) {
	return (sdindexheader*)(i->i.s);
}

static inline sdindexpage*
sd_indexpage(sdindex *i, uint32_t pos)
{
	assert(pos < i->h->count);
	char *p = (char*)sr_bufat(&i->i, i->h->block, pos);
   	p += sizeof(sdindexheader);
	return (sdindexpage*)p;
}

static inline sdindexpage*
sd_indexmin(sdindex *i) {
	return sd_indexpage(i, 0);
}

static inline sdindexpage*
sd_indexmax(sdindex *i) {
	return sd_indexpage(i, i->h->count - 1);
}
static inline uint16_t
sd_indexkeysize(sdindex *i)
{
	if (srunlikely(i->h == NULL))
		return 0;
	return (sd_indexheader(i)->block - sizeof(sdindexpage)) / 2;
}

static inline uint32_t
sd_indexkeys(sdindex *i)
{
	if (srunlikely(i->h == NULL))
		return 0;
	return sd_indexheader(i)->keys;
}

static inline uint32_t
sd_indextotal(sdindex *i)
{
	if (srunlikely(i->h == NULL))
		return 0;
	return sd_indexheader(i)->total;
}

static inline uint32_t
sd_indextotal_kv(sdindex *i)
{
	if (srunlikely(i->h == NULL))
		return 0;
	return sd_indexheader(i)->total -
	       sd_indexheader(i)->count * sizeof(sdpageheader) -
	       sd_indexheader(i)->keys * sizeof(sdv);
}

static inline uint32_t
sd_indexsize(sdindexheader *h)
{
	return sizeof(sdindexheader) + h->count * h->block;
}

static inline int
sd_indexpage_cmp(sdindexpage *p, void *key, int size, srcomparator *c)
{
	int l = sr_compare(c, sd_indexpage_min(p), p->sizemin, key, size);
	int r = sr_compare(c, sd_indexpage_max(p), p->sizemax, key, size);
	/* inside page range */
	if (l <= 0 && r >= 0)
		return 0;
	/* key > page */
	if (l == -1)
		return -1;
	/* key < page */
	assert(r == 1);
	return 1;
}

int sd_indexbegin(sdindex*, sr*, uint32_t, uint64_t);
int sd_indexcommit(sdindex*, sdid*);
int sd_indexadd(sdindex*, sr*, uint64_t, uint32_t, uint32_t,
                char*, int, char*, int,
                uint32_t, uint64_t, uint64_t, uint64_t);
int sd_indexcopy(sdindex*, sr*, sdindexheader*);

#endif
#line 1 "sophia/database/sd_indexiter.h"
#ifndef SD_INDEXITER_H_
#define SD_INDEXITER_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

extern sriterif sd_indexiter;

#endif
#line 1 "sophia/database/sd_seal.h"
#ifndef SD_SEAL_H_
#define SD_SEAL_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sdseal sdseal;

struct sdseal {
	uint32_t crc;
	uint32_t index_crc;
	uint64_t index_offset;
} srpacked;

static inline void
sd_seal(sdseal *s, sdindexheader *h)
{
	s->index_crc = h->crc;
	s->index_offset = h->offset;
	s->crc = sr_crcs(s, sizeof(sdseal), 0);
}

static inline int
sd_sealvalidate(sdseal *s, sdindexheader *h)
{
	uint32_t crc = sr_crcs(s, sizeof(sdseal), 0);
	if (srunlikely(s->crc != crc))
		return -1;
	if (srunlikely(h->crc != s->index_crc))
		return -1;
	if (srunlikely(h->offset != s->index_offset))
		return -1;
	return 0;
}

#endif
#line 1 "sophia/database/sd_build.h"
#ifndef SD_BUILD_H_
#define SD_BUILD_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sdbuildref sdbuildref;
typedef struct sdbuild sdbuild;

struct sdbuildref {
	uint32_t k, ksize;
	uint32_t v, vsize;
} srpacked;

struct sdbuild {
	srbuf list, k, v;
	uint32_t n;
	sr *r;
};

static inline void
sd_buildinit(sdbuild *b, sr *r)
{
	sr_bufinit(&b->list);
	sr_bufinit(&b->k);
	sr_bufinit(&b->v);
	b->n = 0;
	b->r = r;
}

static inline void
sd_buildfree(sdbuild *b)
{
	sr_buffree(&b->list, b->r->a);
	sr_buffree(&b->k, b->r->a);
	sr_buffree(&b->v, b->r->a);
}

static inline void
sd_buildreset(sdbuild *b)
{
	sr_bufreset(&b->list);
	sr_bufreset(&b->k);
	sr_bufreset(&b->v);
	b->n = 0;
}

static inline sdbuildref*
sd_buildref(sdbuild *b) {
	return sr_bufat(&b->list, sizeof(sdbuildref), b->n);
}

static inline sdpageheader*
sd_buildheader(sdbuild *b) {
	return (sdpageheader*)(b->k.s + sd_buildref(b)->k);
}

static inline uint64_t
sd_buildoffset(sdbuild *b)
{
	sdbuildref *r = sd_buildref(b);
	return r->k + sr_bufused(&b->v) - (sr_bufused(&b->v) - r->v);
}

static inline sdv*
sd_buildmin(sdbuild *b) {
	return (sdv*)((char*)sd_buildheader(b) + sizeof(sdpageheader));
}

static inline char*
sd_buildminkey(sdbuild *b) {
	sdbuildref *r = sd_buildref(b);
	return b->v.s + r->v + sd_buildmin(b)->keyoffset;
}

static inline sdv*
sd_buildmax(sdbuild *b) {
	sdpageheader *h = sd_buildheader(b);
	return (sdv*)((char*)h + sizeof(sdpageheader) + sizeof(sdv) * (h->count - 1));
}

static inline char*
sd_buildmaxkey(sdbuild *b) {
	sdbuildref *r = sd_buildref(b);
	return b->v.s + r->v + sd_buildmax(b)->keyoffset;
}

static inline uint32_t
sd_buildsize(sdbuild *b) {
	return sr_bufused(&b->k) + sr_bufused(&b->v);
}

int sd_buildbegin(sdbuild*);
int sd_buildcommit(sdbuild*);
int sd_buildend(sdbuild*);
int sd_buildadd(sdbuild*, sv*, uint32_t);
int sd_buildwrite(sdbuild*, sdindex*, srfile*);
int sd_buildwritepage(sdbuild*, srbuf*);

#endif
#line 1 "sophia/database/sd_c.h"
#ifndef SD_C_H_
#define SD_C_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sdc sdc;

struct sdc {
	sdbuild build;
	srbuf a; /* result */
	srbuf b; /* redistribute buffer */
	srbuf c; /* file buffer */
};

static inline void
sd_cinit(sdc *sc, sr *r)
{
	sd_buildinit(&sc->build, r);
	sr_bufinit(&sc->a);
	sr_bufinit(&sc->b);
	sr_bufinit(&sc->c);
}

static inline void
sd_cfree(sdc *sc, sr *r)
{
	sd_buildfree(&sc->build);
	sr_buffree(&sc->a, r->a);
	sr_buffree(&sc->b, r->a);
	sr_buffree(&sc->c, r->a);
}

static inline void
sd_creset(sdc *sc)
{
	sd_buildreset(&sc->build);
	sr_bufreset(&sc->a);
	sr_bufreset(&sc->b);
	sr_bufreset(&sc->c);
}

#endif
#line 1 "sophia/database/sd_merge.h"
#ifndef SD_MERGE_H_
#define SD_MERGE_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sdmerge sdmerge;

struct sdmerge {
	uint32_t parent;
	sdindex index;
	sriter *merge;
	sriter i;
	uint32_t size_key;
	uint32_t size_stream;
	uint32_t size_page;
	uint64_t size_node;
	uint32_t processed;
	uint64_t offset;
	sr *r;
	sdbuild *build;
};

int sd_mergeinit(sdmerge*, sr*, uint32_t, sriter*,
                 sdbuild*, uint64_t,
                 uint32_t, uint32_t,
                 uint64_t, uint32_t, int, uint64_t);
int sd_mergefree(sdmerge*);
int sd_merge(sdmerge*);
int sd_mergecommit(sdmerge*, sdid*);

#endif
#line 1 "sophia/database/sd_iter.h"
#ifndef SD_ITER_H_
#define SD_ITER_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

extern sriterif sd_iter;

#endif
#line 1 "sophia/database/sd_recover.h"
#ifndef SD_RECOVER_H_
#define SD_RECOVER_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

extern sriterif sd_recover;

int sd_recovercomplete(sriter*);

#endif
#line 1 "sophia/database/sd_build.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/





int sd_buildbegin(sdbuild *b)
{
	int rc = sr_bufensure(&b->list, b->r->a, sizeof(sdbuildref));
	if (srunlikely(rc == -1))
		return sr_error(b->r->e, "%s", "memory allocation failed");
	sdbuildref *ref =
		(sdbuildref*)sr_bufat(&b->list, sizeof(sdbuildref), b->n);
	ref->k     = sr_bufused(&b->k);
	ref->ksize = 0;
	ref->v     = sr_bufused(&b->v);
	ref->vsize = 0;
	rc = sr_bufensure(&b->k, b->r->a, sizeof(sdpageheader));
	if (srunlikely(rc == -1))
		return sr_error(b->r->e, "%s", "memory allocation failed");
	sdpageheader *h = sd_buildheader(b);
	memset(h, 0, sizeof(*h));
	h->lsnmin     = UINT64_MAX;
	h->lsnmindup  = UINT64_MAX;
	h->tsmin      = 0;
	memset(h->reserve, 0, sizeof(h->reserve));
	sr_bufadvance(&b->list, sizeof(sdbuildref));
	sr_bufadvance(&b->k, sizeof(sdpageheader));
	return 0;
}

int sd_buildadd(sdbuild *b, sv *v, uint32_t flags)
{
	/* prepare metadata reference */
	int rc = sr_bufensure(&b->k, b->r->a, sizeof(sdv));
	if (srunlikely(rc == -1))
		return sr_error(b->r->e, "%s", "memory allocation failed");
	sdpageheader *h = sd_buildheader(b);
	sdv *sv = (sdv*)b->k.p;
	sv->lsn         = svlsn(v);
	sv->flags       = svflags(v) | flags;
	sv->timestamp   = 0;
	sv->reserve     = 0;
	sv->keysize     = svkeysize(v);
	sv->valuesize   = svvaluesize(v);
	sv->keyoffset   = sr_bufused(&b->v) - sd_buildref(b)->v;
	sv->valueoffset = sv->keyoffset + sv->keysize;
	/* copy key-value pair */
	rc = sr_bufensure(&b->v, b->r->a, sv->keysize + sv->valuesize);
	if (srunlikely(rc == -1))
		return sr_error(b->r->e, "%s", "memory allocation failed");
	char *data = b->v.p;
	memcpy(b->v.p, svkey(v), sv->keysize);
	sr_bufadvance(&b->v, sv->keysize);
	memcpy(b->v.p, svvalue(v), sv->valuesize);
	sr_bufadvance(&b->v, sv->valuesize);
	sr_bufadvance(&b->k, sizeof(sdv));
	uint32_t crc;
	crc = sr_crcp(data, sv->keysize + sv->valuesize, 0);
	crc = sr_crcs(sv, sizeof(sdv), crc);
	sv->crc = crc;
	/* update page header */
	h->count++;
	h->size += sv->keysize + sv->valuesize + sizeof(sdv);
	if (sv->lsn > h->lsnmax)
		h->lsnmax = sv->lsn;
	if (sv->lsn < h->lsnmin)
		h->lsnmin = sv->lsn;
	if (sv->flags & SVDUP) {
		h->countdup++;
		if (sv->lsn < h->lsnmindup)
			h->lsnmindup = sv->lsn;
	}
	return 0;
}

int sd_buildend(sdbuild *b)
{
	sdpageheader *h = sd_buildheader(b);
	h->crc = sr_crcs(h, sizeof(sdpageheader), 0);
	sdbuildref *ref = sd_buildref(b);
	ref->ksize = sr_bufused(&b->k) - ref->k;
	ref->vsize = sr_bufused(&b->v) - ref->v;
	return 0;
}

int sd_buildcommit(sdbuild *b)
{
	b->n++;
	return 0;
}

int sd_buildwritepage(sdbuild *b, srbuf *buf)
{
	sdbuildref *ref = sd_buildref(b);
	assert(ref->ksize != 0);
	int rc = sr_bufensure(buf, b->r->a, ref->ksize + ref->vsize);
	if (srunlikely(rc == -1))
		return -1;
	memcpy(buf->p, b->k.s + ref->k, ref->ksize);
	sr_bufadvance(buf, ref->ksize);
	memcpy(buf->p, b->v.s + ref->v, ref->vsize);
	sr_bufadvance(buf, ref->vsize);
	return 0;
}

typedef struct {
	sdbuild *b;
	uint32_t i;
	uint32_t iovmax;
} sdbuildiov;

static inline void
sd_buildiov_init(sdbuildiov *i, sdbuild *b, int iovmax)
{
	i->b = b;
	i->iovmax = iovmax;
	i->i = 0;
}

static inline int
sd_buildiov(sdbuildiov *i, sriov *iov)
{
	uint32_t n = 0;
	while (i->i < i->b->n && n < (i->iovmax-2)) {
		sdbuildref *ref =
			(sdbuildref*)sr_bufat(&i->b->list, sizeof(sdbuildref), i->i);
		sr_iovadd(iov, i->b->k.s + ref->k, ref->ksize);
		sr_iovadd(iov, i->b->v.s + ref->v, ref->vsize);
		i->i++;
		n += 2;
	}
	return i->i < i->b->n;
}

int sd_buildwrite(sdbuild *b, sdindex *index, srfile *file)
{
	sdseal seal;
	sd_seal(&seal, index->h);
	struct iovec iovv[1024];
	sriov iov;
	sr_iovinit(&iov, iovv, 1024);
	sr_iovadd(&iov, index->i.s, sr_bufused(&index->i));

	SR_INJECTION(b->r->i, SR_INJECTION_SD_BUILD_0,
	             sr_malfunction(b->r->e, "%s", "error injection");
	             assert( sr_filewritev(file, &iov) == 0 );
	             return -1);

	sdbuildiov iter;
	sd_buildiov_init(&iter, b, 1022);
	int more = 1;
	while (more) {
		more = sd_buildiov(&iter, &iov);
		if (srlikely(! more)) {
			SR_INJECTION(b->r->i, SR_INJECTION_SD_BUILD_1,
			             seal.crc++); /* corrupt seal */
			sr_iovadd(&iov, &seal, sizeof(seal));
		}
		int rc;
		rc = sr_filewritev(file, &iov);
		if (srunlikely(rc == -1)) {
			return sr_malfunction(b->r->e, "file '%s' write error: %s",
			                      file->file, strerror(errno));
		}
		sr_iovreset(&iov);
	}
	return 0;
}
#line 1 "sophia/database/sd_index.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/





int sd_indexbegin(sdindex *i, sr *r, uint32_t keysize, uint64_t offset)
{
	int rc = sr_bufensure(&i->i, r->a, sizeof(sdindexheader));
	if (srunlikely(rc == -1))
		return sr_error(r->e, "%s", "memory allocation failed");
	sdindexheader *h = sd_indexheader(i);
	sr_version(&h->version);
	h->crc       = 0;
	h->block     = sizeof(sdindexpage) + (keysize * 2);
	h->count     = 0;
	h->keys      = 0;
	h->total     = 0;
	h->extension = 0;
	h->lsnmin    = UINT64_MAX;
	h->lsnmax    = 0;
	h->tsmin     = 0;
	h->offset    = offset;
	h->dupkeys   = 0;
	h->dupmin    = UINT64_MAX;
	memset(h->reserve, 0, sizeof(h->reserve));
	sd_idinit(&h->id, 0, 0, 0);
	i->h = h;
	sr_bufadvance(&i->i, sizeof(sdindexheader));
	return 0;
}

int sd_indexcommit(sdindex *i, sdid *id)
{
	i->h      = sd_indexheader(i);
	i->h->id  = *id;
	i->h->crc = sr_crcs(i->h, sizeof(sdindexheader), 0);
	return 0;
}

int sd_indexadd(sdindex *i, sr *r, uint64_t offset,
                uint32_t size,
                uint32_t count,
                char *min, int sizemin,
                char *max, int sizemax,
                uint32_t dupkeys,
                uint64_t dupmin,
                uint64_t lsnmin,
                uint64_t lsnmax)
{
	int rc = sr_bufensure(&i->i, r->a, i->h->block);
	if (srunlikely(rc == -1))
		return sr_error(r->e, "%s", "memory allocation failed");
	i->h = sd_indexheader(i);
	sdindexpage *p = (sdindexpage*)i->i.p;
	p->offset   = offset;
	p->size     = size;
	p->sizemin  = sizemin;
	p->sizemax  = sizemax;
	p->lsnmin   = lsnmin;
	p->lsnmax   = lsnmax;
	memcpy(sd_indexpage_min(p), min, sizemin);
	memcpy(sd_indexpage_max(p), max, sizemax);
	memset(p->reserve, 0, sizeof(p->reserve));
	int padding = i->h->block - (sizeof(sdindexpage) + sizemin + sizemax);
	if (padding > 0)
		memset(sd_indexpage_max(p) + sizemax, 0, padding);
	i->h->count++;
	i->h->keys  += count;
	i->h->total += size;
	if (lsnmin < i->h->lsnmin)
		i->h->lsnmin = lsnmin;
	if (lsnmax > i->h->lsnmax)
		i->h->lsnmax = lsnmax;
	i->h->dupkeys += dupkeys;
	if (dupmin < i->h->dupmin)
		i->h->dupmin = dupmin;
	sr_bufadvance(&i->i, i->h->block);
	return 0;
}

int sd_indexcopy(sdindex *i, sr *r, sdindexheader *h)
{
	int size = sd_indexsize(h);
	int rc = sr_bufensure(&i->i, r->a, size);
	if (srunlikely(rc == -1))
		return sr_error(r->e, "%s", "memory allocation failed");
	memcpy(i->i.s, (char*)h, size);
	sr_bufadvance(&i->i, size);
	i->h = (sdindexheader*)i->i.s;
	return 0;
}
#line 1 "sophia/database/sd_indexiter.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/





typedef struct sdindexiter sdindexiter;

struct sdindexiter {
	sdindex *index;
	sdindexpage *v;
	int pos;
	srorder cmp;
	void *key;
	int keysize;
} srpacked;

static void
sd_indexiter_init(sriter *i)
{
	assert(sizeof(sdindexiter) <= sizeof(i->priv));
	sdindexiter *ii = (sdindexiter*)i->priv;
	memset(ii, 0, sizeof(*ii));
}

static inline int
sd_indexiter_seek(sriter *i, void *key, int size, int *minp, int *midp, int *maxp)
{
	sdindexiter *ii = (sdindexiter*)i->priv;
	int match = 0;
	int min = 0;
	int max = ii->index->h->count - 1;
	int mid = 0;
	while (max >= min)
	{
		mid = min + ((max - min) >> 1);
		sdindexpage *page = sd_indexpage(ii->index, mid);

		int rc = sd_indexpage_cmp(page, key, size, i->r->cmp);
		switch (rc) {
		case -1: min = mid + 1;
			continue;
		case  1: max = mid - 1;
			continue;
		default: match = 1;
			goto done;
		}
	}
done:
	*minp = min;
	*midp = mid;
	*maxp = max;
	return match;
}

static int
sd_indexiter_route(sriter *i)
{
	sdindexiter *ii = (sdindexiter*)i->priv;
	int mid, min, max;
	int rc = sd_indexiter_seek(i, ii->key, ii->keysize, &min, &mid, &max);
	if (srlikely(rc))
		return mid;
	if (srunlikely(min >= (int)ii->index->h->count))
		min = ii->index->h->count - 1;
	return min;
}

static int
sd_indexiter_open(sriter *i, va_list args)
{
	sdindexiter *ii = (sdindexiter*)i->priv;
	ii->index   = va_arg(args, sdindex*);
	ii->cmp     = va_arg(args, srorder);
	ii->key     = va_arg(args, void*);
	ii->keysize = va_arg(args, int);
	ii->v       = NULL;
	if (ii->index->h->count == 1) {
		ii->pos = 0;
		if (ii->index->h->lsnmin == UINT64_MAX &&
		    ii->index->h->lsnmax == 0) {
			/* skip bootstrap node  */
			return 0;
		} 
		ii->v = sd_indexpage(ii->index, ii->pos);
		return 0;
	}
	if (ii->key == NULL) {
		switch (ii->cmp) {
		case SR_LT:
		case SR_LTE: ii->pos = ii->index->h->count - 1;
			break;
		case SR_GT:
		case SR_GTE: ii->pos = 0;
			break;
		default:
			assert(0);
		}
	} else {
		ii->pos = sd_indexiter_route(i);
		sdindexpage *p = sd_indexpage(ii->index, ii->pos);
		switch (ii->cmp) {
		case SR_LTE: break;
		case SR_LT: {
			int l = sr_compare(i->r->cmp, sd_indexpage_min(p), p->sizemin,
			                   ii->key, ii->keysize);
			if (srunlikely(l == 0))
				ii->pos--;
			break;
		}
		case SR_GTE: break;
		case SR_GT: {
			int r = sr_compare(i->r->cmp, sd_indexpage_max(p), p->sizemax,
			                   ii->key, ii->keysize);
			if (srunlikely(r == 0))
				ii->pos++;
			break;
		}
		case SR_RANDOM:{
			uint32_t rnd = *(uint32_t*)ii->key;
			ii->pos = rnd % ii->index->h->count;
			break;
		}
		default: assert(0);
		}
	}
	if (srunlikely(ii->pos == -1 ||
	               ii->pos >= (int)ii->index->h->count))
		return 0;
	ii->v = sd_indexpage(ii->index, ii->pos);
	return 0;
}

static void
sd_indexiter_close(sriter *i srunused)
{ }

static int
sd_indexiter_has(sriter *i)
{
	sdindexiter *ii = (sdindexiter*)i->priv;
	return ii->v != NULL;
}

static void*
sd_indexiter_of(sriter *i)
{
	sdindexiter *ii = (sdindexiter*)i->priv;
	return ii->v;
}

static void
sd_indexiter_next(sriter *i)
{
	sdindexiter *ii = (sdindexiter*)i->priv;
	switch (ii->cmp) {
	case SR_LT:
	case SR_LTE:
		ii->pos--;
		break;
	case SR_GT:
	case SR_GTE:
		ii->pos++;
		break;
	default:
		assert(0);
		break;
	}
	if (srunlikely(ii->pos < 0))
		ii->v = NULL;
	else
	if (srunlikely(ii->pos >= (int)ii->index->h->count))
		ii->v = NULL;
	else
		ii->v = sd_indexpage(ii->index, ii->pos);
}

sriterif sd_indexiter =
{
	.init  = sd_indexiter_init,
	.open  = sd_indexiter_open,
	.close = sd_indexiter_close,
	.has   = sd_indexiter_has,
	.of    = sd_indexiter_of,
	.next  = sd_indexiter_next
};
#line 1 "sophia/database/sd_iter.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/





typedef struct sditer sditer;

struct sditer {
	int validate;
	sdindex *index;
	char *start, *end;
	char *page;
	sdpage pagev;
	uint32_t pos;
	sdv *dv;
	sv v;
} srpacked;

static void
sd_iterinit(sriter *i)
{
	assert(sizeof(sditer) <= sizeof(i->priv));
	sditer *ii = (sditer*)i->priv;
	memset(ii, 0, sizeof(*ii));
}

static int sd_iternextpage(sriter*);

static int
sd_iteropen(sriter *i, va_list args)
{
	sditer *ii = (sditer*)i->priv;
	ii->index    = va_arg(args, sdindex*);
	ii->start    = va_arg(args, char*);
	ii->validate = va_arg(args, int);
	return sd_iternextpage(i);
}

static void
sd_iterclose(sriter *i srunused)
{
	sditer *ii = (sditer*)i->priv;
	(void)ii;
}

static int
sd_iterhas(sriter *i)
{
	sditer *ii = (sditer*)i->priv;
	return ii->page != NULL;
}

static void*
sd_iterof(sriter *i)
{
	sditer *ii = (sditer*)i->priv;
	if (srunlikely(ii->page == NULL))
		return NULL;
	assert(ii->dv != NULL);
	assert(ii->v.v  == ii->dv);
	assert(ii->v.arg == ii->pagev.h);
	return &ii->v;
}

static inline int
sd_iternextpage(sriter *it)
{
	sditer *i = (sditer*)it->priv;
	char *page = NULL;
	if (srunlikely(i->page == NULL))
	{
		sdindexheader *h = i->index->h;
		page = i->start + h->offset + sd_indexsize(i->index->h);
		i->end = page + h->total;
	} else {
		page = i->page + sizeof(sdpageheader) + i->pagev.h->size;
	}
	if (srunlikely(page >= i->end)) {
		i->page = NULL;
		return 0;
	}
	i->page = page;
	if (i->validate) {
		sdpageheader *h = (sdpageheader*)i->page;
		uint32_t crc = sr_crcs(h, sizeof(sdpageheader), 0);
		if (srunlikely(crc != h->crc)) {
			i->page = NULL;
			sr_malfunction(it->r->e, "%s", "bad page header crc");
			return -1;
		}
	}
	sd_pageinit(&i->pagev, (void*)i->page);
	i->pos = 0;
	if (srunlikely(i->pagev.h->count == 0)) {
		i->page = NULL;
		i->dv = NULL;
		return 0;
	}
	i->dv = sd_pagev(&i->pagev, 0);
	svinit(&i->v, &sd_vif, i->dv, i->pagev.h);
	return 1;
}

static void
sd_iternext(sriter *i)
{
	sditer *ii = (sditer*)i->priv;
	if (srunlikely(ii->page == NULL))
		return;
	ii->pos++;
	if (srlikely(ii->pos < ii->pagev.h->count)) {
		ii->dv = sd_pagev(&ii->pagev, ii->pos);
		svinit(&ii->v, &sd_vif, ii->dv, ii->pagev.h);
	} else {
		ii->dv = NULL;
		sd_iternextpage(i);
	}
}

sriterif sd_iter =
{
	.init    = sd_iterinit,
	.open    = sd_iteropen,
	.close   = sd_iterclose,
	.has     = sd_iterhas,
	.of      = sd_iterof,
	.next    = sd_iternext
};
#line 1 "sophia/database/sd_merge.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/





int sd_mergeinit(sdmerge *m, sr *r, uint32_t parent,
                 sriter *i,
                 sdbuild *build,
                 uint64_t offset,
                 uint32_t size_key,
                 uint32_t size_stream,
                 uint64_t size_node,
                 uint32_t size_page, int save_delete,
                 uint64_t vlsn)
{
	m->r           = r;
	m->parent      = parent;
	m->build       = build;
	m->offset      = offset;
	m->size_key    = size_key;
	m->size_stream = size_stream;
	m->size_node   = size_node;
	m->size_page   = size_page;
	sd_indexinit(&m->index);
	m->merge       = i;
	sr_iterinit(&m->i, &sv_writeiter, r);
	sr_iteropen(&m->i, i, (uint64_t)size_page, sizeof(sdv), vlsn,
	            save_delete);
	return 0;
}

int sd_mergefree(sdmerge *m)
{
	sd_indexfree(&m->index, m->r);
	return 0;
}

int sd_merge(sdmerge *m)
{
	if (srunlikely(! sr_iterhas(&m->i)))
		return 0;
	sd_buildreset(m->build);

	sd_indexinit(&m->index);
	int rc = sd_indexbegin(&m->index, m->r, m->size_key, m->offset);
	if (srunlikely(rc == -1))
		return -1;

	uint32_t processed = sv_writeiter_total(&m->i); /* kv */
	uint32_t processed_last = 0;
	assert(processed <= m->size_stream);
	uint64_t left = (m->size_stream - processed);
	uint64_t limit;
	if (left >= (m->size_node * 2))
		limit = m->size_node;
	else
	if (left > (m->size_node))
		limit = m->size_node / 2;
	else
		limit = left;

	while (sr_iterhas(&m->i) && (processed_last <= limit))
	{
		rc = sd_buildbegin(m->build);
		if (srunlikely(rc == -1))
			return -1;
		while (sr_iterhas(&m->i)) {
			sv *v = sr_iterof(&m->i);
			rc = sd_buildadd(m->build, v, sv_mergeisdup(m->merge));
			if (srunlikely(rc == -1))
				return -1;
			sr_iternext(&m->i);
		}
		rc = sd_buildend(m->build);
		if (srunlikely(rc == -1))
			return -1;

		/* page offset is relative to index:
		 *
		 * m->offset + (index_size) + page->offset
		*/
		sdpageheader *h = sd_buildheader(m->build);
		rc = sd_indexadd(&m->index, m->r,
		                 sd_buildoffset(m->build),
		                 h->size + sizeof(sdpageheader),
		                 h->count,
		                 sd_buildminkey(m->build),
		                 sd_buildmin(m->build)->keysize,
		                 sd_buildmaxkey(m->build),
		                 sd_buildmax(m->build)->keysize,
		                 h->countdup,
		                 h->lsnmindup,
		                 h->lsnmin,
		                 h->lsnmax);
		if (srunlikely(rc == -1))
			return -1;
		sd_buildcommit(m->build);

		processed_last = sv_writeiter_total(&m->i) -
		                 processed;
		if (srunlikely(! sv_writeiter_resume(&m->i)))
			break;
	}
	return 1;
}

int sd_mergecommit(sdmerge *m, sdid *id)
{
	sd_indexcommit(&m->index, id);
	return 0;
}
#line 1 "sophia/database/sd_pageiter.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/





typedef struct sdpageiter sdpageiter;

struct sdpageiter {
	sdpage *page;
	int64_t pos;
	sdv *v;
	sv current;
	srorder order;
	void *key;
	int keysize;
	uint64_t vlsn;
} srpacked;

static void
sd_pageiter_init(sriter *i)
{
	assert(sizeof(sdpageiter) <= sizeof(i->priv));

	sdpageiter *pi = (sdpageiter*)i->priv;
	memset(pi, 0, sizeof(*pi));
}

static inline void
sd_pageiter_end(sdpageiter *i)
{
	i->pos = i->page->h->count;
	i->v   = NULL;
}

static inline int
sd_pageiter_search(sriter *i, int search_min)
{
	sdpageiter *pi = (sdpageiter*)i->priv;
	srcomparator *cmp = i->r->cmp;
	int min = 0;
	int mid = 0;
	int max = pi->page->h->count - 1;
	while (max >= min)
	{
		mid = min + (max - min) / 2;
		sdv *v = sd_pagev(pi->page, mid);
		char *key = sd_pagekey(pi->page, v);
		int rc = sr_compare(cmp, key, v->keysize, pi->key, pi->keysize);
		switch (rc) {
		case -1: min = mid + 1;
			continue;
		case  1: max = mid - 1;
			continue;
		default: return mid;
		}
	}
	return (search_min) ? min : max;
}

static inline void
sd_pageiter_lv(sdpageiter *i, int64_t pos)
{
	/* lower-visible bound */

	/* find visible max: any first key which
	 * lsn <= vlsn (max in dup chain) */
	int64_t maxpos = 0;
	sdv *v;
	sdv *max = NULL;
	while (pos >= 0) {
		v = sd_pagev(i->page, pos);
		if (v->lsn <= i->vlsn) {
			maxpos = pos;
			max = v;
		}
		if (! (v->flags & SVDUP)) {
			/* head */
			if (max) {
				i->pos = maxpos;
				i->v = max;
				return;
			}
		}
		pos--;
	}
	sd_pageiter_end(i);
}

static inline void
sd_pageiter_gv(sdpageiter *i, int64_t pos)
{
	/* greater-visible bound */

	/* find visible max: any first key which
	 * lsn <= vlsn (max in dup chain) */
	while (pos < i->page->h->count ) {
		sdv *v = sd_pagev(i->page, pos);
		if (v->lsn <= i->vlsn) {
			i->pos = pos;
			i->v = v;
			return;
		}
		pos++;
	}
	sd_pageiter_end(i);
}

static inline void
sd_pageiter_lland(sdpageiter *i, int64_t pos)
{
	/* reposition to a visible duplicate */
	i->pos = pos;
	i->v = sd_pagev(i->page, i->pos);
	if (i->v->lsn == i->vlsn)
		return;
	if (i->v->lsn > i->vlsn) {
		/* search max < i->vlsn */
		pos++;
		while (pos < i->page->h->count)
		{
			sdv *v = sd_pagev(i->page, pos);
			if (! (v->flags & SVDUP))
				break;
			if (v->lsn <= i->vlsn) {
				i->pos = pos;
				i->v = v;
				return;
			}
			pos++;
		}
	}
	sd_pageiter_lv(i, i->pos);
}

static inline void
sd_pageiter_gland(sdpageiter *i, int64_t pos)
{
	/* reposition to a visible duplicate */
	i->pos = pos;
	i->v = sd_pagev(i->page, i->pos);
	if (i->v->lsn == i->vlsn)
		return;

	if (i->v->lsn > i->vlsn) {
		/* search max < i->vlsn */
		pos++;
		sd_pageiter_gv(i, pos);
		return;
	}

	/* i->v->lsn < i->vlsn */
	if (! (i->v->flags & SVDUP))
		return;
	int64_t maxpos = pos;
	sdv *max = sd_pagev(i->page, i->pos);
	pos--;
	while (pos >= 0) {
		sdv *v = sd_pagev(i->page, pos);
		if (v->lsn <= i->vlsn) {
			maxpos = pos;
			max = v;
		}
		if (! (v->flags & SVDUP))
			break;
		pos--;
	}
	i->pos = maxpos;
	i->v = max;
}

static void
sd_pageiter_bkw(sdpageiter *i)
{
	/* skip to previous visible key */
	int64_t pos = i->pos;
	sdv *v = sd_pagev(i->page, pos);
	if (v->flags & SVDUP) {
		/* skip duplicates */
		pos--;
		while (pos >= 0) {
			v = sd_pagev(i->page, pos);
			if (! (v->flags & SVDUP))
				break;
			pos--;
		}
		if (srunlikely(pos < 0)) {
			sd_pageiter_end(i);
			return;
		}
	}
	assert(! (v->flags & SVDUP));
	pos--;

	sd_pageiter_lv(i, pos);
}

static void
sd_pageiter_fwd(sdpageiter *i)
{
	/* skip to next visible key */
	int64_t pos = i->pos + 1;
	while (pos < i->page->h->count)
	{
		sdv *v = sd_pagev(i->page, pos);
		if (! (v->flags & SVDUP))
			break;
		pos++;
	}
	if (srunlikely(pos >= i->page->h->count)) {
		sd_pageiter_end(i);
		return;
	}
	sdv *match = NULL;
	while (pos < i->page->h->count)
	{
		sdv *v = sd_pagev(i->page, pos);
		if (v->lsn <= i->vlsn) {
			match = v;
			break;
		}
		pos++;
	}
	if (srunlikely(pos == i->page->h->count)) {
		sd_pageiter_end(i);
		return;
	}
	assert(match != NULL);
	i->pos = pos;
	i->v = match;
}

static inline int
sd_pageiter_lt(sriter *i, int e)
{
	sdpageiter *pi = (sdpageiter*)i->priv;
	if (srunlikely(pi->page->h->count == 0)) {
		sd_pageiter_end(pi);
		return 0;
	}
	if (pi->key == NULL) {
		sd_pageiter_lv(pi, pi->page->h->count - 1);
		return 0;
	}
	int64_t pos = sd_pageiter_search(i, 1);
	if (srunlikely(pos >= pi->page->h->count))
		pos = pi->page->h->count - 1;
	sd_pageiter_lland(pi, pos);
	if (pi->v == NULL)
		return 0;
	char *key = sd_pagekey(pi->page, pi->v);
	int rc = sr_compare(i->r->cmp, key, pi->v->keysize,
	                    pi->key,
	                    pi->keysize);
	int match = rc == 0;
	switch (rc) {
		case  0:
			if (! e)
				sd_pageiter_bkw(pi);
			break;
		case  1:
			sd_pageiter_bkw(pi);
			break;
	}
	return match;
}

static inline int
sd_pageiter_gt(sriter *i, int e)
{
	sdpageiter *pi = (sdpageiter*)i->priv;
	if (srunlikely(pi->page->h->count == 0)) {
		sd_pageiter_end(pi);
		return 0;
	}
	if (pi->key == NULL) {
		sd_pageiter_gv(pi, 0);
		return 0;
	}
	int64_t pos = sd_pageiter_search(i, 1);
	if (srunlikely(pos >= pi->page->h->count))
		pos = pi->page->h->count - 1;
	sd_pageiter_gland(pi, pos);
	if (pi->v == NULL)
		return 0;
	char *key = sd_pagekey(pi->page, pi->v);
	int rc = sr_compare(i->r->cmp, key, pi->v->keysize,
	                    pi->key,
	                    pi->keysize);
	int match = rc == 0;
	switch (rc) {
		case  0:
			if (! e)
				sd_pageiter_fwd(pi);
			break;
		case -1:
			sd_pageiter_fwd(pi);
			break;
	}
	return match;
}

static inline int
sd_pageiter_random(sriter *i)
{
	sdpageiter *pi = (sdpageiter*)i->priv;
	if (srunlikely(pi->page->h->count == 0)) {
		sd_pageiter_end(pi);
		return 0;
	}
	assert(pi->key != NULL);
	uint32_t rnd = *(uint32_t*)pi->key;
	int64_t pos = rnd % pi->page->h->count;
	if (srunlikely(pos >= pi->page->h->count))
		pos = pi->page->h->count - 1;
	sd_pageiter_gland(pi, pos);
	return 0;
}

static int
sd_pageiter_open(sriter *i, va_list args)
{
	sdpageiter *pi = (sdpageiter*)i->priv;
	pi->page    = va_arg(args, sdpage*);
	pi->order   = va_arg(args, srorder);
	pi->key     = va_arg(args, void*);
	pi->keysize = va_arg(args, int);
	pi->vlsn    = va_arg(args, uint64_t);
	if (srunlikely(pi->page->h->lsnmin > pi->vlsn &&
	               pi->order != SR_UPDATE))
		return 0;
	int match;
	switch (pi->order) {
	case SR_LT:     return sd_pageiter_lt(i, 0);
	case SR_LTE:    return sd_pageiter_lt(i, 1);
	case SR_GT:     return sd_pageiter_gt(i, 0);
	case SR_GTE:    return sd_pageiter_gt(i, 1);
	case SR_EQ:     return sd_pageiter_lt(i, 1);
	case SR_RANDOM: return sd_pageiter_random(i);
	case SR_UPDATE: {
		uint64_t vlsn = pi->vlsn;
		pi->vlsn = (uint64_t)-1;
		match = sd_pageiter_lt(i, 1);
		if (match == 0)
			return 0;
		return pi->v->lsn > vlsn;
	}
	default: assert(0);
	}
	return 0;
}

static void
sd_pageiter_close(sriter *i srunused)
{ }

static int
sd_pageiter_has(sriter *i)
{
	sdpageiter *pi = (sdpageiter*)i->priv;
	return pi->v != NULL;
}

static void*
sd_pageiter_of(sriter *i)
{
	sdpageiter *pi = (sdpageiter*)i->priv;
	if (srunlikely(pi->v == NULL))
		return NULL;
	svinit(&pi->current, &sd_vif, pi->v, pi->page->h);
	return &pi->current;
}

static void
sd_pageiter_next(sriter *i)
{
	sdpageiter *pi = (sdpageiter*)i->priv;
	switch (pi->order) {
	case SR_LT:
	case SR_LTE: sd_pageiter_bkw(pi);
		break;
	case SR_RANDOM:
	case SR_GT:
	case SR_GTE: sd_pageiter_fwd(pi);
		break;
	default: assert(0);
	}
}

sriterif sd_pageiter =
{
	.init    = sd_pageiter_init,
	.open    = sd_pageiter_open,
	.close   = sd_pageiter_close,
	.has     = sd_pageiter_has,
	.of      = sd_pageiter_of,
	.next    = sd_pageiter_next
};

typedef struct sdpageiterraw sdpageiterraw;

struct sdpageiterraw {
	sdpage *page;
	int64_t pos;
	sdv *v;
	sv current;
} srpacked;

static void
sd_pageiterraw_init(sriter *i)
{
	assert(sizeof(sdpageiterraw) <= sizeof(i->priv));

	sdpageiterraw *pi = (sdpageiterraw*)i->priv;
	memset(pi, 0, sizeof(*pi));
}

static int
sd_pageiterraw_open(sriter *i, va_list args)
{
	sdpageiterraw *pi = (sdpageiterraw*)i->priv;
	sdpage *p = va_arg(args, sdpage*);
	pi->page = p;
	if (srunlikely(p->h->count == 0)) {
		pi->pos = 1;
		pi->v = NULL;
		return 0;
	}
	pi->pos = 0;
	pi->v = sd_pagev(p, 0);
	return 0;
}

static void
sd_pageiterraw_close(sriter *i srunused)
{ }

static int
sd_pageiterraw_has(sriter *i)
{
	sdpageiterraw *pi = (sdpageiterraw*)i->priv;
	return pi->v != NULL;
}

static void*
sd_pageiterraw_of(sriter *i)
{
	sdpageiterraw *pi = (sdpageiterraw*)i->priv;
	if (srunlikely(pi->v == NULL))
		return NULL;
	svinit(&pi->current, &sd_vif, pi->v, pi->page->h);
	return &pi->current;
}

static void
sd_pageiterraw_next(sriter *i)
{
	sdpageiterraw *pi = (sdpageiterraw*)i->priv;
	pi->pos++;
	if (srlikely(pi->pos < pi->page->h->count))
		pi->v = sd_pagev(pi->page, pi->pos);
	else
		pi->v = NULL;
}

sriterif sd_pageiterraw =
{
	.init  = sd_pageiterraw_init,
	.open  = sd_pageiterraw_open,
	.close = sd_pageiterraw_close,
	.has   = sd_pageiterraw_has,
	.of    = sd_pageiterraw_of,
	.next  = sd_pageiterraw_next,
};
#line 1 "sophia/database/sd_recover.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/





typedef struct sdrecover sdrecover;

struct sdrecover {
	srfile *file;
	int corrupt;
	sdindexheader *actual;
	sdindexheader *v;
	srmap map;
} srpacked;

static void
sd_recoverinit(sriter *i)
{
	assert(sizeof(sdrecover) <= sizeof(i->priv));
	sdrecover *ri = (sdrecover*)i->priv;
	memset(ri, 0, sizeof(*ri));
}

static int
sd_recovernext_of(sriter *i, sdindexheader *next)
{
	sdrecover *ri = (sdrecover*)i->priv;
	if (next == NULL)
		return 0;
	char *eof   = (char*)ri->map.p + ri->map.size;
	char *start = (char*)next;
	/* eof */
	if (srunlikely(start == eof)) {
		ri->v = NULL;
		return 0;
	}
	/* validate crc */
	uint32_t crc = sr_crcs(next, sizeof(sdindexheader), 0);
	if (next->crc != crc) {
		sr_malfunction(i->r->e, "corrupted db file '%s': bad index crc",
		               ri->file->file);
		ri->corrupt = 1;
		ri->v = NULL;
		return -1;
	}
	/* check version */
	if (! sr_versioncheck(&next->version))
		return sr_malfunction(i->r->e, "bad db file '%s' version",
		                      ri->file->file);
	char *end = start + sizeof(sdindexheader) +
	            next->count * next->block +
	            next->total +
	            next->extension + sizeof(sdseal);
	if (srunlikely((start > eof || (end > eof)))) {
		sr_malfunction(i->r->e, "corrupted db file '%s': bad record size",
		               ri->file->file);
		ri->corrupt = 1;
		ri->v = NULL;
		return -1;
	}
	/* check seal */
	sdseal *s = (sdseal*)(end - sizeof(sdseal));
	int rc = sd_sealvalidate(s, next);
	if (srunlikely(rc == -1)) {
		sr_malfunction(i->r->e, "corrupted db file '%s': bad seal",
		               ri->file->file);
		ri->corrupt = 1;
		ri->v = NULL;
		return -1;
	}
	ri->actual = next;
	ri->v = next;
	return 1;
}

static int
sd_recoveropen(sriter *i, va_list args)
{
	sdrecover *ri = (sdrecover*)i->priv;
	ri->file = va_arg(args, srfile*);
	if (srunlikely(ri->file->size < (sizeof(sdindexheader) + sizeof(sdseal)))) {
		sr_malfunction(i->r->e, "corrupted db file '%s': bad size",
		               ri->file->file);
		ri->corrupt = 1;
		return -1;
	}
	int rc = sr_map(&ri->map, ri->file->fd, ri->file->size, 1);
	if (srunlikely(rc == -1)) {
		sr_malfunction(i->r->e, "failed to mmap db file '%s': %s",
		               ri->file->file, strerror(errno));
		return -1;
	}
	ri->v = NULL;
	sdindexheader *next = (sdindexheader*)((char*)ri->map.p);
	rc = sd_recovernext_of(i, next);
	if (srunlikely(rc == -1))
		sr_mapunmap(&ri->map);
	return rc;
}

static void
sd_recoverclose(sriter *i srunused)
{
	sdrecover *ri = (sdrecover*)i->priv;
	sr_mapunmap(&ri->map);
}

static int
sd_recoverhas(sriter *i)
{
	sdrecover *ri = (sdrecover*)i->priv;
	return ri->v != NULL;
}

static void*
sd_recoverof(sriter *i)
{
	sdrecover *ri = (sdrecover*)i->priv;
	return ri->v;
}

static void
sd_recovernext(sriter *i)
{
	sdrecover *ri = (sdrecover*)i->priv;
	if (srunlikely(ri->v == NULL))
		return;
	sdindexheader *next =
		(sdindexheader*)((char*)ri->v +
		    (sizeof(sdindexheader) + ri->v->count * ri->v->block) +
		     ri->v->total +
		     ri->v->extension + sizeof(sdseal));
	sd_recovernext_of(i, next);
}

sriterif sd_recover =
{
	.init    = sd_recoverinit,
	.open    = sd_recoveropen,
	.close   = sd_recoverclose,
	.has     = sd_recoverhas,
	.of      = sd_recoverof,
	.next    = sd_recovernext
};

int sd_recovercomplete(sriter *i)
{
	sdrecover *ri = (sdrecover*)i->priv;
	if (srunlikely(ri->actual == NULL))
		return -1;
	if (srlikely(ri->corrupt == 0))
		return  0;
	/* truncate file to the latest actual index */
	char *eof =
		(char*)ri->actual + sizeof(sdindexheader) +
		       ri->actual->count * ri->actual->block +
		       ri->actual->total +
		       ri->actual->extension + sizeof(sdseal);
	uint64_t file_size = eof - ri->map.p;
	int rc = sr_fileresize(ri->file, file_size);
	if (srunlikely(rc == -1))
		return -1;
	sr_errorreset(i->r->e);
	return 0;
}
#line 1 "sophia/database/sd_v.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/





static uint8_t
sd_vifflags(sv *v) {
	return ((sdv*)v->v)->flags;
}

static void
sd_vifflagsadd(sv *v, uint32_t flags) {
	((sdv*)v->v)->flags |= flags;
}

static uint64_t
sd_viflsn(sv *v) {
	return ((sdv*)v->v)->lsn;
}

static char*
sd_vifkey(sv *v)
{
	sdv *dv = v->v;
	sdpage p = {
		.h = (sdpageheader*)v->arg
	};
	return sd_pagekey(&p, dv);
}

static uint16_t
sd_vifkeysize(sv *v) {
	return ((sdv*)v->v)->keysize;
}

static char*
sd_vifvalue(sv *v)
{
	sdv *dv = v->v;
	sdpage p = {
		.h = (sdpageheader*)v->arg
	};
	return sd_pagevalue(&p, dv);
}

static uint32_t
sd_vifvaluesize(sv *v) {
	return ((sdv*)v->v)->valuesize;
}

static uint64_t
sd_vifoffset(sv *v) {
	return ((sdv*)v->v)->valueoffset;
}

static char*
sd_vifraw(sv *v) {
	return v->v;
}

static uint32_t
sd_vifrawsize(sv *v) {
	return sizeof(sdv) + ((sdv*)v->v)->keysize;
}

svif sd_vif =
{
	.flags       = sd_vifflags,
	.flagsadd    = sd_vifflagsadd,
	.lsn         = sd_viflsn,
	.lsnset      = NULL,
	.key         = sd_vifkey,
	.keysize     = sd_vifkeysize,
	.value       = sd_vifvalue,
	.valuesize   = sd_vifvaluesize,
	.valueoffset = sd_vifoffset,
	.raw         = sd_vifraw,
	.rawsize     = sd_vifrawsize,
	.ref         = NULL,
	.unref       = NULL 
};
#line 1 "sophia/index/si_conf.h"
#ifndef SI_CONF_H_
#define SI_CONF_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct siconf siconf;

struct siconf {
	char     *name;
	char     *path;
	char     *path_backup;
	int       sync;
	uint64_t  node_size;
	uint32_t  node_page_size;
};

#endif
#line 1 "sophia/index/si_zone.h"
#ifndef SI_ZONE_H_
#define SI_ZONE_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sizone sizone;
typedef struct sizonemap sizonemap;

struct sizone {
	uint32_t enable;
	char     name[4];
	uint32_t mode;
	uint32_t compact_wm;
	uint32_t branch_prio;
	uint32_t branch_wm;
	uint32_t branch_age;
	uint32_t branch_age_period;
	uint32_t branch_age_wm;
	uint32_t backup_prio;
	uint32_t gc_prio;
	uint32_t gc_period;
	uint32_t gc_wm;
};

struct sizonemap {
	sizone zones[11];
};

static inline int
si_zonemap_init(sizonemap *m) {
	memset(m->zones, 0, sizeof(m->zones));
	return 0;
}

static inline void
si_zonemap_set(sizonemap *m, uint32_t percent, sizone *z)
{
	if (srunlikely(percent > 100))
		percent = 100;
	percent = percent - percent % 10;
	int p = percent / 10;
	m->zones[p] = *z;
	snprintf(m->zones[p].name, sizeof(m->zones[p].name), "%d", percent);
}

static inline sizone*
si_zonemap(sizonemap *m, uint32_t percent)
{
	if (srunlikely(percent > 100))
		percent = 100;
	percent = percent - percent % 10;
	int p = percent / 10;
	sizone *z = &m->zones[p];
	if (!z->enable) {
		while (p >= 0) {
			z = &m->zones[p];
			if (z->enable)
				return z;
			p--;
		}
		return NULL;
	}
	return z;
}

#endif
#line 1 "sophia/index/si_branch.h"
#ifndef SI_BRANCH_H_
#define SI_BRANCH_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sibranch sibranch;

struct sibranch {
	sdid id;
	sdindex index;
	sibranch *next;
};

static inline void
si_branchinit(sibranch *b) {
	memset(&b->id, 0, sizeof(b->id));
	sd_indexinit(&b->index);
	b->next = NULL;
}

static inline sibranch*
si_branchnew(sr *r)
{
	sibranch *b = (sibranch*)sr_malloc(r->a, sizeof(sibranch));
	if (srunlikely(b == NULL)) {
		sr_malfunction(r->e, "%s", "memory allocation failed");
		return NULL;
	}
	si_branchinit(b);
	return b;
}

static inline void
si_branchset(sibranch *b, sdindex *i)
{
	b->id = i->h->id;
	b->index = *i;
}

static inline void
si_branchfree(sibranch *b, sr *r)
{
	sd_indexfree(&b->index, r);
	sr_free(r->a, b);
}

#endif
#line 1 "sophia/index/si_node.h"
#ifndef SI_NODE_H_
#define SI_NODE_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sinode sinode;

#define SI_NONE       0
#define SI_LOCK       1
#define SI_I1         2

#define SI_RDB        16
#define SI_RDB_DBI    32
#define SI_RDB_DBSEAL 64
#define SI_RDB_UNDEF  128
#define SI_RDB_REMOVE 256

struct sinode {
	uint32_t  recover;
	uint8_t   flags;
	uint64_t  update_time;
	uint32_t  used;
	uint32_t  backup;
	sibranch  self;
	sibranch *branch;
	uint32_t  branch_count;
	svindex   i0, i1;
	srfile    file;
	srrbnode  node;
	srrqnode  nodecompact;
	srrqnode  nodebranch;
	srlist    commit;
} srpacked;

sinode *si_nodenew(sr*);
int si_nodeopen(sinode*, sr*, srpath*);
int si_nodecreate(sinode*, sr*, siconf*, sdid*, sdindex*, sdbuild*);
int si_nodefree(sinode*, sr*, int);
int si_nodegc_index(sr*, svindex*);

int si_nodesync(sinode*, sr*);
int si_nodecmp(sinode*, void*, int, srcomparator*);
int si_nodeseal(sinode*, sr*, siconf*);
int si_nodecomplete(sinode*, sr*, siconf*);

static inline svindex*
si_noderotate(sinode *node) {
	node->flags |= SI_I1;
	return &node->i0;
}

static inline void
si_nodeunrotate(sinode *node) {
	assert((node->flags & SI_I1) > 0);
	node->flags &= ~SI_I1;
	node->i0 = node->i1;
	sv_indexinit(&node->i1);
}

static inline void
si_nodelock(sinode *node) {
	assert(! (node->flags & SI_LOCK));
	node->flags |= SI_LOCK;
}

static inline void
si_nodeunlock(sinode *node) {
	assert((node->flags & SI_LOCK) > 0);
	node->flags &= ~SI_LOCK;
}

static inline svindex*
si_nodeindex(sinode *node) {
	if (node->flags & SI_I1)
		return &node->i1;
	return &node->i0;
}

static inline sinode*
si_nodeof(srrbnode *node) {
	return srcast(node, sinode, node);
}

#endif
#line 1 "sophia/index/si_planner.h"
#ifndef SI_PLANNER_H_
#define SI_PLANNER_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct siplanner siplanner;
typedef struct siplan siplan;

struct siplanner {
	srrq branch;
	srrq compact;
};

/* plan */
#define SI_BRANCH        1
#define SI_AGE           2
#define SI_COMPACT       4
#define SI_CHECKPOINT    8
#define SI_GC            16
#define SI_BACKUP        32

/* explain */
#define SI_ENONE         0
#define SI_ERETRY        1
#define SI_EINDEX_SIZE   2
#define SI_EINDEX_AGE    4
#define SI_EBRANCH_COUNT 3

struct siplan {
	int explain;
	int plan;
	/* branch:
	 *   a: index_size
	 *   b: ttl
	 *   c: ttl_wm
	 * age:
	 *   a: ttl
	 *   b: ttl_wm
	 *   c:
	 * compact:
	 *   a: branches
	 *   b:
	 *   c:
	 * checkpoint:
	 *   a: lsn
	 *   b:
	 *   c:
	 * gc:
	 *   a: lsn
	 *   b: percent
	 *   c:
	 * backup:
	 *   a: bsn
	 *   b:
	 *   c:
	 */
	uint64_t a, b, c;
	sinode *node;
};

int si_planinit(siplan*);
int si_plannerinit(siplanner*, sra*);
int si_plannerfree(siplanner*, sra*);
int si_plannertrace(siplan*, srtrace*);
int si_plannerupdate(siplanner*, int, sinode*);
int si_plannerremove(siplanner*, int, sinode*);
int si_planner(siplanner*, siplan*);

#endif
#line 1 "sophia/index/si.h"
#ifndef SI_H_
#define SI_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct si si;

struct si {
	srmutex lock;
	srcond cond;
	siplanner p;
	srrb i;
	int n;
	uint64_t update_time;
	uint64_t read_disk;
	uint64_t read_cache;
	srquota *quota;
	siconf *conf;
};

static inline void
si_lock(si *i) {
	sr_mutexlock(&i->lock);
}

static inline void
si_unlock(si *i) {
	sr_mutexunlock(&i->lock);
}

int si_init(si*, sr*, srquota*);
int si_open(si*, sr*, siconf*);
int si_close(si*, sr*);
int si_insert(si*, sr*, sinode*);
int si_remove(si*, sinode*);
int si_replace(si*, sinode*, sinode*);
int si_plan(si*, siplan*);
int si_execute(si*, sr*, sdc*, siplan*, uint64_t);

#endif
#line 1 "sophia/index/si_commit.h"
#ifndef SI_COMMIT_H_
#define SI_COMMIT_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sitx sitx;

struct sitx {
	uint64_t time;
	uint64_t vlsn;
	srlist nodelist;
	svlog *l;
	svlogindex *li;
	si *index;
	sr *r;
};

void si_begin(sitx*, sr*, si*, uint64_t, uint64_t,
              svlog*, svlogindex*);
void si_commit(sitx*);
void si_write(sitx*, int);

#endif
#line 1 "sophia/index/si_cache.h"
#ifndef SI_CACHE_H_
#define SI_CACHE_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sicachebranch sicachebranch;
typedef struct sicache sicache;

struct sicachebranch {
	sibranch *branch;
	sdindexpage *ref;
	sriter i;
	srbuf buf;
	int iterate;
	sicachebranch *next;
} srpacked;

struct sicache {
	sra *ac;
	sicachebranch *path;
	sicachebranch *branch;
	uint32_t count;
	uint32_t nodeid;
	sinode *node;
};

static inline void
si_cacheinit(sicache *c, sra *ac)
{
	c->path   = NULL;
	c->branch = NULL;
	c->count  = 0;
	c->node   = NULL;
	c->nodeid = 0;
	c->ac     = ac;
}

static inline void
si_cachefree(sicache *c, sr *r)
{
	sicachebranch *next;
	sicachebranch *cb = c->path;
	while (cb) {
		next = cb->next;
		sr_buffree(&cb->buf, r->a);
		sr_free(c->ac, cb);
		cb = next;
	}
}

static inline void
si_cachereset(sicache *c)
{
	sicachebranch *cb = c->path;
	while (cb) {
		sr_bufreset(&cb->buf);
		cb->branch = NULL;
		cb->ref = NULL;
		cb->iterate = 0;
		cb = cb->next;
	}
	c->branch = NULL;
	c->node   = NULL;
	c->nodeid = 0;
	c->count  = 0;
}

static inline sicachebranch*
si_cacheadd(sicache *c, sibranch *b)
{
	sicachebranch *nb = sr_malloc(c->ac, sizeof(sicachebranch));
	if (srunlikely(nb == NULL))
		return NULL;
	nb->branch  = b;
	nb->ref     = NULL;
	nb->iterate = 0;
	nb->next    = NULL;
	sr_bufinit(&nb->buf);
	return nb;
}

static inline int
si_cachevalidate(sicache *c, sinode *n)
{
	if (srlikely(c->node == n && c->nodeid == n->self.id.id))
	{
		if (srlikely(n->branch_count == c->count)) {
			c->branch = c->path;
			return 0;
		}
		assert(n->branch_count > c->count);
		/* c b a */
		/* e d c b a */
		sicachebranch *head = NULL;
		sicachebranch *last = NULL;
		sicachebranch *cb = c->path;
		sibranch *b = n->branch;
		while (b) {
			if (cb->branch == b) {
				assert(last != NULL);
				last->next = cb;
				break;
			}
			sicachebranch *nb = si_cacheadd(c, b);
			if (srunlikely(nb == NULL))
				return -1;
			if (! head)
				head = nb;
			if (last)
				last->next = nb;
			last = nb;
			b = b->next;
		}
		c->path   = head;
		c->count  = n->branch_count;
		c->branch = c->path;
		return 0;
	}
	sicachebranch *last = c->path;
	sicachebranch *cb = last;
	sibranch *b = n->branch;
	while (cb && b) {
		cb->branch = b;
		cb->ref = NULL;
		sr_bufreset(&cb->buf);
		last = cb;
		cb = cb->next;
		b  = b->next;
	}
	while (b) {
		cb = si_cacheadd(c, b);
		if (srunlikely(cb == NULL))
			return -1;
		if (last)
			last->next = cb;
		last = cb;
		if (c->path == NULL)
			c->path = cb;
		b = b->next;
	}
	c->count  = n->branch_count;
	c->node   = n;
	c->nodeid = n->self.id.id;
	c->branch = c->path;
	return 0;
}

static inline sicachebranch*
si_cachefollow(sicache *c)
{
	sicachebranch *b = c->branch;
	c->branch = c->branch->next;
	return b;
}

#endif
#line 1 "sophia/index/si_query.h"
#ifndef SI_QUERY_H_
#define SI_QUERY_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct siquery siquery;

struct siquery {
	srorder order;
	void *key;
	uint32_t keysize;
	uint64_t vlsn;
	svmerge merge;
	sv result;
	sicache *cache;
	sr *r;
	si *index;
};

int si_queryopen(siquery*, sr*, sicache*, si*, srorder, uint64_t,
                 void*, uint32_t);
int si_queryclose(siquery*);
int si_querydup(siquery*, sv*);
int si_query(siquery*);
int si_querycommited(si*, sr*, sv*);

#endif
#line 1 "sophia/index/si_iter.h"
#ifndef SI_ITER_H_
#define SI_ITER_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

extern sriterif si_iter;

#endif
#line 1 "sophia/index/si_backup.h"
#ifndef SI_BACKUP_H_
#define SI_BACKUP_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

int si_backup(si*, sr*, sdc*, siplan*);

#endif
#line 1 "sophia/index/si_balance.h"
#ifndef SI_BALANCE_H_
#define SI_BALANCE_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

int si_branch(si*, sr*, sdc*, siplan*, uint64_t);
int si_compact(si*, sr*, sdc*, siplan*, uint64_t);

#endif
#line 1 "sophia/index/si_compaction.h"
#ifndef SI_COMPACTION_H_
#define SI_COMPACTION_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

int si_compaction(si*, sr*, sdc*, uint64_t, sinode*, sriter*,
                  uint32_t, uint32_t);

#endif
#line 1 "sophia/index/si_track.h"
#ifndef SI_TRACK_H_
#define SI_TRACK_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sitrack sitrack;

struct sitrack {
	srrb i;
	int count;
	uint32_t nsn;
	uint64_t lsn;
};

static inline void
si_trackinit(sitrack *t) {
	sr_rbinit(&t->i);
	t->count = 0;
	t->nsn = 0;
	t->lsn = 0;
}

sr_rbtruncate(si_tracktruncate,
              si_nodefree(srcast(n, sinode, node), (sr*)arg, 0))

static inline void
si_trackfree(sitrack *t, sr *r) {
	if (t->i.root)
		si_tracktruncate(t->i.root, r);
}

static inline void
si_trackmetrics(sitrack *t, sinode *n)
{
	sibranch *b = n->branch;
	while (b) {
		sdindexheader *h = b->index.h;
		if (b->id.parent > t->nsn)
			t->nsn = b->id.parent;
		if (b->id.id > t->nsn)
			t->nsn = b->id.id;
		if (h->lsnmin != UINT64_MAX && h->lsnmin > t->lsn)
			t->lsn = h->lsnmin;
		if (h->lsnmax > t->lsn)
			t->lsn = h->lsnmax;
		b = b->next;
	}
}

static inline void
si_tracknsn(sitrack *t, uint32_t nsn)
{
	if (t->nsn < nsn)
		t->nsn = nsn;
}

sr_rbget(si_trackmatch,
         sr_cmpu32((char*)&(srcast(n, sinode, node))->self.id.id, sizeof(uint32_t),
                   (char*)key, sizeof(uint32_t), NULL))

static inline void
si_trackset(sitrack *t, sinode *n)
{
	srrbnode *p = NULL;
	int rc = si_trackmatch(&t->i, NULL, (char*)&n->self.id.id,
	                       sizeof(n->self.id.id), &p);
	assert(! (rc == 0 && p));
	sr_rbset(&t->i, p, rc, &n->node);
	t->count++;
}

static inline sinode*
si_trackget(sitrack *t, uint32_t id)
{
	srrbnode *p = NULL;
	int rc = si_trackmatch(&t->i, NULL, (char*)&id, sizeof(id), &p);
	if (rc == 0 && p)
		return srcast(p, sinode, node);
	return NULL;
}

static inline void
si_trackreplace(sitrack *t, sinode *o, sinode *n)
{
	sr_rbreplace(&t->i, &o->node, &n->node);
}

static inline void
si_trackremove(sitrack *t, sinode *n)
{
	sr_rbremove(&t->i, &n->node);
	t->count--;
}

#endif
#line 1 "sophia/index/si_recover.h"
#ifndef SI_RECOVER_H_
#define SI_RECOVER_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

sinode *si_bootstrap(si*, sr*, uint32_t);
int si_recover(si*, sr*);

#endif
#line 1 "sophia/index/si_profiler.h"
#ifndef SI_PROFILER_H_
#define SI_PROFILER_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct siprofiler siprofiler;

struct siprofiler {
	si *i;
	uint32_t  total_node_count;
	uint64_t  total_node_size;
	uint32_t  total_branch_count;
	uint32_t  total_branch_avg;
	uint32_t  total_branch_max;
	uint64_t  memory_used;
	uint64_t  count;
	uint64_t  count_dup;
	uint64_t  read_disk;
	uint64_t  read_cache;
	int       histogram_branch[20];
	int       histogram_branch_20plus;
	char      histogram_branch_sz[512];
	char     *histogram_branch_ptr;
} srpacked;

int si_profilerbegin(siprofiler*, si*);
int si_profilerend(siprofiler*);
int si_profiler(siprofiler*);

#endif
#line 1 "sophia/index/si.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/






int si_init(si *i, sr *r, srquota *q)
{
	int rc = si_plannerinit(&i->p, r->a);
	if (srunlikely(rc == -1))
		return -1;
	sr_rbinit(&i->i);
	sr_mutexinit(&i->lock);
	sr_condinit(&i->cond);
	i->quota       = q;
	i->conf        = NULL;
	i->update_time = 0;
	i->read_disk   = 0;
	i->read_cache  = 0;
	return 0;
}

int si_open(si *i, sr *r, siconf *conf)
{
	i->conf = conf;
	return si_recover(i, r);
}

sr_rbtruncate(si_truncate,
              si_nodefree(srcast(n, sinode, node), (sr*)arg, 0))

int si_close(si *i, sr *r)
{
	int rcret = 0;
	if (i->i.root)
		si_truncate(i->i.root, r);
	i->i.root = NULL;
	sr_condfree(&i->cond);
	sr_mutexfree(&i->lock);
	return rcret;
}

sr_rbget(si_match,
         sr_compare(cmp,
                    sd_indexpage_min(sd_indexmin(&(srcast(n, sinode, node))->self.index)),
                    sd_indexmin(&(srcast(n, sinode, node))->self.index)->sizemin,
                    key, keysize))

int si_insert(si *i, sr *r, sinode *n)
{
	sdindexpage *min = sd_indexmin(&n->self.index);
	srrbnode *p = NULL;
	int rc = si_match(&i->i, r->cmp, sd_indexpage_min(min), min->sizemin, &p);
	assert(! (rc == 0 && p));
	sr_rbset(&i->i, p, rc, &n->node);
	i->n++;
	return 0;
}

int si_remove(si *i, sinode *n)
{
	sr_rbremove(&i->i, &n->node);
	i->n--;
	return 0;
}

int si_replace(si *i, sinode *o, sinode *n)
{
	sr_rbreplace(&i->i, &o->node, &n->node);
	return 0;
}

int si_plan(si *i, siplan *plan)
{
	si_lock(i);
	int rc = si_planner(&i->p, plan);
	si_unlock(i);
	return rc;
}

int si_execute(si *i, sr *r, sdc *c, siplan *plan, uint64_t vlsn)
{
	assert(plan->node != NULL);
	int rc = -1;
	switch (plan->plan) {
	case SI_CHECKPOINT:
	case SI_BRANCH:
	case SI_AGE:
		rc = si_branch(i, r, c, plan, vlsn);
		break;
	case SI_GC:
	case SI_COMPACT:
		rc = si_compact(i, r, c, plan, vlsn);
		break;
	case SI_BACKUP:
		rc = si_backup(i, r, c, plan);
		break;
	}
	return rc;
}
#line 1 "sophia/index/si_backup.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/






int si_backup(si *index, sr *r, sdc *c, siplan *plan)
{
	sinode *node = plan->node;
	sd_creset(c);

	char dest[1024];
	snprintf(dest, sizeof(dest), "%s/%" PRIu32 ".incomplete/%s",
	         index->conf->path_backup,
	         (uint32_t)plan->a,
	         index->conf->name);

	/* read origin file */
	int rc = sr_bufensure(&c->c, r->a, node->file.size);
	if (srunlikely(rc == -1)) {
		sr_error(r->e, "%s", "memory allocation failed");
		return -1;
	}
	rc = sr_filepread(&node->file, 0, c->c.s, node->file.size);
	if (srunlikely(rc == -1)) {
		sr_error(r->e, "db file '%s' read error: %s",
		         node->file.file, strerror(errno));
		return -1;
	}
	sr_bufadvance(&c->c, node->file.size);

	/* copy */
	srpath path;
	sr_pathA(&path, dest, node->self.id.id, ".db");
	srfile file;
	sr_fileinit(&file, r->a);
	rc = sr_filenew(&file, path.path);
	if (srunlikely(rc == -1)) {
		sr_error(r->e, "backup db file '%s' create error: %s",
		         path.path, strerror(errno));
		return -1;
	}
	rc = sr_filewrite(&file, c->c.s, node->file.size);
	if (srunlikely(rc == -1)) {
		sr_error(r->e, "backup db file '%s' write error: %s",
				 path.path, strerror(errno));
		sr_fileclose(&file);
		return -1;
	}
	/* sync? */
	rc = sr_fileclose(&file);
	if (srunlikely(rc == -1)) {
		sr_error(r->e, "backup db file '%s' close error: %s",
				 path.path, strerror(errno));
		return -1;
	}

	si_lock(index);
	node->backup = plan->a;
	si_nodeunlock(node);
	si_unlock(index);
	return 0;
}
#line 1 "sophia/index/si_balance.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/






static inline sibranch*
si_branchcreate(si *index, sr *r, sdc *c, sinode *parent, svindex *vindex, uint64_t vlsn)
{
	svmerge vmerge;
	sv_mergeinit(&vmerge);
	int rc = sv_mergeprepare(&vmerge, r, 1);
	if (srunlikely(rc == -1))
		return NULL;
	svmergesrc *s = sv_mergeadd(&vmerge, NULL);
	sr_iterinit(&s->src, &sv_indexiterraw, r);
	sr_iteropen(&s->src, vindex);
	sriter i;
	sr_iterinit(&i, &sv_mergeiter, r);
	sr_iteropen(&i, &vmerge, SR_GTE);

	/* merge iter is not used */
	sdmerge merge;
	sd_mergeinit(&merge, r, parent->self.id.id,
	             &i,
	             &c->build,
	             parent->file.size,
	             vindex->keymax,
	             vindex->used,
	             UINT64_MAX,
	             index->conf->node_page_size, 1,
	             vlsn);
	rc = sd_merge(&merge);
	if (srunlikely(rc == -1)) {
		sv_mergefree(&vmerge, r->a);
		sr_malfunction(r->e, "%s", "memory allocation failed");
		goto error;
	}
	assert(rc == 1);
	sv_mergefree(&vmerge, r->a);

	sibranch *branch = si_branchnew(r);
	if (srunlikely(branch == NULL))
		goto error;
	sdid id = {
		.parent = parent->self.id.id,
		.flags  = SD_IDBRANCH,
		.id     = sr_seq(r->seq, SR_NSNNEXT)
	};
	rc = sd_mergecommit(&merge, &id);
	if (srunlikely(rc == -1))
		goto error;

	si_branchset(branch, &merge.index);
	rc = sd_buildwrite(&c->build, &branch->index, &parent->file);
	if (srunlikely(rc == -1)) {
		si_branchfree(branch, r);
		return NULL;
	}

	SR_INJECTION(r->i, SR_INJECTION_SI_BRANCH_0,
	             sr_malfunction(r->e, "%s", "error injection");
	             si_branchfree(branch, r);
	             return NULL);

	if (index->conf->sync) {
		rc = si_nodesync(parent, r);
		if (srunlikely(rc == -1)) {
			si_branchfree(branch, r);
			return NULL;
		}
	}
	return branch;
error:
	sd_mergefree(&merge);
	return NULL;
}

int si_branch(si *index, sr *r, sdc *c, siplan *plan, uint64_t vlsn)
{
	sinode *n = plan->node;
	assert(n->flags & SI_LOCK);

	si_lock(index);
	if (srunlikely(n->used == 0)) {
		si_nodeunlock(n);
		si_unlock(index);
		return 0;
	}
	svindex *i;
	i = si_noderotate(n);
	si_unlock(index);

	sd_creset(c);
	sibranch *branch = si_branchcreate(index, r, c, n, i, vlsn);
	if (srunlikely(branch == NULL))
		return -1;

	/* commit */
	si_lock(index);
	branch->next = n->branch;
	n->branch = branch;
	n->branch_count++;
	uint32_t used = sv_indexused(i);
	n->used -= used;
	sr_quota(index->quota, SR_QREMOVE, used);
	svindex swap = *i;
	si_nodeunrotate(n);
	si_nodeunlock(n);
	si_plannerupdate(&index->p, SI_BRANCH|SI_COMPACT, n);
	si_unlock(index);

	/* gc */
	si_nodegc_index(r, &swap);
	return 1;
}

int si_compact(si *index, sr *r, sdc *c, siplan *plan, uint64_t vlsn)
{
	sinode *node = plan->node;
	assert(node->flags & SI_LOCK);

	/* read file */
	sd_creset(c);
	int rc = sr_bufensure(&c->c, r->a, node->file.size);
	if (srunlikely(rc == -1)) {
		sr_malfunction(r->e, "%s", "memory allocation failed");
		return -1;
	}
	rc = sr_filepread(&node->file, 0, c->c.s, node->file.size);
	if (srunlikely(rc == -1)) {
		sr_malfunction(r->e, "db file '%s' read error: %s",
		               node->file.file, strerror(errno));
		return -1;
	}
	sr_bufadvance(&c->c, node->file.size);

	/* prepare for compaction */
	svmerge merge;
	sv_mergeinit(&merge);
	rc = sv_mergeprepare(&merge, r, node->branch_count);
	if (srunlikely(rc == -1))
		return -1;
	uint32_t size_stream = 0;
	uint32_t size_key = 0;
	uint32_t gc = 0;
	sibranch *b = node->branch;
	while (b) {
		svmergesrc *s = sv_mergeadd(&merge, NULL);
		uint16_t key = sd_indexkeysize(&b->index);
		if (key > size_key)
			size_key = key;
		size_stream += sd_indextotal_kv(&b->index);
		sr_iterinit(&s->src, &sd_iter, r);
		sr_iteropen(&s->src, &b->index, c->c.s, 0);
		b = b->next;
	}
	sriter i;
	sr_iterinit(&i, &sv_mergeiter, r);
	sr_iteropen(&i, &merge, SR_GTE);
	rc = si_compaction(index, r, c, vlsn, node, &i, size_stream, size_key);
	if (srunlikely(rc == -1)) {
		sv_mergefree(&merge, r->a);
		return -1;
	}
	sv_mergefree(&merge, r->a);
	if (gc) {
		sr_quota(index->quota, SR_QREMOVE, gc);
	}
	return 0;
}
#line 1 "sophia/index/si_commit.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/







uint32_t
si_vgc(sra *a, svv *gc)
{
	uint32_t used = 0;
	svv *v = gc;
	while (v) {
		used += sv_vsize(v);
		svv *n = v->next;
		sl *log = (sl*)v->log;
		if (log)
			sr_gcsweep(&log->gc, 1);
		sr_free(a, v);
		v = n;
	}
	return used;
}

void si_begin(sitx *t, sr *r, si *index, uint64_t vlsn, uint64_t time,
              svlog *l,
              svlogindex *li)
{
	t->index = index;
	t->time  = time;
	t->vlsn  = vlsn;
	t->r     = r;
	t->l     = l;
	t->li    = li;
	sr_listinit(&t->nodelist);
	si_lock(index);
}

void si_commit(sitx *t)
{
	/* reschedule nodes */
	srlist *i, *n;
	sr_listforeach_safe(&t->nodelist, i, n) {
		sinode *node = srcast(i, sinode, commit);
		sr_listinit(&node->commit);
		si_plannerupdate(&t->index->p, SI_BRANCH, node);
	}
	si_unlock(t->index);
}

static inline void
si_set(sitx *t, svv *v)
{
	si *index = t->index;
	t->index->update_time = t->time;
	/* match node */
	sriter i;
	sr_iterinit(&i, &si_iter, t->r);
	sr_iteropen(&i, index, SR_ROUTE, sv_vkey(v), v->keysize);
	sinode *node = sr_iterof(&i);
	assert(node != NULL);
	/* update node */
	svindex *vindex = si_nodeindex(node);
	svv *vgc = NULL;
	sv_indexset(vindex, t->r, t->vlsn, v, &vgc);
	node->update_time = index->update_time;
	node->used += sv_vsize(v);
	if (srunlikely(vgc)) {
		uint32_t gc = si_vgc(t->r->a, vgc);
		node->used -= gc;
		sr_quota(index->quota, SR_QREMOVE, gc);
	}
	if (sr_listempty(&node->commit))
		sr_listappend(&t->nodelist, &node->commit);
}

void si_write(sitx *t, int check)
{
	svlogv *cv = sv_logat(t->l, t->li->head);
	int c = t->li->count;
	while (c) {
		svv *v = cv->v.v;
		if (check && si_querycommited(t->index, t->r, &cv->v)) {
			uint32_t gc = si_vgc(t->r->a, v);
			sr_quota(t->index->quota, SR_QREMOVE, gc);
			goto next;
		}
		si_set(t, v);
next:
		cv = sv_logat(t->l, cv->next);
		c--;
	}
}
#line 1 "sophia/index/si_compaction.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/






extern uint32_t si_vgc(sra*, svv*);

static int
si_redistribute(si *index, sr *r, sdc *c, sinode *node, srbuf *result,
                uint64_t vlsn)
{
	svindex *vindex = si_nodeindex(node);
	sriter i;
	sr_iterinit(&i, &sv_indexiterraw, r);
	sr_iteropen(&i, vindex);
	for (; sr_iterhas(&i); sr_iternext(&i)) {
		sv *v = sr_iterof(&i);
		int rc = sr_bufadd(&c->b, r->a, &v->v, sizeof(svv**));
		if (srunlikely(rc == -1))
			return sr_malfunction(r->e, "%s", "memory allocation failed");
	}
	if (srunlikely(sr_bufused(&c->b) == 0))
		return 0;
	uint32_t gc = 0;
	sr_iterinit(&i, &sr_bufiterref, NULL);
	sr_iteropen(&i, &c->b, sizeof(svv*));
	sriter j;
	sr_iterinit(&j, &sr_bufiterref, NULL);
	sr_iteropen(&j, result, sizeof(sinode*));
	sinode *prev = sr_iterof(&j);
	sr_iternext(&j);
	while (1) {
		sinode *p = sr_iterof(&j);
		if (p == NULL) {
			assert(prev != NULL);
			while (sr_iterhas(&i)) {
				svv *v = sr_iterof(&i);
				v->next = NULL;

				svv *vgc = NULL;
				sv_indexset(&prev->i0, r, vlsn, v, &vgc);
				sr_iternext(&i);
				if (vgc) {
					gc += si_vgc(r->a, vgc);
				}
			}
			break;
		}
		while (sr_iterhas(&i)) {
			svv *v = sr_iterof(&i);
			v->next = NULL;

			svv *vgc = NULL;
			sdindexpage *page = sd_indexmin(&p->self.index);
			int rc = sr_compare(r->cmp, sv_vkey(v), v->keysize,
			                    sd_indexpage_min(page), page->sizemin);
			if (srunlikely(rc >= 0))
				break;
			sv_indexset(&prev->i0, r, vlsn, v, &vgc);
			sr_iternext(&i);
			if (vgc) {
				gc += si_vgc(r->a, vgc);
			}
		}
		if (srunlikely(! sr_iterhas(&i)))
			break;
		prev = p;
		sr_iternext(&j);
	}
	if (gc) {
		sr_quota(index->quota, SR_QREMOVE, gc);
	}
	assert(sr_iterof(&i) == NULL);
	return 0;
}

static inline void
si_redistribute_set(si *index, sr *r, uint64_t vlsn, uint64_t now, svv *v)
{
	index->update_time = now;
	/* match node */
	sriter i;
	sr_iterinit(&i, &si_iter, r);
	sr_iteropen(&i, index, SR_ROUTE, sv_vkey(v), v->keysize);
	sinode *node = sr_iterof(&i);
	assert(node != NULL);
	/* update node */
	svindex *vindex = si_nodeindex(node);
	svv *vgc = NULL;
	sv_indexset(vindex, r, vlsn, v, &vgc);
	node->update_time = index->update_time;
	node->used += sv_vsize(v);
	if (srunlikely(vgc)) {
		uint32_t gc = si_vgc(r->a, vgc);
		node->used -= gc;
		sr_quota(index->quota, SR_QREMOVE, gc);
	}
	/* schedule node */
	si_plannerupdate(&index->p, SI_BRANCH, node);
}

static int
si_redistribute_index(si *index, sr *r, sdc *c, sinode *node, uint64_t vlsn)
{
	svindex *vindex = si_nodeindex(node);
	sriter i;
	sr_iterinit(&i, &sv_indexiterraw, r);
	sr_iteropen(&i, vindex);
	for (; sr_iterhas(&i); sr_iternext(&i)) {
		sv *v = sr_iterof(&i);
		int rc = sr_bufadd(&c->b, r->a, &v->v, sizeof(svv**));
		if (srunlikely(rc == -1))
			return sr_malfunction(r->e, "%s", "memory allocation failed");
	}
	if (srunlikely(sr_bufused(&c->b) == 0))
		return 0;
	uint64_t now = sr_utime();
	sr_iterinit(&i, &sr_bufiterref, NULL);
	sr_iteropen(&i, &c->b, sizeof(svv*));
	while (sr_iterhas(&i)) {
		svv *v = sr_iterof(&i);
		si_redistribute_set(index, r, vlsn, now, v);
		sr_iternext(&i);
	}
	return 0;
}

static int
si_splitfree(srbuf *result, sr *r)
{
	sriter i;
	sr_iterinit(&i, &sr_bufiterref, NULL);
	sr_iteropen(&i, result, sizeof(sinode*));
	for (; sr_iterhas(&i); sr_iternext(&i)) {
		sinode *p = sr_iterof(&i);
		si_nodefree(p, r, 0);
	}
	return 0;
}

static inline int
si_split(si *index, sr *r, sdc *c, srbuf *result,
         sinode   *parent,
         sriter   *i,
         uint64_t  size_node,
         uint32_t  size_key,
         uint32_t  size_stream,
         uint64_t  vlsn)
{
	int count = 0;
	int rc;
	sdmerge merge;
	sd_mergeinit(&merge, r, parent->self.id.id,
	             i, &c->build,
	             0, /* offset */
	             size_key,
	             size_stream,
	             size_node,
	             index->conf->node_page_size, 0, vlsn);
	while ((rc = sd_merge(&merge)) > 0)
	{
		sinode *n = si_nodenew(r);
		if (srunlikely(n == NULL))
			goto error;
		sdid id = {
			.parent = parent->self.id.id,
			.flags  = 0,
			.id     = sr_seq(r->seq, SR_NSNNEXT)
		};
		rc = sd_mergecommit(&merge, &id);
		if (srunlikely(rc == -1))
			goto error;
		rc = si_nodecreate(n, r, index->conf, &id, &merge.index, &c->build);
		if (srunlikely(rc == -1))
			goto error;
		rc = sr_bufadd(result, r->a, &n, sizeof(sinode*));
		if (srunlikely(rc == -1)) {
			sr_malfunction(r->e, "%s", "memory allocation failed");
			si_nodefree(n, r, 1);
			goto error;
		}
		sd_buildreset(&c->build);
		count++;
	}
	if (srunlikely(rc == -1))
		goto error;
	return 0;
error:
	si_splitfree(result, r);
	sd_mergefree(&merge);
	return -1;
}

int si_compaction(si *index, sr *r, sdc *c, uint64_t vlsn,
                  sinode *node,
                  sriter *stream,
                  uint32_t size_stream,
                  uint32_t size_key)
{
	srbuf *result = &c->a;
	sriter i;

	/* begin compaction.
	 *
	 * split merge stream into a number
	 * of a new nodes.
	 */
	int rc;
	rc = si_split(index, r, c, result,
	              node, stream,
	              index->conf->node_size,
	              size_key,
	              size_stream,
	              vlsn);
	if (srunlikely(rc == -1))
		return -1;

	SR_INJECTION(r->i, SR_INJECTION_SI_COMPACTION_0,
	             si_splitfree(result, r);
	             sr_malfunction(r->e, "%s", "error injection");
	             return -1);

	/* mask removal of a single node as a
	 * single node update */
	int count = sr_bufused(result) / sizeof(sinode*);
	int count_index;

	si_lock(index);
	count_index = index->n;
	si_unlock(index);

	sinode *n;
	if (srunlikely(count == 0 && count_index == 1))
	{
		n = si_bootstrap(index, r, node->self.id.id);
		if (srunlikely(n == NULL))
			return -1;
		rc = sr_bufadd(result, r->a, &n, sizeof(sinode*));
		if (srunlikely(rc == -1)) {
			sr_malfunction(r->e, "%s", "memory allocation failed");
			si_nodefree(n, r, 1);
			return -1;
		}
		count++;
	}

	/* commit compaction changes */
	si_lock(index);
	svindex *j = si_nodeindex(node);
	si_plannerremove(&index->p, SI_COMPACT|SI_BRANCH, node);
	switch (count) {
	case 0: /* delete */
		si_remove(index, node);
		si_redistribute_index(index, r, c, node, vlsn);
		uint32_t used = sv_indexused(j);
		if (used) {
			sr_quota(index->quota, SR_QREMOVE, used);
		}
		break;
	case 1: /* self update */
		n = *(sinode**)result->s;
		n->i0   = *j;
		n->used = sv_indexused(j);
		si_nodelock(n);
		si_replace(index, node, n);
		si_plannerupdate(&index->p, SI_COMPACT|SI_BRANCH, n);
		break;
	default: /* split */
		rc = si_redistribute(index, r, c, node, result, vlsn);
		if (srunlikely(rc == -1)) {
			si_unlock(index);
			si_splitfree(result, r);
			return -1;
		}
		sr_iterinit(&i, &sr_bufiterref, NULL);
		sr_iteropen(&i, result, sizeof(sinode*));
		n = sr_iterof(&i);
		n->used = sv_indexused(&n->i0);
		si_nodelock(n);
		si_replace(index, node, n);
		si_plannerupdate(&index->p, SI_COMPACT|SI_BRANCH, n);
		for (sr_iternext(&i); sr_iterhas(&i);
		     sr_iternext(&i)) {
			n = sr_iterof(&i);
			n->used = sv_indexused(&n->i0);
			si_nodelock(n);
			si_insert(index, r, n);
			si_plannerupdate(&index->p, SI_COMPACT|SI_BRANCH, n);
		}
		break;
	}
	sv_indexinit(j);
	si_unlock(index);

	/* compaction completion */

	/* seal nodes */
	sr_iterinit(&i, &sr_bufiterref, NULL);
	sr_iteropen(&i, result, sizeof(sinode*));
	for (; sr_iterhas(&i); sr_iternext(&i)) {
		n = sr_iterof(&i);
		if (index->conf->sync) {
			rc = si_nodesync(n, r);
			if (srunlikely(rc == -1))
				return -1;
		}
		rc = si_nodeseal(n, r, index->conf);
		if (srunlikely(rc == -1))
			return -1;
		SR_INJECTION(r->i, SR_INJECTION_SI_COMPACTION_3,
		             si_nodefree(node, r, 0);
		             sr_malfunction(r->e, "%s", "error injection");
		             return -1);
	}

	SR_INJECTION(r->i, SR_INJECTION_SI_COMPACTION_1,
	             si_nodefree(node, r, 0);
	             sr_malfunction(r->e, "%s", "error injection");
	             return -1);

	/* gc old node */
	rc = si_nodefree(node, r, 1);
	if (srunlikely(rc == -1))
		return -1;

	SR_INJECTION(r->i, SR_INJECTION_SI_COMPACTION_2,
	             sr_malfunction(r->e, "%s", "error injection");
	             return -1);

	/* complete new nodes */
	sr_iterinit(&i, &sr_bufiterref, NULL);
	sr_iteropen(&i, result, sizeof(sinode*));
	for (; sr_iterhas(&i); sr_iternext(&i)) {
		n = sr_iterof(&i);
		rc = si_nodecomplete(n, r, index->conf);
		if (srunlikely(rc == -1))
			return -1;
		SR_INJECTION(r->i, SR_INJECTION_SI_COMPACTION_4,
		             sr_malfunction(r->e, "%s", "error injection");
		             return -1);
	}

	/* unlock */
	si_lock(index);
	sr_iterinit(&i, &sr_bufiterref, NULL);
	sr_iteropen(&i, result, sizeof(sinode*));
	for (; sr_iterhas(&i); sr_iternext(&i)) {
		n = sr_iterof(&i);
		si_nodeunlock(n);
	}
	si_unlock(index);
	return 0;
}
#line 1 "sophia/index/si_iter.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/






sr_rbget(si_itermatch,
         si_nodecmp(srcast(n, sinode, node), key, keysize, cmp))

typedef struct siiter siiter;

struct siiter {
	si *index;
	srrbnode *v;
	srorder order;
	void *key;
	int keysize;
} srpacked;

static void
si_iterinit(sriter *i)
{
	assert(sizeof(siiter) <= sizeof(i->priv));
	siiter *ii = (siiter*)i->priv;
	memset(ii, 0, sizeof(*ii));
}

static int
si_iteropen(sriter *i, va_list args)
{
	siiter *ii = (siiter*)i->priv;
	ii->index   = va_arg(args, si*);
	ii->order   = va_arg(args, srorder);
	ii->key     = va_arg(args, void*);
	ii->keysize = va_arg(args, int);
	ii->v       = NULL;
	int eq = 0;
	if (srunlikely(ii->index->n == 1)) {
		ii->v = sr_rbmin(&ii->index->i);
		return 1;
	}
	int rc;
	switch (ii->order) {
	case SR_LT:
	case SR_LTE:
		if (srunlikely(ii->key == NULL)) {
			ii->v = sr_rbmax(&ii->index->i);
			break;
		}
		rc = si_itermatch(&ii->index->i, i->r->cmp, ii->key, ii->keysize, &ii->v);
		if (ii->v == NULL)
			break;
		switch (rc) {
		case 0:
			if (ii->order == SR_LT) {
				eq = 1;
				sinode *n = si_nodeof(ii->v);
				sdindexpage *min = sd_indexmin(&n->self.index);
				int l = sr_compare(i->r->cmp, sd_indexpage_min(min), min->sizemin,
				                   ii->key, ii->keysize);
				if (srunlikely(l == 0))
					ii->v = sr_rbprev(&ii->index->i, ii->v);
			}
			break;
		case 1:
			ii->v = sr_rbprev(&ii->index->i, ii->v);
			break;
		}
		break;
	case SR_GT:
	case SR_GTE:
		if (srunlikely(ii->key == NULL)) {
			ii->v = sr_rbmin(&ii->index->i);
			break;
		}
		rc = si_itermatch(&ii->index->i, i->r->cmp, ii->key, ii->keysize, &ii->v);
		if (ii->v == NULL)
			break;
		switch (rc) {
		case  0:
			if (ii->order == SR_GT) {
				eq = 1;
				sinode *n = si_nodeof(ii->v);
				sdindexpage *max = sd_indexmax(&n->self.index);
				int r = sr_compare(i->r->cmp, sd_indexpage_max(max), max->sizemax,
				                   ii->key, ii->keysize);
				if (srunlikely(r == 0))
					ii->v = sr_rbnext(&ii->index->i, ii->v);
			}
			break;
		case -1:
			ii->v = sr_rbnext(&ii->index->i, ii->v);
			break;
		}
		break;
	case SR_ROUTE:
		assert(ii->key != NULL);
		rc = si_itermatch(&ii->index->i, i->r->cmp, ii->key, ii->keysize, &ii->v);
		if (srunlikely(ii->v == NULL)) {
			assert(rc != 0);
			if (rc == 1)
				ii->v = sr_rbmin(&ii->index->i);
			else
				ii->v = sr_rbmax(&ii->index->i);
		} else {
			eq = rc == 0 && ii->v;
			if (rc == 1) {
				ii->v = sr_rbprev(&ii->index->i, ii->v);
				if (srunlikely(ii->v == NULL))
					ii->v = sr_rbmin(&ii->index->i);
			}
		}
		assert(ii->v != NULL);
		break;
	case SR_RANDOM: {
		assert(ii->key != NULL);
		uint32_t rnd = *(uint32_t*)ii->key;
		rnd %= ii->index->n;
		ii->v = sr_rbmin(&ii->index->i);
		uint32_t pos = 0;
		while (pos != rnd) {
			ii->v = sr_rbnext(&ii->index->i, ii->v);
			pos++;
		}
		break;
	}
	default: assert(0);
	}
	return eq;
}

static void
si_iterclose(sriter *i srunused)
{ }

static int
si_iterhas(sriter *i)
{
	siiter *ii = (siiter*)i->priv;
	return ii->v != NULL;
}

static void*
si_iterof(sriter *i)
{
	siiter *ii = (siiter*)i->priv;
	if (srunlikely(ii->v == NULL))
		return NULL;
	sinode *n = si_nodeof(ii->v);
	return n;
}

static void
si_iternext(sriter *i)
{
	siiter *ii = (siiter*)i->priv;
	switch (ii->order) {
	case SR_LT:
	case SR_LTE:
		ii->v = sr_rbprev(&ii->index->i, ii->v);
		break;
	case SR_GT:
	case SR_GTE:
		ii->v = sr_rbnext(&ii->index->i, ii->v);
		break;
	default: assert(0);
	}
}

sriterif si_iter =
{
	.init  = si_iterinit,
	.open  = si_iteropen,
	.close = si_iterclose,
	.has   = si_iterhas,
	.of    = si_iterof,
	.next  = si_iternext
};
#line 1 "sophia/index/si_node.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/







sinode *si_nodenew(sr *r)
{
	sinode *n = (sinode*)sr_malloc(r->a, sizeof(sinode));
	if (srunlikely(n == NULL)) {
		sr_malfunction(r->e, "%s", "memory allocation failed");
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
	sr_fileinit(&n->file, r->a);
	sv_indexinit(&n->i0);
	sv_indexinit(&n->i1);
	sr_rbinitnode(&n->node);
	sr_rqinitnode(&n->nodecompact);
	sr_rqinitnode(&n->nodebranch);
	sr_listinit(&n->commit);
	return n;
}

static inline int
si_nodeclose(sinode *n, sr *r)
{
	int rcret = 0;
	int rc = sr_fileclose(&n->file);
	if (srunlikely(rc == -1)) {
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
	sriter i;
	sr_iterinit(&i, &sd_recover, r);
	sr_iteropen(&i, &n->file);
	int first = 1;
	int rc;
	while (sr_iterhas(&i)) {
		sdindexheader *h = sr_iterof(&i);
		sibranch *b;
		if (first) {
			b =  &n->self;
		} else {
			b = si_branchnew(r);
			if (srunlikely(b == NULL))
				goto error;
		}
		sdindex index;
		sd_indexinit(&index);
		rc = sd_indexcopy(&index, r, h);
		if (srunlikely(rc == -1))
			goto error;
		si_branchset(b, &index);

		b->next   = n->branch;
		n->branch = b;
		n->branch_count++;

		first = 0;
		sr_iternext(&i);
	}
	rc = sd_recovercomplete(&i);
	if (srunlikely(rc == -1))
		goto error;
	sr_iterclose(&i);
	return 0;
error:
	sr_iterclose(&i);
	return -1;
}

int si_nodeopen(sinode *n, sr *r, srpath *path)
{
	int rc = sr_fileopen(&n->file, path->path);
	if (srunlikely(rc == -1)) {
		sr_malfunction(r->e, "db file '%s' open error: %s",
		               n->file.file, strerror(errno));
		return -1;
	}
	rc = sr_fileseek(&n->file, n->file.size);
	if (srunlikely(rc == -1)) {
		si_nodeclose(n, r);
		sr_malfunction(r->e, "db file '%s' seek error: %s",
		               n->file.file, strerror(errno));
		return -1;
	}
	rc = si_noderecover(n, r);
	if (srunlikely(rc == -1))
		si_nodeclose(n, r);
	return rc;
}

int si_nodecreate(sinode *n, sr *r, siconf *conf, sdid *id,
                  sdindex *i,
                  sdbuild *build)
{
	si_branchset(&n->self, i);
	srpath path;
	sr_pathAB(&path, conf->path, id->parent, id->id, ".db.incomplete");
	int rc = sr_filenew(&n->file, path.path);
	if (srunlikely(rc == -1)) {
		sr_malfunction(r->e, "db file '%s' create error: %s",
		               path.path, strerror(errno));
		return -1;
	}
	rc = sd_buildwrite(build, &n->self.index, &n->file);
	if (srunlikely(rc == -1))
		return -1;
	n->branch = &n->self;
	n->branch_count++;
	return 0;
}

int si_nodesync(sinode *n, sr *r)
{
	int rc = sr_filesync(&n->file);
	if (srunlikely(rc == -1)) {
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
		rc = sr_fileunlink(n->file.file);
		if (srunlikely(rc == -1)) {
			sr_malfunction(r->e, "db file '%s' unlink error: %s",
			               n->file.file, strerror(errno));
			rcret = -1;
		}
	}
	si_nodefree_branches(n, r);
	rc = si_nodeclose(n, r);
	if (srunlikely(rc == -1))
		rcret = -1;
	sr_free(r->a, n);
	return rcret;
}

uint32_t si_vgc(sra*, svv*);

sr_rbtruncate(si_nodegc_indexgc,
              si_vgc((sra*)arg, srcast(n, svv, node)))

int si_nodegc_index(sr *r, svindex *i)
{
	if (i->i.root)
		si_nodegc_indexgc(i->i.root, r->a);
	sv_indexinit(i);
	return 0;
}

int si_nodecmp(sinode *n, void *key, int size, srcomparator *c)
{
	sdindexpage *min = sd_indexmin(&n->self.index);
	sdindexpage *max = sd_indexmax(&n->self.index);
	int l = sr_compare(c, sd_indexpage_min(min), min->sizemin, key, size);
	int r = sr_compare(c, sd_indexpage_max(max), max->sizemin, key, size);
	/* inside range */
	if (l <= 0 && r >= 0)
		return 0;
	/* key > range */
	if (l == -1)
		return -1;
	/* key < range */
	assert(r == 1);
	return 1;
}

int si_nodeseal(sinode *n, sr *r, siconf *conf)
{
	srpath path;
	sr_pathAB(&path, conf->path, n->self.id.parent,
	          n->self.id.id, ".db.seal");
	int rc = sr_filerename(&n->file, path.path);
	if (srunlikely(rc == -1)) {
		sr_malfunction(r->e, "db file '%s' rename error: %s",
		               n->file.file, strerror(errno));
	}
	return rc;
}

int si_nodecomplete(sinode *n, sr *r, siconf *conf)
{
	srpath path;
	sr_pathA(&path, conf->path, n->self.id.id, ".db");
	int rc = sr_filerename(&n->file, path.path);
	if (srunlikely(rc == -1)) {
		sr_malfunction(r->e, "db file '%s' rename error: %s",
		               n->file.file, strerror(errno));
	}
	return rc;
}
#line 1 "sophia/index/si_planner.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/






int si_planinit(siplan *p)
{
	p->plan    = SI_NONE;
	p->explain = SI_ENONE;
	p->a       = 0;
	p->b       = 0;
	p->c       = 0;
	p->node    = NULL;
	return 0;
}

int si_plannerinit(siplanner *p, sra *a)
{
	int rc = sr_rqinit(&p->compact, a, 1, 20);
	if (srunlikely(rc == -1))
		return -1;
	rc = sr_rqinit(&p->branch, a, 512 * 1024, 100); /* ~ 50 Mb */
	if (srunlikely(rc == -1)) {
		sr_rqfree(&p->compact, a);
		return -1;
	}
	return 0;
}

int si_plannerfree(siplanner *p, sra *a)
{
	sr_rqfree(&p->compact, a);
	sr_rqfree(&p->branch, a);
	return 0;
}

int si_plannertrace(siplan *p, srtrace *t)
{
	char *plan = NULL;
	switch (p->plan) {
	case SI_BRANCH: plan = "branch";
		break;
	case SI_AGE: plan = "age";
		break;
	case SI_COMPACT: plan = "compact";
		break;
	case SI_CHECKPOINT: plan = "checkpoint";
		break;
	case SI_GC: plan = "gc";
		break;
	case SI_BACKUP: plan = "backup";
		break;
	}
	char *explain = NULL;;
	switch (p->explain) {
	case SI_ENONE:
		explain = "none";
		break;
	case SI_ERETRY:
		explain = "retry expected";
		break;
	case SI_EINDEX_SIZE:
		explain = "index size";
		break;
	case SI_EINDEX_AGE:
		explain = "index age";
		break;
	case SI_EBRANCH_COUNT:
		explain = "branch count";
		break;
	}
	sr_trace(t, "%s <#%" PRIu32 " explain: %s>",
	         plan,
	         p->node->self.id.id, explain);
	return 0;
}

int si_plannerupdate(siplanner *p, int mask, sinode *n)
{
	if (mask & SI_BRANCH)
		sr_rqupdate(&p->branch, &n->nodebranch, n->used);
	if (mask & SI_COMPACT)
		sr_rqupdate(&p->compact, &n->nodecompact, n->branch_count);
	return 0;
}

int si_plannerremove(siplanner *p, int mask, sinode *n)
{
	if (mask & SI_BRANCH)
		sr_rqdelete(&p->branch, &n->nodebranch);
	if (mask & SI_COMPACT)
		sr_rqdelete(&p->compact, &n->nodecompact);
	return 0;
}

static inline int
si_plannerpeek_backup(siplanner *p, siplan *plan)
{
	/* try to peek a node which has
	 * bsn <= required value
	*/
	int rc_inprogress = 0;
	sinode *n;
	srrqnode *pn = NULL;
	while ((pn = sr_rqprev(&p->branch, pn))) {
		n = srcast(pn, sinode, nodebranch);
		if (n->backup < plan->a) {
			if (n->flags & SI_LOCK) {
				rc_inprogress = 2;
				continue;
			}
			goto match;
		}
	}
	if (rc_inprogress)
		plan->explain = SI_ERETRY;
	return rc_inprogress;
match:
	si_nodelock(n);
	plan->explain = SI_ENONE;
	plan->node = n;
	return 1;
}

static inline int
si_plannerpeek_checkpoint(siplanner *p, siplan *plan)
{
	/* try to peek a node which has min
	 * lsn <= required value
	*/
	int rc_inprogress = 0;
	sinode *n;
	srrqnode *pn = NULL;
	while ((pn = sr_rqprev(&p->branch, pn))) {
		n = srcast(pn, sinode, nodebranch);
		if (n->i0.lsnmin <= plan->a) {
			if (n->flags & SI_LOCK) {
				rc_inprogress = 2;
				continue;
			}
			goto match;
		}
	}
	if (rc_inprogress)
		plan->explain = SI_ERETRY;
	return rc_inprogress;
match:
	si_nodelock(n);
	plan->explain = SI_ENONE;
	plan->node = n;
	return 1;
}

static inline int
si_plannerpeek_branch(siplanner *p, siplan *plan)
{
	/* try to peek a node with a biggest in-memory index */
	sinode *n;
	srrqnode *pn = NULL;
	while ((pn = sr_rqprev(&p->branch, pn))) {
		n = srcast(pn, sinode, nodebranch);
		if (n->flags & SI_LOCK)
			continue;
		if (n->used >= plan->a)
			goto match;
		return 0;
	}
	return 0;
match:
	si_nodelock(n);
	plan->explain = SI_EINDEX_SIZE;
	plan->node = n;
	return 1;
}

static inline int
si_plannerpeek_age(siplanner *p, siplan *plan)
{
	/* try to peek a node with update >= a and in-memory
	 * index size >= b */

	/* full scan */
	uint64_t now = sr_utime();
	sinode *n = NULL;
	srrqnode *pn = NULL;
	while ((pn = sr_rqprev(&p->branch, pn))) {
		n = srcast(pn, sinode, nodebranch);
		if (n->flags & SI_LOCK)
			continue;
		if (n->used >= plan->b && ((now - n->update_time) >= plan->a))
			goto match;
	}
	return 0;
match:
	si_nodelock(n);
	plan->explain = SI_EINDEX_AGE;
	plan->node = n;
	return 1;
}

static inline int
si_plannerpeek_compact(siplanner *p, siplan *plan)
{
	/* try to peek a node with a biggest number
	 * of branches */
	sinode *n;
	srrqnode *pn = NULL;
	while ((pn = sr_rqprev(&p->compact, pn))) {
		n = srcast(pn, sinode, nodecompact);
		if (n->flags & SI_LOCK)
			continue;
		if (n->branch_count >= plan->a)
			goto match;
		return 0;
	}
	return 0;
match:
	si_nodelock(n);
	plan->explain = SI_EBRANCH_COUNT;
	plan->node = n;
	return 1;
}

static inline int
si_plannerpeek_gc(siplanner *p, siplan *plan)
{
	/* try to peek a node with a biggest number
	 * of branches which is ready for gc */
	int rc_inprogress = 0;
	sinode *n;
	srrqnode *pn = NULL;
	while ((pn = sr_rqprev(&p->compact, pn))) {
		n = srcast(pn, sinode, nodecompact);
		sdindexheader *h = n->self.index.h;
		if (srlikely(h->dupkeys == 0) || (h->dupmin >= plan->a))
			continue;
		uint32_t used = (h->dupkeys * 100) / h->keys;
		if (used >= plan->b) {
			if (n->flags & SI_LOCK) {
				rc_inprogress = 2;
				continue;
			}
			goto match;
		}
	}
	if (rc_inprogress)
		plan->explain = SI_ERETRY;
	return rc_inprogress;
match:
	si_nodelock(n);
	plan->explain = SI_ENONE;
	plan->node = n;
	return 1;
}

int si_planner(siplanner *p, siplan *plan)
{
	switch (plan->plan) {
	case SI_BRANCH:
		return si_plannerpeek_branch(p, plan);
	case SI_AGE:
		return si_plannerpeek_age(p, plan);
	case SI_CHECKPOINT:
		return si_plannerpeek_checkpoint(p, plan);
	case SI_COMPACT:
		return si_plannerpeek_compact(p, plan);
	case SI_GC:
		return si_plannerpeek_gc(p, plan);
	case SI_BACKUP:
		return si_plannerpeek_backup(p, plan);
	}
	return -1;
}
#line 1 "sophia/index/si_profiler.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/






int si_profilerbegin(siprofiler *p, si *i)
{
	memset(p, 0, sizeof(*p));
	p->i = i;
	si_lock(i);
	return 0;
}

int si_profilerend(siprofiler *p)
{
	si_unlock(p->i);
	return 0;
}

static void
si_profiler_histogram_branch(siprofiler *p)
{
	/* prepare histogram string */
	int size = 0;
	int i = 0;
	while (i < 20) {
		if (p->histogram_branch[i] == 0) {
			i++;
			continue;
		}
		size += snprintf(p->histogram_branch_sz + size,
		                 sizeof(p->histogram_branch_sz) - size,
		                 "[%d]:%d ", i,
		                 p->histogram_branch[i]);
		i++;
	}
	if (p->histogram_branch_20plus) {
		size += snprintf(p->histogram_branch_sz + size,
		                 sizeof(p->histogram_branch_sz) - size,
		                 "[20+]:%d ",
		                 p->histogram_branch_20plus);
	}
	if (size == 0)
		p->histogram_branch_ptr = NULL;
	else {
		p->histogram_branch_ptr = p->histogram_branch_sz;
	}
}

int si_profiler(siprofiler *p)
{
	uint64_t memory_used = 0;
	srrbnode *pn;
	sinode *n;
	pn = sr_rbmin(&p->i->i);
	while (pn) {
		n = srcast(pn, sinode, node);
		p->total_node_size += n->file.size;
		p->total_node_count++;
		p->count += n->i0.count;
		p->count += n->i1.count;
		p->total_branch_count += n->branch_count;
		if (p->total_branch_max < n->branch_count)
			p->total_branch_max = n->branch_count;
		if (n->branch_count < 20)
			p->histogram_branch[n->branch_count]++;
		else
			p->histogram_branch_20plus++;
		memory_used += sv_indexused(&n->i0);
		memory_used += sv_indexused(&n->i1);
		sibranch *b = n->branch;
		while (b) {
			p->count += b->index.h->keys;
			p->count_dup += b->index.h->dupkeys;
			b = b->next;
		}
		pn = sr_rbnext(&p->i->i, pn);
	}
	if (p->total_node_count > 0)
		p->total_branch_avg =
			p->total_branch_count / p->total_node_count;
	p->memory_used = memory_used;
	p->read_disk  = p->i->read_disk;
	p->read_cache = p->i->read_cache;
	si_profiler_histogram_branch(p);
	return 0;
}
#line 1 "sophia/index/si_query.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/






int si_queryopen(siquery *q, sr *r, sicache *c, si *i, srorder o,
                 uint64_t vlsn,
                 void *key, uint32_t keysize)
{
	q->order   = o;
	q->key     = key;
	q->keysize = keysize;
	q->vlsn    = vlsn;
	q->index   = i;
	q->r       = r;
	q->cache   = c;
	memset(&q->result, 0, sizeof(q->result));
	sv_mergeinit(&q->merge);
	si_lock(q->index);
	return 0;
}

int si_queryclose(siquery *q)
{
	si_unlock(q->index);
	sv_mergefree(&q->merge, q->r->a);
	return 0;
}

static inline int
si_qresult(siquery *q, sriter *i)
{
	sv *v = sr_iterof(i);
	if (srunlikely(v == NULL))
		return 0;
	if (srunlikely(svflags(v) & SVDELETE))
		return 2;
	q->result = *v;
	return 1;
}

static inline int
si_qmatchindex(siquery *q, sinode *node)
{
	sriter i;
	sr_iterinit(&i, &sv_indexiter, q->r);
	int rc = sr_iteropen(&i, &node->i0, q->order, q->key, q->keysize, q->vlsn);
	if (rc)
		return si_qresult(q, &i);
	if (! (node->flags & SI_I1))
		return 0;
	sr_iterinit(&i, &sv_indexiter, q->r);
	rc = sr_iteropen(&i, &node->i1, q->order, q->key, q->keysize, q->vlsn);
	if (rc)
		return si_qresult(q, &i);
	return 0;
}

static inline sdpage*
si_qread(srbuf *buf, sr *r, si *i, sinode *n,
         sibranch *b, sdindexpage *ref)
{
	int size = sizeof(sdpage) + ref->size;
	int rc = sr_bufensure(buf, r->a, size);
	if (srunlikely(rc == -1)) {
		sr_error(r->e, "%s", "memory allocation failed");
		return NULL;
	}
	uint64_t offset =
		b->index.h->offset + sd_indexsize(b->index.h) +
	    ref->offset;
	rc = sr_filepread(&n->file, offset, buf->s + sizeof(sdpage), ref->size);
	if (srunlikely(rc == -1)) {
		sr_error(r->e, "db file '%s' read error: %s",
		         n->file.file, strerror(errno));
		return NULL;
	}
	sr_bufadvance(buf, size);
	i->read_disk++;
	sdpageheader *h = (sdpageheader*)(buf->s + sizeof(sdpage));
	sdpage *page = (sdpage*)(buf->s);
	sd_pageinit(page, h);
	return page;
}

static inline int
si_qmatchbranch(siquery *q, sinode *n, sibranch *b)
{
	sicachebranch *cb = si_cachefollow(q->cache);
	assert(cb->branch == b);
	sriter i;
	sr_iterinit(&i, &sd_indexiter, q->r);
	sr_iteropen(&i, &b->index, SR_LTE, q->key, q->keysize);
	cb->ref = sr_iterof(&i);
	if (cb->ref == NULL)
		return 0;
	sdpage *page = si_qread(&cb->buf, q->r, q->index, n, b, cb->ref);
	if (srunlikely(page == NULL)) {
		cb->ref = NULL;
		return -1;
	}
	sr_iterinit(&cb->i, &sd_pageiter, q->r);
	int rc;
	rc = sr_iteropen(&cb->i, page, q->order, q->key, q->keysize, q->vlsn);
	if (rc == 0) {
		cb->ref = NULL;
		return 0;
	}
	return si_qresult(q, &cb->i);
}

static inline int
si_qmatch(siquery *q)
{
	sriter i;
	sr_iterinit(&i, &si_iter, q->r);
	sr_iteropen(&i, q->index, SR_ROUTE, q->key, q->keysize);
	sinode *node;
	node = sr_iterof(&i);
	assert(node != NULL);
	/* search in memory */
	int rc;
	rc = si_qmatchindex(q, node);
	switch (rc) {
	case  2: rc = 0; /* delete */
	case -1: /* error */
	case  1: return rc;
	}
	/* */
	rc = si_cachevalidate(q->cache, node);
	if (srunlikely(rc == -1)) {
		sr_error(q->r->e, "%s", "memory allocation failed");
		return -1;
	}
	/* search on disk */
	sibranch *b = node->branch;
	while (b) {
		rc = si_qmatchbranch(q, node, b);
		switch (rc) {
		case  2: rc = 0;
		case -1: 
		case  1: return rc;
		}
		b = b->next;
	}
	return 0;
}

int si_querydup(siquery *q, sv *result)
{
	svv *v = sv_valloc(q->r->a, &q->result);
	if (srunlikely(v == NULL)) {
		sr_error(q->r->e, "%s", "memory allocation failed");
		return -1;
	}
	svinit(result, &sv_vif, v, NULL);
	return 1;
}

static inline void
si_qfetchbranch(siquery *q, sinode *n, sibranch *b, svmerge *m)
{
	sicachebranch *cb = si_cachefollow(q->cache);
	assert(cb->branch == b);
	/* cache iteration */
	if (srlikely(cb->ref)) {
		if (sr_iterhas(&cb->i)) {
			svmergesrc *s = sv_mergeadd(m, &cb->i);
			s->ptr = cb;
			q->index->read_cache++;
			return;
		}
	}
	/* read page to cache buffer */
	sriter i;
	sr_iterinit(&i, &sd_indexiter, q->r);
	sr_iteropen(&i, &b->index, q->order, q->key, q->keysize);
	sdindexpage *prev = cb->ref;
	cb->ref = sr_iterof(&i);
	if (cb->ref == NULL || cb->ref == prev)
		return;
	sdpage *page = si_qread(&cb->buf, q->r, q->index, n, b, cb->ref);
	if (srunlikely(page == NULL)) {
		cb->ref = NULL;
		return;
	}
	svmergesrc *s = sv_mergeadd(m, &cb->i);
	s->ptr = cb;
	sr_iterinit(&cb->i, &sd_pageiter, q->r);
	sr_iteropen(&cb->i, page, q->order, q->key, q->keysize, q->vlsn);
}

static inline int
si_qfetch(siquery *q)
{
	sriter i;
	sr_iterinit(&i, &si_iter, q->r);
	sr_iteropen(&i, q->index, q->order, q->key, q->keysize);
	sinode *node;
next_node:
	node = sr_iterof(&i);
	if (srunlikely(node == NULL))
		return 0;

	/* prepare sources */
	svmerge *m = &q->merge;
	int count = node->branch_count + 2;
	int rc = sv_mergeprepare(m, q->r, count);
	if (srunlikely(rc == -1)) {
		sr_errorreset(q->r->e);
		return -1;
	}
	svmergesrc *s;
	s = sv_mergeadd(m, NULL);
	sr_iterinit(&s->src, &sv_indexiter, q->r);
	sr_iteropen(&s->src, &node->i1, q->order, q->key, q->keysize, q->vlsn);
	s = sv_mergeadd(m, NULL);
	sr_iterinit(&s->src, &sv_indexiter, q->r);
	sr_iteropen(&s->src, &node->i0, q->order, q->key, q->keysize, q->vlsn);

	/* */
	rc = si_cachevalidate(q->cache, node);
	if (srunlikely(rc == -1)) {
		sr_error(q->r->e, "%s", "memory allocation failed");
		return -1;
	}
	sibranch *b = node->branch;
	while (b) {
		si_qfetchbranch(q, node, b, m);
		b = b->next;
	}

	/* merge and filter data stream */
	sriter j;
	sr_iterinit(&j, &sv_mergeiter, q->r);
	sr_iteropen(&j, m, q->order);
	sriter k;
	sr_iterinit(&k, &sv_readiter, q->r);
	sr_iteropen(&k, &j, q->vlsn);
	sv *v = sr_iterof(&k);
	if (srunlikely(v == NULL)) {
		sv_mergereset(&q->merge);
		sr_iternext(&i);
		goto next_node;
	}
	q->result = *v;

	/* skip a possible duplicates from data sources */
	sr_iternext(&k);
	return 1;
}

int si_query(siquery *q)
{
	switch (q->order) {
	case SR_EQ:
	case SR_UPDATE:
		return si_qmatch(q);
	case SR_RANDOM:
	case SR_LT:
	case SR_LTE:
	case SR_GT:
	case SR_GTE:
		return si_qfetch(q);
	default:
		break;
	}
	return -1;
}

static int
si_querycommited_branch(sr *r, sibranch *b, sv *v)
{
	sriter i;
	sr_iterinit(&i, &sd_indexiter, r);
	sr_iteropen(&i, &b->index, SR_LTE, svkey(v), svkeysize(v));
	sdindexpage *page = sr_iterof(&i);
	if (page == NULL)
		return 0;
	return page->lsnmax >= svlsn(v);
}

int si_querycommited(si *index, sr *r, sv *v)
{
	sriter i;
	sr_iterinit(&i, &si_iter, r);
	sr_iteropen(&i, index, SR_ROUTE, svkey(v), svkeysize(v));
	sinode *node;
	node = sr_iterof(&i);
	assert(node != NULL);
	sibranch *b = node->branch;
	int rc;
	while (b) {
		rc = si_querycommited_branch(r, b, v);
		if (rc)
			return 1;
		b = b->next;
	}
	rc = si_querycommited_branch(r, &node->self, v);
	return rc;
}
#line 1 "sophia/index/si_recover.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

/*
	repository recover states
	-------------------------

	compaction

	000000001.000000002.db.incomplete  (1)
	000000001.000000002.db.seal        (2)
	000000002.db                       (3)
	000000001.000000003.db.incomplete
	000000001.000000003.db.seal
	000000003.db
	(4)

	1. remove incomplete, mark parent as having incomplete
	2. find parent, mark as having seal
	3. add
	4. recover:
		a. if parent has incomplete and seal - remove both
		b. if parent has incomplete - remove incomplete
		c. if parent has seal - remove parent, complete seal

	see: test/recovery_crash.test.c
*/






sinode *si_bootstrap(si *i, sr *r, uint32_t parent)
{
	sinode *n = si_nodenew(r);
	if (srunlikely(n == NULL))
		return NULL;
	sdid id = {
		.parent = parent,
		.flags  = 0,
		.id     = sr_seq(r->seq, SR_NSNNEXT)
	};
	sdindex index;
	sd_indexinit(&index);
	int rc = sd_indexbegin(&index, r, 0, 0);
	if (srunlikely(rc == -1)) {
		si_nodefree(n, r, 0);
		return NULL;
	}
	sdbuild build;
	sd_buildinit(&build, r);
	rc = sd_buildbegin(&build);
	if (srunlikely(rc == -1)) {
		sd_indexfree(&index, r);
		sd_buildfree(&build);
		si_nodefree(n, r, 0);
		return NULL;
	}
	sd_buildend(&build);
	sdpageheader *h = sd_buildheader(&build);
	rc = sd_indexadd(&index, r,
	                 sd_buildoffset(&build),
	                 h->size + sizeof(sdpageheader),
	                 h->count,
	                 NULL,
	                 0,
	                 NULL,
                     0,
                     0, UINT64_MAX,
                     UINT64_MAX, 0);
	if (srunlikely(rc == -1)) {
		sd_indexfree(&index, r);
		si_nodefree(n, r, 0);
		return NULL;
	}
	sd_buildcommit(&build);
	sd_indexcommit(&index, &id);
	rc = si_nodecreate(n, r, i->conf, &id, &index, &build);
	sd_buildfree(&build);
	if (srunlikely(rc == -1)) {
		si_nodefree(n, r, 1);
		return NULL;
	}
	return n;
}

static inline int
si_deploy(si *i, sr *r)
{
	int rc = sr_filemkdir(i->conf->path);
	if (srunlikely(rc == -1)) {
		sr_malfunction(r->e, "directory '%s' create error: %s",
		               i->conf->path, strerror(errno));
		return -1;
	}
	sinode *n = si_bootstrap(i, r, 0);
	if (srunlikely(n == NULL))
		return -1;
	SR_INJECTION(r->i, SR_INJECTION_SI_RECOVER_0,
	             si_nodefree(n, r, 0);
	             sr_malfunction(r->e, "%s", "error injection");
	             return -1);
	rc = si_nodecomplete(n, r, i->conf);
	if (srunlikely(rc == -1)) {
		si_nodefree(n, r, 1);
		return -1;
	}
	si_insert(i, r, n);
	si_plannerupdate(&i->p, SI_COMPACT|SI_BRANCH, n);
	return 1;
}

static inline ssize_t
si_processid(char **str) {
	char *s = *str;
	size_t v = 0;
	while (*s && *s != '.') {
		if (srunlikely(!isdigit(*s)))
			return -1;
		v = (v * 10) + *s - '0';
		s++;
	}
	*str = s;
	return v;
}

static inline int
si_process(char *name, uint32_t *nsn, uint32_t *parent)
{
	/* id.db */
	/* id.id.db.incomplete */
	/* id.id.db.seal */
	char *token = name;
	ssize_t id = si_processid(&token);
	if (srunlikely(id == -1))
		return -1;
	*parent = id;
	*nsn = id;
	if (strcmp(token, ".db") == 0)
		return SI_RDB;
	if (srunlikely(*token != '.'))
		return -1;
	token++;
	id = si_processid(&token);
	if (srunlikely(id == -1))
		return -1;
	*nsn = id;
	if (strcmp(token, ".db.incomplete") == 0)
		return SI_RDB_DBI;
	else
	if (strcmp(token, ".db.seal") == 0)
		return SI_RDB_DBSEAL;
	return -1;
}

static inline int
si_trackdir(sitrack *track, sr *r, si *i)
{
	DIR *dir = opendir(i->conf->path);
	if (srunlikely(dir == NULL)) {
		sr_malfunction(r->e, "directory '%s' open error: %s",
		               i->conf->path, strerror(errno));
		return -1;
	}
	struct dirent *de;
	while ((de = readdir(dir))) {
		if (srunlikely(de->d_name[0] == '.'))
			continue;
		uint32_t id_parent = 0;
		uint32_t id = 0;
		int rc = si_process(de->d_name, &id, &id_parent);
		if (srunlikely(rc == -1))
			continue; /* skip unknown file */
		si_tracknsn(track, id_parent);
		si_tracknsn(track, id);

		sinode *head, *node;
		srpath path;
		switch (rc) {
		case SI_RDB_DBI:
		case SI_RDB_DBSEAL: {
			/* find parent node and mark it as having
			 * incomplete compaction process */
			head = si_trackget(track, id_parent);
			if (srlikely(head == NULL)) {
				head = si_nodenew(r);
				if (srunlikely(head == NULL))
					goto error;
				head->self.id.id = id_parent;
				head->recover = SI_RDB_UNDEF;
				si_trackset(track, head);
			}
			head->recover |= rc;
			/* remove any incomplete file made during compaction */
			if (rc == SI_RDB_DBI) {
				sr_pathAB(&path, i->conf->path, id_parent, id, ".db.incomplete");
				rc = sr_fileunlink(path.path);
				if (srunlikely(rc == -1)) {
					sr_malfunction(r->e, "db file '%s' unlink error: %s",
					               path.path, strerror(errno));
					goto error;
				}
				continue;
			}
			assert(rc == SI_RDB_DBSEAL);
			/* recover 'sealed' node */
			node = si_nodenew(r);
			if (srunlikely(node == NULL))
				goto error;
			node->recover = SI_RDB_DBSEAL;
			sr_pathAB(&path, i->conf->path, id_parent, id, ".db.seal");
			rc = si_nodeopen(node, r, &path);
			if (srunlikely(rc == -1)) {
				si_nodefree(node, r, 0);
				goto error;
			}
			si_trackset(track, node);
			si_trackmetrics(track, node);
			continue;
		}
		}
		assert(rc == SI_RDB);

		/* recover node */
		node = si_nodenew(r);
		if (srunlikely(node == NULL))
			goto error;
		node->recover = SI_RDB;
		sr_pathA(&path, i->conf->path, id, ".db");
		rc = si_nodeopen(node, r, &path);
		if (srunlikely(rc == -1)) {
			si_nodefree(node, r, 0);
			goto error;
		}
		si_trackmetrics(track, node);

		/* track node */
		head = si_trackget(track, id);
		if (srlikely(head == NULL)) {
			si_trackset(track, node);
		} else {
			/* replace a node previously created by a
			 * incomplete compaction. */
			if (! (head->recover & SI_RDB_UNDEF)) {
				sr_malfunction(r->e, "corrupted database repository: %s",
				               i->conf->path);
				goto error;
			}
			si_trackreplace(track, head, node);
			head->recover &= ~SI_RDB_UNDEF;
			node->recover |= head->recover;
			si_nodefree(head, r, 0);
		}
	}
	closedir(dir);
	return 0;
error:
	closedir(dir);
	return -1;
}

static inline int
si_trackvalidate(sitrack *track, srbuf *buf, sr *r, si *i)
{
	sr_bufreset(buf);
	srrbnode *p = sr_rbmax(&track->i);
	while (p) {
		sinode *n = srcast(p, sinode, node);
		switch (n->recover) {
		case SI_RDB|SI_RDB_DBI|SI_RDB_DBSEAL|SI_RDB_REMOVE:
		case SI_RDB|SI_RDB_DBSEAL|SI_RDB_REMOVE:
		case SI_RDB|SI_RDB_REMOVE:
		case SI_RDB_UNDEF|SI_RDB_DBSEAL|SI_RDB_REMOVE:
		case SI_RDB|SI_RDB_DBI|SI_RDB_DBSEAL:
		case SI_RDB|SI_RDB_DBI:
		case SI_RDB:
		case SI_RDB|SI_RDB_DBSEAL:
		case SI_RDB_UNDEF|SI_RDB_DBSEAL: {
			/* match and remove any leftover ancestor */
			sinode *ancestor = si_trackget(track, n->self.id.parent);
			if (ancestor && (ancestor != n))
				ancestor->recover |= SI_RDB_REMOVE;
			break;
		}
		case SI_RDB_DBSEAL: {
			/* find parent */
			sinode *parent = si_trackget(track, n->self.id.parent);
			if (parent) {
				/* schedule node for removal, if has incomplete merges */
				if (parent->recover & SI_RDB_DBI)
					n->recover |= SI_RDB_REMOVE;
				else
					parent->recover |= SI_RDB_REMOVE;
			}
			if (! (n->recover & SI_RDB_REMOVE)) {
				/* complete node */
				int rc = si_nodecomplete(n, r, i->conf);
				if (srunlikely(rc == -1))
					return -1;
				n->recover = SI_RDB;
			}
			break;
		}
		default:
			/* corrupted states */
			return sr_malfunction(r->e, "corrupted database repository: %s",
			                      i->conf->path);
		}
		p = sr_rbprev(&track->i, p);
	}
	return 0;
}

static inline int
si_recovercomplete(sitrack *track, sr *r, si *index, srbuf *buf)
{
	/* prepare and build primary index */
	sr_bufreset(buf);
	srrbnode *p = sr_rbmin(&track->i);
	while (p) {
		sinode *n = srcast(p, sinode, node);
		int rc = sr_bufadd(buf, r->a, &n, sizeof(sinode**));
		if (srunlikely(rc == -1))
			return sr_malfunction(r->e, "%s", "memory allocation failed");
		p = sr_rbnext(&track->i, p);
	}
	sriter i;
	sr_iterinit(&i, &sr_bufiterref, r);
	sr_iteropen(&i, buf, sizeof(sinode*));
	for (; sr_iterhas(&i); sr_iternext(&i)) {
		sinode *n = sr_iterof(&i);
		if (n->recover & SI_RDB_REMOVE) {
			int rc = si_nodefree(n, r, 1);
			if (srunlikely(rc == -1))
				return -1;
			continue;
		}
		n->recover = SI_RDB;
		si_insert(index, r, n);
		si_plannerupdate(&index->p, SI_COMPACT|SI_BRANCH, n);
	}
	return 0;
}

static inline int
si_recoverindex(si *i, sr *r)
{
	sitrack track;
	si_trackinit(&track);
	srbuf buf;
	sr_bufinit(&buf);
	int rc = si_trackdir(&track, r, i);
	if (srunlikely(rc == -1))
		goto error;
	if (srunlikely(track.count == 0)) {
		sr_malfunction(r->e, "corrupted database repository: %s",
		               i->conf->path);
		goto error;
	}
	rc = si_trackvalidate(&track, &buf, r, i);
	if (srunlikely(rc == -1))
		goto error;
	rc = si_recovercomplete(&track, r, i, &buf);
	if (srunlikely(rc == -1))
		goto error;
	/* set actual metrics */
	if (track.nsn > r->seq->nsn)
		r->seq->nsn = track.nsn;
	if (track.lsn > r->seq->lsn)
		r->seq->lsn = track.lsn;
	sr_buffree(&buf, r->a);
	return 0;
error:
	sr_buffree(&buf, r->a);
	si_trackfree(&track, r);
	return -1;
}

int si_recover(si *i, sr *r)
{
	int exist = sr_fileexists(i->conf->path);
	if (exist == 0)
		return si_deploy(i, r);
	return si_recoverindex(i, r);
}
#line 1 "sophia/repository/se_conf.h"
#ifndef SE_CONF_H_
#define SE_CONF_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct seconf seconf;

struct seconf {
	char *path;
	int   path_create;
	char *path_backup;
	int   sync;
};

#endif
#line 1 "sophia/repository/se.h"
#ifndef SE_H_
#define SE_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct se se;

struct se {
	seconf *conf;
};

int se_init(se*);
int se_open(se*, sr*, seconf*);
int se_close(se*, sr*);

#endif
#line 1 "sophia/repository/se.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/






int se_init(se *e)
{
	e->conf = NULL;
	return 0;
}

static int
se_deploy(se *e, sr *r)
{
	int rc;
	rc = sr_filemkdir(e->conf->path);
	if (srunlikely(rc == -1)) {
		sr_error(r->e, "directory '%s' create error: %s",
		         e->conf->path, strerror(errno));
		return -1;
	}
	return 0;
}

static inline int
se_recover(se *e, sr *r)
{
	(void)e;
	(void)r;
	return 0;
}

static inline ssize_t
se_processid(char **str) {
	char *s = *str;
	size_t v = 0;
	while (*s && *s != '.') {
		if (srunlikely(!isdigit(*s)))
			return -1;
		v = (v * 10) + *s - '0';
		s++;
	}
	*str = s;
	return v;
}

static inline int
se_process(char *name, uint32_t *bsn)
{
	/* id */
	/* id.incomplete */
	char *token = name;
	ssize_t id = se_processid(&token);
	if (srunlikely(id == -1))
		return -1;
	*bsn = id;
	if (strcmp(token, ".incomplete") == 0)
		return 1;
	return 0;
}

static inline int
se_recoverbackup(se *i, sr *r)
{
	if (i->conf->path_backup == NULL)
		return 0;
	int rc;
	int exists = sr_fileexists(i->conf->path_backup);
	if (! exists) {
		rc = sr_filemkdir(i->conf->path_backup);
		if (srunlikely(rc == -1)) {
			sr_error(r->e, "backup directory '%s' create error: %s",
					 i->conf->path_backup, strerror(errno));
			return -1;
		}
	}
	/* recover backup sequential number */
	DIR *dir = opendir(i->conf->path_backup);
	if (srunlikely(dir == NULL)) {
		sr_error(r->e, "backup directory '%s' open error: %s",
				 i->conf->path_backup, strerror(errno));
		return -1;
	}
	uint32_t bsn = 0;
	struct dirent *de;
	while ((de = readdir(dir))) {
		if (srunlikely(de->d_name[0] == '.'))
			continue;
		uint32_t id = 0;
		rc = se_process(de->d_name, &id);
		switch (rc) {
		case  1:
		case  0:
			if (id > bsn)
				bsn = id;
			break;
		case -1: /* skip unknown file */
			continue;
		}
	}
	closedir(dir);
	r->seq->bsn = bsn;
	return 0;
}

int se_open(se *e, sr *r, seconf *conf)
{
	e->conf = conf;
	int rc = se_recoverbackup(e, r);
	if (srunlikely(rc == -1))
		return -1;
	int exists = sr_fileexists(conf->path);
	if (exists == 0) {
		if (srunlikely(! conf->path_create)) {
			sr_error(r->e, "directory '%s' does not exist", conf->path);
			return -1;
		}
		return se_deploy(e, r);
	}
	return se_recover(e, r);
}

int se_close(se *e, sr *r)
{
	(void)e;
	(void)r;
	return 0;
}
#line 1 "sophia/sophia/so_status.h"
#ifndef SO_STATUS_H_
#define SO_STATUS_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

enum {
	SO_OFFLINE,
	SO_ONLINE,
	SO_RECOVER,
	SO_SHUTDOWN,
	SO_MALFUNCTION
};

typedef struct sostatus sostatus;

struct sostatus {
	int status;
	srspinlock lock;
};

static inline void
so_statusinit(sostatus *s)
{
	s->status = SO_OFFLINE;
	sr_spinlockinit(&s->lock);
}

static inline void
so_statusfree(sostatus *s)
{
	sr_spinlockfree(&s->lock);
}

static inline void
so_statuslock(sostatus *s) {
	sr_spinlock(&s->lock);
}

static inline void
so_statusunlock(sostatus *s) {
	sr_spinunlock(&s->lock);
}

static inline int
so_statusset(sostatus *s, int status)
{
	sr_spinlock(&s->lock);
	int old = s->status;
	if (old == SO_MALFUNCTION) {
		sr_spinunlock(&s->lock);
		return -1;
	}
	s->status = status;
	sr_spinunlock(&s->lock);
	return old;
}

static inline int
so_status(sostatus *s)
{
	sr_spinlock(&s->lock);
	int status = s->status;
	sr_spinunlock(&s->lock);
	return status;
}

static inline char*
so_statusof(sostatus *s)
{
	int status = so_status(s);
	switch (status) {
	case SO_OFFLINE:     return "offline";
	case SO_ONLINE:      return "online";
	case SO_RECOVER:     return "recover";
	case SO_SHUTDOWN:    return "shutdown";
	case SO_MALFUNCTION: return "malfunction";
	}
	assert(0);
	return NULL;
}

static inline int
so_statusactive_is(int status) {
	switch (status) {
	case SO_ONLINE:
	case SO_RECOVER:
		return 1;
	case SO_OFFLINE:
	case SO_SHUTDOWN:
	case SO_MALFUNCTION:
		return 0;
	}
	assert(0);
	return 0;
}

static inline int
so_statusactive(sostatus *s) {
	return so_statusactive_is(so_status(s));
}

#endif
#line 1 "sophia/sophia/so_worker.h"
#ifndef SO_WORKER_H_
#define SO_WORKER_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct soworker soworker;
typedef struct soworkers soworkers;

struct soworker {
	srthread t;
	char name[16];
	srtrace trace;
	void *arg;
	sdc dc;
	srlist link;
};

struct soworkers {
	srlist list;
	int n;
};

int so_workersinit(soworkers*);
int so_workersshutdown(soworkers*, sr*);
int so_workersnew(soworkers*, sr*, int, srthreadf, void*);

static inline void
so_workerstub_init(soworker *w, sr *r)
{
	sd_cinit(&w->dc, r);
	sr_listinit(&w->link);
	sr_traceinit(&w->trace);
	sr_trace(&w->trace, "%s", "init");
}

static inline void
so_workerstub_free(soworker *w, sr *r)
{
	sd_cfree(&w->dc, r);
	sr_tracefree(&w->trace);
}

#endif
#line 1 "sophia/sophia/so_obj.h"
#ifndef SO_OBJ_H_
#define SO_OBJ_H_

/*
 * sophia database
 * sehia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef enum {
	SOUNDEF      = 0L,
	SOENV        = 0x06154834L,
	SOCTL        = 0x1234FFBBL,
	SOCTLCURSOR  = 0x6AB65429L,
	SOV          = 0x2FABCDE2L,
	SODB         = 0x34591111L,
	SOTX         = 0x13491FABL,
	SOLOGCURSOR  = 0x19315400L,
	SOCURSOR     = 0x45ABCDFAL,
	SOSNAPSHOT   = 0x71230BAFL
} soobjid;

static inline soobjid
so_objof(void *ptr) {
	return *(soobjid*)ptr;
}

typedef struct soobjif soobjif;
typedef struct soobj soobj;

struct soobjif {
	void *(*ctl)(soobj*, va_list);
	int   (*open)(soobj*, va_list);
	int   (*error)(soobj*, va_list);
	int   (*destroy)(soobj*, va_list);
	int   (*set)(soobj*, va_list);
	void *(*get)(soobj*, va_list);
	int   (*del)(soobj*, va_list);
	int   (*drop)(soobj*, va_list);
	void *(*begin)(soobj*, va_list);
	int   (*prepare)(soobj*, va_list);
	int   (*commit)(soobj*, va_list);
	void *(*cursor)(soobj*, va_list);
	void *(*object)(soobj*, va_list);
	void *(*type)(soobj*, va_list);
};

struct soobj {
	soobjid  id;
	soobjif *i;
	soobj *env;
	srlist link;
};

static inline void
so_objinit(soobj *o, soobjid id, soobjif *i, soobj *env)
{
	o->id  = id;
	o->i   = i;
	o->env = env;
	sr_listinit(&o->link);
}

static inline int
so_objopen(soobj *o, ...)
{
	va_list args;
	va_start(args, o);
	int rc = o->i->open(o, args);
	va_end(args);
	return rc;
}

static inline int
so_objdestroy(soobj *o, ...) {
	va_list args;
	va_start(args, o);
	int rc = o->i->destroy(o, args);
	va_end(args);
	return rc;
}

static inline int
so_objerror(soobj *o, ...)
{
	va_list args;
	va_start(args, o);
	int rc = o->i->error(o, args);
	va_end(args);
	return rc;
}

static inline void*
so_objobject(soobj *o, ...)
{
	va_list args;
	va_start(args, o);
	void *h = o->i->object(o, args);
	va_end(args);
	return h;
}

static inline int
so_objset(soobj *o, ...)
{
	va_list args;
	va_start(args, o);
	int rc = o->i->set(o, args);
	va_end(args);
	return rc;
}

static inline void*
so_objget(soobj *o, ...)
{
	va_list args;
	va_start(args, o);
	void *h = o->i->get(o, args);
	va_end(args);
	return h;
}

static inline int
so_objdelete(soobj *o, ...)
{
	va_list args;
	va_start(args, o);
	int rc = o->i->del(o, args);
	va_end(args);
	return rc;
}

static inline void*
so_objbegin(soobj *o, ...) {
	va_list args;
	va_start(args, o);
	void *h = o->i->begin(o, args);
	va_end(args);
	return h;
}

static inline int
so_objprepare(soobj *o, ...)
{
	va_list args;
	va_start(args, o);
	int rc = o->i->prepare(o, args);
	va_end(args);
	return rc;
}

static inline int
so_objcommit(soobj *o, ...)
{
	va_list args;
	va_start(args, o);
	int rc = o->i->commit(o, args);
	va_end(args);
	return rc;
}

static inline void*
so_objcursor(soobj *o, ...) {
	va_list args;
	va_start(args, o);
	void *h = o->i->cursor(o, args);
	va_end(args);
	return h;
}

#endif
#line 1 "sophia/sophia/so_objindex.h"
#ifndef SO_OBJINDEX_H_
#define SO_OBJINDEX_H_

/*
 * sophia database
 * sehia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct soobjindex soobjindex;

struct soobjindex {
	srlist list;
	int n;
};

static inline void
so_objindex_init(soobjindex *i)
{
	sr_listinit(&i->list);
	i->n = 0;
}

static inline int
so_objindex_destroy(soobjindex *i)
{
	int rcret = 0;
	int rc;
	srlist *p, *n;
	sr_listforeach_safe(&i->list, p, n) {
		soobj *o = srcast(p, soobj, link);
		rc = so_objdestroy(o);
		if (srunlikely(rc == -1))
			rcret = -1;
	}
	i->n = 0;
	sr_listinit(&i->list);
	return rcret;
}

static inline void
so_objindex_register(soobjindex *i, soobj *o)
{
	sr_listappend(&i->list, &o->link);
	i->n++;
}

static inline void
so_objindex_unregister(soobjindex *i, soobj *o)
{
	sr_listunlink(&o->link);
	i->n--;
}

#endif
#line 1 "sophia/sophia/so_ctlcursor.h"
#ifndef SO_CTLCURSOR_H_
#define SO_CTLCURSOR_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct soctlcursor soctlcursor;

struct soctlcursor {
	soobj o;
	int ready;
	srbuf dump;
	srcv *pos;
	soobj *v;
} srpacked;

soobj *so_ctlcursor_new(void*);

#endif
#line 1 "sophia/sophia/so_ctl.h"
#ifndef SO_CTL_H_
#define SO_CTL_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct soctlrt soctlrt;
typedef struct soctl soctl;

struct soctlrt {
	/* sophia */
	char      version[16];
	/* memory */
	uint64_t  memory_used;
	/* scheduler */
	char      zone[4];
	uint32_t  checkpoint_active;
	uint64_t  checkpoint_lsn;
	uint64_t  checkpoint_lsn_last;
	uint32_t  backup_active;
	uint32_t  backup_last;
	uint32_t  backup_last_complete;
	uint32_t  gc_active;
	/* log */
	uint32_t  log_files;
	/* metric */
	srseq     seq;
};

struct soctl {
	soobj o;
	/* sophia */
	char      *path;
	uint32_t   path_create;
	/* backup */
	char      *backup_path;
	srtrigger  backup_on_complete;
	/* compaction */
	uint32_t   node_size;
	uint32_t   page_size;
	sizonemap  zones;
	/* scheduler */
	uint32_t   threads;
	srtrigger  checkpoint_on_complete;
	/* memory */
	uint64_t   memory_limit;
	/* log */
	uint32_t   log_enable;
	char      *log_path;
	uint32_t   log_sync;
	uint32_t   log_rotate_wm;
	uint32_t   log_rotate_sync;
	uint32_t   two_phase_recover;
	uint32_t   commit_lsn;
};

void  so_ctlinit(soctl*, void*);
void  so_ctlfree(soctl*);
int   so_ctlvalidate(soctl*);
int   so_ctlserialize(soctl*, srbuf*);
void *so_ctlreturn(src*, void*);

#endif
#line 1 "sophia/sophia/so_scheduler.h"
#ifndef SO_SCHEDULER_H_
#define SO_SCHEDULER_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct soscheduler soscheduler;
typedef struct sotask sotask;

struct sotask {
	siplan plan;
	int rotate;
	int gc;
	int checkpoint_complete;
	int backup_complete;
	void *db;
};

struct soscheduler {
	soworkers workers;
	srmutex lock;
	uint64_t checkpoint_lsn_last;
	uint64_t checkpoint_lsn;
	uint32_t checkpoint;
	uint32_t age;
	uint32_t age_last;
	uint32_t backup_bsn;
	uint32_t backup_last;
	uint32_t backup_last_complete;
	uint32_t backup;
	uint32_t gc;
	uint32_t gc_last;
	uint32_t workers_backup;
	uint32_t workers_branch;
	uint32_t workers_gc;
	int rotate;
	int rr;
	void **i;
	int count;
	void *env;
};

int so_scheduler_init(soscheduler*, void*);
int so_scheduler_run(soscheduler*);
int so_scheduler_shutdown(soscheduler*);
int so_scheduler_add(soscheduler*, void*);
int so_scheduler_del(soscheduler*, void*);
int so_scheduler(soscheduler*, soworker*);

int so_scheduler_branch(void*);
int so_scheduler_compact(void*);
int so_scheduler_checkpoint(void*);
int so_scheduler_gc(void*);
int so_scheduler_backup(void*);
int so_scheduler_call(void*);

#endif
#line 1 "sophia/sophia/so.h"
#ifndef SO_H_
#define SO_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct so so;

struct so {
	soobj o;
	srmutex apilock;
	soobjindex db;
	soobjindex tx;
	soobjindex snapshot;
	soobjindex ctlcursor;
	sostatus status;
	soctl ctl;
	srseq seq;
	srquota quota;
	srpager pager;
	sra a;
	sra a_db;
	sra a_v;
	sra a_cursor;
	sra a_cursorcache;
	sra a_ctlcursor;
	sra a_snapshot;
	sra a_tx;
	sra a_sxv;
	seconf seconf;
	se se;
	slconf lpconf;
	slpool lp;
	sxmanager xm;
	soscheduler sched;
	srinjection ei;
	srerror error;
	sr r;
};

static inline int
so_active(so *o) {
	return so_statusactive(&o->status);
}

static inline void
so_apilock(soobj *o) {
	sr_mutexlock(&((so*)o)->apilock);
}

static inline void
so_apiunlock(soobj *o) {
	sr_mutexunlock(&((so*)o)->apilock);
}

static inline so*
so_of(soobj *o) {
	return (so*)o->env;
}

soobj *so_new(void);

#endif
#line 1 "sophia/sophia/so_v.h"
#ifndef SO_V_H_
#define SO_V_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sov sov;

#define SO_VALLOCATED 1
#define SO_VRO        2
#define SO_VIMMUTABLE 4

struct sov {
	soobj o;
	uint8_t flags;
	svlocal lv;
	sv v;
	srorder order;
	void *log;
	soobj *parent;
} srpacked;

static inline int
so_vhas(sov *v) {
	return v->v.v != NULL;
}

soobj *so_vnew(so*, soobj*);
soobj *so_vdup(so*, soobj*, sv*);
soobj *so_vinit(sov*, so*, soobj*);
soobj *so_vrelease(sov*);
soobj *so_vput(sov*, sv*);
int    so_vimmutable(sov*);

#endif
#line 1 "sophia/sophia/so_db.h"
#ifndef SO_DB_H_
#define SO_DB_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sodbctl sodbctl;
typedef struct sodb sodb;

struct sodbctl {
	void         *parent;
	char         *name;
	uint32_t      id;
	srcomparator  cmp;
	char         *path;
	uint32_t      created;
	uint32_t      sync;
	siprofiler    rtp;
} srpacked;

struct sodb {
	soobj o;
	sostatus status;
	sodbctl ctl;
	soobjindex cursor;
	sxindex coindex;
	sdc dc;
	siconf indexconf;
	si index;
	sr r;
} srpacked;

static inline int
so_dbactive(sodb *o) {
	return so_statusactive(&o->status);
}

soobj *so_dbnew(so*, char*);
soobj *so_dbmatch(so*, char*);
soobj *so_dbmatch_id(so*, uint32_t);
int    so_dbmalfunction(sodb *o);

#endif
#line 1 "sophia/sophia/so_recover.h"
#ifndef SO_RECOVER_H_
#define SO_RECOVER_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

int so_recoverbegin(sodb*);
int so_recoverend(sodb*);
int so_recover(so*);
int so_recover_repository(so*);

#endif
#line 1 "sophia/sophia/so_tx.h"
#ifndef SO_TX_H_
#define SO_TX_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sotx sotx;

struct sotx {
	soobj o;
	sx t;
} srpacked;

int    so_txdbset(sodb*, uint8_t, va_list);
void  *so_txdbget(sodb*, uint64_t, va_list);
soobj *so_txnew(so*);

#endif
#line 1 "sophia/sophia/so_cursor.h"
#ifndef SO_CURSOR_H_
#define SO_CURSOR_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct socursor socursor;

struct socursor {
	soobj o;
	int ready;
	srorder order;
	sx t;
	sicache cache;
	sov v;
	soobj *key;
	sodb *db;
} srpacked;

soobj *so_cursornew(sodb*, uint64_t, va_list);

#endif
#line 1 "sophia/sophia/so_snapshot.h"
#ifndef SO_SNAPSHOT_H_
#define SO_SNAPSHOT_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sosnapshot sosnapshot;

struct sosnapshot {
	soobj o;
	sx t;
	uint64_t vlsn;
	char *name;
} srpacked;

soobj *so_snapshotnew(so*, uint64_t, char*);
int    so_snapshotupdate(sosnapshot*);

#endif
#line 1 "sophia/sophia/sophia.h"
#ifndef SOPHIA_H_
#define SOPHIA_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

#ifdef __cplusplus
extern "C" {
#endif

#include <stdlib.h>
#include <stdint.h>

#if __GNUC__ >= 4
#  define SP_API __attribute__((visibility("default")))
#else
#  define SP_API
#endif

SP_API void *sp_env(void);
SP_API void *sp_ctl(void*, ...);
SP_API void *sp_object(void*, ...);
SP_API int   sp_open(void*, ...);
SP_API int   sp_destroy(void*, ...);
SP_API int   sp_error(void*, ...);
SP_API int   sp_set(void*, ...);
SP_API void *sp_get(void*, ...);
SP_API int   sp_delete(void*, ...);
SP_API int   sp_drop(void*, ...);
SP_API void *sp_begin(void*, ...);
SP_API int   sp_prepare(void*, ...);
SP_API int   sp_commit(void*, ...);
SP_API void *sp_cursor(void*, ...);
SP_API void *sp_type(void*, ...);

#ifdef __cplusplus
}
#endif

#endif
#line 1 "sophia/sophia/so.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/










static void*
so_ctl(soobj *obj, va_list args srunused)
{
	so *o = (so*)obj;
	return &o->ctl;
}

static int
so_open(soobj *o, va_list args)
{
	so *e = (so*)o;
	int status = so_status(&e->status);
	if (status == SO_RECOVER) {
		assert(e->ctl.two_phase_recover == 1);
		goto online;
	}
	if (status != SO_OFFLINE)
		return -1;
	int rc;
	rc = so_ctlvalidate(&e->ctl);
	if (srunlikely(rc == -1))
		return -1;
	so_statusset(&e->status, SO_RECOVER);

	/* set memory quota (disable during recovery) */
	sr_quotaset(&e->quota, e->ctl.memory_limit);
	sr_quotaenable(&e->quota, 0);

	/* repository recover */
	rc = so_recover_repository(e);
	if (srunlikely(rc == -1))
		return -1;
	/* databases recover */
	srlist *i, *n;
	sr_listforeach_safe(&e->db.list, i, n) {
		soobj *o = srcast(i, soobj, link);
		rc = o->i->open(o, args);
		if (srunlikely(rc == -1))
			return -1;
	}
	/* recover logpool */
	rc = so_recover(e);
	if (srunlikely(rc == -1))
		return -1;
	if (e->ctl.two_phase_recover)
		return 0;

online:
	/* complete */
	sr_listforeach_safe(&e->db.list, i, n) {
		soobj *o = srcast(i, soobj, link);
		rc = o->i->open(o, args);
		if (srunlikely(rc == -1))
			return -1;
	}
	/* enable quota */
	sr_quotaenable(&e->quota, 1);
	so_statusset(&e->status, SO_ONLINE);
	/* run thread-pool and scheduler */
	rc = so_scheduler_run(&e->sched);
	if (srunlikely(rc == -1))
		return -1;
	return 0;
}

static int
so_destroy(soobj *o, va_list args srunused)
{
	so *e = (so*)o;
	int rcret = 0;
	int rc;
	so_statusset(&e->status, SO_SHUTDOWN);
	rc = so_scheduler_shutdown(&e->sched);
	if (srunlikely(rc == -1))
		rcret = -1;
	rc = so_objindex_destroy(&e->tx);
	if (srunlikely(rc == -1))
		rcret = -1;
	rc = so_objindex_destroy(&e->snapshot);
	if (srunlikely(rc == -1))
		rcret = -1;
	rc = so_objindex_destroy(&e->ctlcursor);
	if (srunlikely(rc == -1))
		rcret = -1;
	rc = so_objindex_destroy(&e->db);
	if (srunlikely(rc == -1))
		rcret = -1;
	rc = sl_poolshutdown(&e->lp);
	if (srunlikely(rc == -1))
		rcret = -1;
	rc = se_close(&e->se, &e->r);
	if (srunlikely(rc == -1))
		rcret = -1;
	sx_free(&e->xm);
	so_ctlfree(&e->ctl);
	sr_quotafree(&e->quota);
	sr_mutexfree(&e->apilock);
	sr_seqfree(&e->seq);
	sr_pagerfree(&e->pager);
	so_statusfree(&e->status);
	free(e);
	return rcret;
}

static void*
so_begin(soobj *o, va_list args srunused) {
	return so_txnew((so*)o);
}

static int
so_error(soobj *o, va_list args srunused)
{
	so *e = (so*)o;
	int status = sr_errorof(&e->error);
	if (status == SR_ERROR_MALFUNCTION)
		return 1;
	status = so_status(&e->status);
	if (status == SO_MALFUNCTION)
		return 1;
	return 0;
}

static void*
so_type(soobj *o srunused, va_list args srunused) {
	return "env";
}

static soobjif soif =
{
	.ctl      = so_ctl,
	.open     = so_open,
	.destroy  = so_destroy,
	.error    = so_error,
	.set      = NULL,
	.get      = NULL,
	.del      = NULL,
	.drop     = NULL,
	.begin    = so_begin,
	.prepare  = NULL,
	.commit   = NULL,
	.cursor   = NULL,
	.object   = NULL,
	.type     = so_type
};

soobj *so_new(void)
{
	so *e = malloc(sizeof(*e));
	if (srunlikely(e == NULL))
		return NULL;
	memset(e, 0, sizeof(*e));
	so_objinit(&e->o, SOENV, &soif, &e->o /* self */);
	sr_pagerinit(&e->pager, 10, 4096);
	int rc = sr_pageradd(&e->pager);
	if (srunlikely(rc == -1)) {
		free(e);
		return NULL;
	}
	sr_allocopen(&e->a, &sr_astd);
	sr_allocopen(&e->a_db, &sr_aslab, &e->pager, sizeof(sodb));
	sr_allocopen(&e->a_v, &sr_aslab, &e->pager, sizeof(sov));
	sr_allocopen(&e->a_cursor, &sr_aslab, &e->pager, sizeof(socursor));
	sr_allocopen(&e->a_cursorcache, &sr_aslab, &e->pager, sizeof(sicachebranch));
	sr_allocopen(&e->a_ctlcursor, &sr_aslab, &e->pager, sizeof(soctlcursor));
	sr_allocopen(&e->a_snapshot, &sr_aslab, &e->pager, sizeof(sosnapshot));
	sr_allocopen(&e->a_tx, &sr_aslab, &e->pager, sizeof(sotx));
	sr_allocopen(&e->a_sxv, &sr_aslab, &e->pager, sizeof(sxv));
	so_statusinit(&e->status);
	so_statusset(&e->status, SO_OFFLINE);
	so_ctlinit(&e->ctl, e);
	so_objindex_init(&e->db);
	so_objindex_init(&e->tx);
	so_objindex_init(&e->snapshot);
	so_objindex_init(&e->ctlcursor);
	sr_mutexinit(&e->apilock);
	sr_quotainit(&e->quota);
	sr_seqinit(&e->seq);
	sr_errorinit(&e->error);
	sr_init(&e->r, &e->error, &e->a, &e->seq, NULL, &e->ei);
	se_init(&e->se);
	sl_poolinit(&e->lp, &e->r);
	sx_init(&e->xm, &e->r, &e->a_sxv);
	so_scheduler_init(&e->sched, e);
	return &e->o;
}
#line 1 "sophia/sophia/so_ctl.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/










void *so_ctlreturn(src *c, void *o)
{
	so *e = o;
	int size = 0;
	int type = c->flags & ~SR_CRO;
	char *value = NULL;
	char function_sz[] = "function";
	char integer[64];
	switch (type) {
	case SR_CU32:
		size = snprintf(integer, sizeof(integer), "%"PRIu32, *(uint32_t*)c->value);
		value = integer;
		break;
	case SR_CU64:
		size = snprintf(integer, sizeof(integer), "%"PRIu64, *(uint64_t*)c->value);
		value = integer;
		break;
	case SR_CSZREF:
		value = *(char**)c->value;
		if (value)
			size = strlen(value);
		break;
	case SR_CSZ:
		value = c->value;
		if (value)
			size = strlen(value);
		break;
	case SR_CVOID: {
		value = function_sz;
		size = sizeof(function_sz);
		break;
	}
	case SR_CC: assert(0);
		break;
	}
	if (value)
		size++;
	svlocal l;
	l.lsn       = 0;
	l.flags     = 0;
	l.keysize   = strlen(c->name) + 1;
	l.key       = c->name;
	l.valuesize = size;
	l.value     = value;
	sv vp;
	svinit(&vp, &sv_localif, &l, NULL);
	svv *v = sv_valloc(&e->a, &vp);
	if (srunlikely(v == NULL)) {
		sr_error(&e->error, "%s", "memory allocation failed");
		return NULL;
	}
	sov *result = (sov*)so_vnew(e, NULL);
	if (srunlikely(result == NULL)) {
		sv_vfree(&e->a, v);
		sr_error(&e->error, "%s", "memory allocation failed");
		return NULL;
	}
	svinit(&vp, &sv_vif, v, NULL);
	return so_vput(result, &vp);
}

static inline int
so_ctlv(src *c, srcstmt *s, va_list args)
{
	switch (s->op) {
	case SR_CGET: {
		void *ret = so_ctlreturn(c, s->ptr);
		if ((srunlikely(ret == NULL)))
			return -1;
		*s->result = ret;
		return 0;
	}
	case SR_CSERIALIZE:
		return sr_cserialize(c, s);
	case SR_CSET: {
		char *arg = va_arg(args, char*);
		return sr_cset(c, s, arg);
	}
	}
	assert(0);
	return -1;
}

static inline int
so_ctlv_offline(src *c, srcstmt *s, va_list args)
{
	so *e = s->ptr;
	if (srunlikely(s->op == SR_CSET && so_statusactive(&e->status))) {
		sr_error(s->r->e, "write to %s is offline-only", s->path);
		return -1;
	}
	return so_ctlv(c, s, args);
}

static inline int
so_ctlsophia_error(src *c, srcstmt *s, va_list args srunused)
{
	so *e = s->ptr;
	char *errorp;
	char  error[128];
	error[0] = 0;
	int len = sr_errorcopy(&e->error, error, sizeof(error));
	if (srlikely(len == 0))
		errorp = NULL;
	else
		errorp = error;
	src ctl = {
		.name     = c->name,
		.flags    = c->flags,
		.function = NULL,
		.value    = errorp,
		.next     = NULL
	};
	return so_ctlv(&ctl, s, args);
}

static inline src*
so_ctlsophia(so *e, soctlrt *rt, src **pc)
{
	src *sophia = *pc;
	src *p = NULL;
	sr_clink(&p, sr_c(pc, so_ctlv,            "version",     SR_CSZ|SR_CRO, rt->version));
	sr_clink(&p, sr_c(pc, so_ctlv,            "build",       SR_CSZ|SR_CRO, SR_VERSION_COMMIT));
	sr_clink(&p, sr_c(pc, so_ctlsophia_error, "error",       SR_CSZ|SR_CRO, NULL));
	sr_clink(&p, sr_c(pc, so_ctlv_offline,    "path",        SR_CSZREF,     &e->ctl.path));
	sr_clink(&p, sr_c(pc, so_ctlv_offline,    "path_create", SR_CU32,       &e->ctl.path_create));
	return sr_c(pc, NULL, "sophia", SR_CC, sophia);
}

static inline src*
so_ctlmemory(so *e, soctlrt *rt, src **pc)
{
	src *memory = *pc;
	src *p = NULL;
	sr_clink(&p, sr_c(pc, so_ctlv_offline, "limit",           SR_CU64,        &e->ctl.memory_limit));
	sr_clink(&p, sr_c(pc, so_ctlv,         "used",            SR_CU64|SR_CRO, &rt->memory_used));
	sr_clink(&p, sr_c(pc, so_ctlv,         "pager_pool_size", SR_CU32|SR_CRO, &e->pager.pool_size));
	sr_clink(&p, sr_c(pc, so_ctlv,         "pager_page_size", SR_CU32|SR_CRO, &e->pager.page_size));
	sr_clink(&p, sr_c(pc, so_ctlv,         "pager_pools",     SR_CU32|SR_CRO, &e->pager.pools));
	return sr_c(pc, NULL, "memory", SR_CC, memory);
}

static inline int
so_ctlcompaction_set(src *c srunused, srcstmt *s, va_list args)
{
	so *e = s->ptr;
	if (s->op != SR_CSET) {
		sr_error(&e->error, "%s", "bad operation");
		return -1;
	}
	if (srunlikely(so_statusactive(&e->status))) {
		sr_error(s->r->e, "write to %s is offline-only", s->path);
		return -1;
	}
	/* validate argument */
	char *arg = va_arg(args, char*);
	uint32_t percent = atoi(arg);
	if (percent > 100) {
		sr_error(&e->error, "%s", "bad argument");
		return -1;
	}
	sizone z;
	memset(&z, 0, sizeof(z));
	z.enable = 1;
	si_zonemap_set(&e->ctl.zones, percent, &z);
	return 0;
}

static inline src*
so_ctlcompaction(so *e, soctlrt *rt srunused, src **pc)
{
	src *compaction = *pc;
	src *prev;
	src *p = NULL;
	sr_clink(&p, sr_c(pc, so_ctlv_offline, "node_size", SR_CU32, &e->ctl.node_size));
	sr_clink(&p, sr_c(pc, so_ctlv_offline, "page_size", SR_CU32, &e->ctl.page_size));
	prev = p;
	int i = 0;
	for (; i < 11; i++) {
		sizone *z = &e->ctl.zones.zones[i];
		if (! z->enable)
			continue;
		src *zone = *pc;
		p = NULL;
		sr_clink(&p,    sr_c(pc, so_ctlv_offline, "mode",              SR_CU32, &z->mode));
		sr_clink(&p,    sr_c(pc, so_ctlv_offline, "compact_wm",        SR_CU32, &z->compact_wm));
		sr_clink(&p,    sr_c(pc, so_ctlv_offline, "branch_prio",       SR_CU32, &z->branch_prio));
		sr_clink(&p,    sr_c(pc, so_ctlv_offline, "branch_wm",         SR_CU32, &z->branch_wm));
		sr_clink(&p,    sr_c(pc, so_ctlv_offline, "branch_age",        SR_CU32, &z->branch_age));
		sr_clink(&p,    sr_c(pc, so_ctlv_offline, "branch_age_period", SR_CU32, &z->branch_age_period));
		sr_clink(&p,    sr_c(pc, so_ctlv_offline, "branch_age_wm",     SR_CU32, &z->branch_age_wm));
		sr_clink(&p,    sr_c(pc, so_ctlv_offline, "backup_prio",       SR_CU32, &z->backup_prio));
		sr_clink(&p,    sr_c(pc, so_ctlv_offline, "gc_wm",             SR_CU32, &z->gc_wm));
		sr_clink(&p,    sr_c(pc, so_ctlv_offline, "gc_prio",           SR_CU32, &z->gc_prio));
		sr_clink(&p,    sr_c(pc, so_ctlv_offline, "gc_period",         SR_CU32, &z->gc_period));
		sr_clink(&prev, sr_c(pc, NULL, z->name, SR_CC, zone));
	}
	return sr_c(pc, so_ctlcompaction_set, "compaction", SR_CC, compaction);
}

static inline int
so_ctlscheduler_trace(src *c, srcstmt *s, va_list args srunused)
{
	soworker *w = c->value;
	char tracesz[128];
	char *trace;
	int tracelen = sr_tracecopy(&w->trace, tracesz, sizeof(tracesz));
	if (srlikely(tracelen == 0))
		trace = NULL;
	else
		trace = tracesz;
	src ctl = {
		.name     = c->name,
		.flags    = c->flags,
		.function = NULL,
		.value    = trace,
		.next     = NULL
	};
	return so_ctlv(&ctl, s, args);
}

static inline int
so_ctlscheduler_checkpoint(src *c, srcstmt *s, va_list args)
{
	if (s->op != SR_CSET)
		return so_ctlv(c, s, args);
	so *e = s->ptr;
	return so_scheduler_checkpoint(e);
}

static inline int
so_ctlscheduler_checkpoint_on_complete(src *c, srcstmt *s, va_list args)
{
	so *e = s->ptr;
	if (s->op != SR_CSET)
		return so_ctlv(c, s, args);
	if (srunlikely(so_statusactive(&e->status))) {
		sr_error(s->r->e, "write to %s is offline-only", s->path);
		return -1;
	}
	char *v   = va_arg(args, char*);
	char *arg = va_arg(args, char*);
	int rc = sr_triggerset(&e->ctl.checkpoint_on_complete, v);
	if (srunlikely(rc == -1))
		return -1;
	if (arg) {
		rc = sr_triggersetarg(&e->ctl.checkpoint_on_complete, arg);
		if (srunlikely(rc == -1))
			return -1;
	}
	return 0;
}

static inline int
so_ctlscheduler_gc(src *c, srcstmt *s, va_list args)
{
	if (s->op != SR_CSET)
		return so_ctlv(c, s, args);
	so *e = s->ptr;
	return so_scheduler_gc(e);
}

static inline int
so_ctlscheduler_run(src *c, srcstmt *s, va_list args)
{
	if (s->op != SR_CSET)
		return so_ctlv(c, s, args);
	so *e = s->ptr;
	return so_scheduler_call(e);
}

static inline src*
so_ctlscheduler(so *e, soctlrt *rt, src **pc)
{
	src *scheduler = *pc;
	src *prev;
	src *p = NULL;
	sr_clink(&p, sr_c(pc, so_ctlv_offline,     "threads",                SR_CU32,        &e->ctl.threads));
	sr_clink(&p, sr_c(pc, so_ctlv,             "zone",                   SR_CSZ|SR_CRO,  rt->zone));
	sr_clink(&p, sr_c(pc, so_ctlv,             "checkpoint_active",      SR_CU32|SR_CRO, &rt->checkpoint_active));
	sr_clink(&p, sr_c(pc, so_ctlv,             "checkpoint_lsn",         SR_CU64|SR_CRO, &rt->checkpoint_lsn));
	sr_clink(&p, sr_c(pc, so_ctlv,             "checkpoint_lsn_last",    SR_CU64|SR_CRO, &rt->checkpoint_lsn_last));
	sr_clink(&p, sr_c(pc, so_ctlscheduler_checkpoint_on_complete, "checkpoint_on_complete", SR_CVOID, NULL));
	sr_clink(&p, sr_c(pc, so_ctlscheduler_checkpoint, "checkpoint",      SR_CVOID, NULL));
	sr_clink(&p, sr_c(pc, so_ctlv,             "gc_active",              SR_CU32|SR_CRO, &rt->gc_active));
	sr_clink(&p, sr_c(pc, so_ctlscheduler_gc,  "gc",                     SR_CVOID, NULL));
	sr_clink(&p, sr_c(pc, so_ctlscheduler_run, "run",                    SR_CVOID, NULL));
	prev = p;
	srlist *i;
	sr_listforeach(&e->sched.workers.list, i) {
		soworker *w = srcast(i, soworker, link);
		src *worker = *pc;
		p = NULL;
		sr_clink(&p,    sr_c(pc, so_ctlscheduler_trace, "trace", SR_CSZ|SR_CRO, w));
		sr_clink(&prev, sr_c(pc, NULL, w->name, SR_CC, worker));
	}
	return sr_c(pc, NULL, "scheduler", SR_CC, scheduler);
}

static inline int
so_ctllog_rotate(src *c, srcstmt *s, va_list args)
{
	if (s->op != SR_CSET)
		return so_ctlv(c, s, args);
	so *e = s->ptr;
	return sl_poolrotate(&e->lp);
}

static inline int
so_ctllog_gc(src *c, srcstmt *s, va_list args)
{
	if (s->op != SR_CSET)
		return so_ctlv(c, s, args);
	so *e = s->ptr;
	return sl_poolgc(&e->lp);
}

static inline src*
so_ctllog(so *e, soctlrt *rt, src **pc)
{
	src *log = *pc;
	src *p = NULL;
	sr_clink(&p, sr_c(pc, so_ctlv_offline,  "enable",            SR_CU32,        &e->ctl.log_enable));
	sr_clink(&p, sr_c(pc, so_ctlv_offline,  "path",              SR_CSZREF,      &e->ctl.log_path));
	sr_clink(&p, sr_c(pc, so_ctlv_offline,  "sync",              SR_CU32,        &e->ctl.log_sync));
	sr_clink(&p, sr_c(pc, so_ctlv_offline,  "rotate_wm",         SR_CU32,        &e->ctl.log_rotate_wm));
	sr_clink(&p, sr_c(pc, so_ctlv_offline,  "rotate_sync",       SR_CU32,        &e->ctl.log_rotate_sync));
	sr_clink(&p, sr_c(pc, so_ctllog_rotate, "rotate",            SR_CVOID,       NULL));
	sr_clink(&p, sr_c(pc, so_ctllog_gc,     "gc",                SR_CVOID,       NULL));
	sr_clink(&p, sr_c(pc, so_ctlv,          "files",             SR_CU32|SR_CRO, &rt->log_files));
	sr_clink(&p, sr_c(pc, so_ctlv_offline,  "two_phase_recover", SR_CU32,        &e->ctl.two_phase_recover));
	sr_clink(&p, sr_c(pc, so_ctlv_offline,  "commit_lsn",        SR_CU32,        &e->ctl.commit_lsn));
	return sr_c(pc, NULL, "log", SR_CC, log);
}

static inline src*
so_ctlmetric(so *e srunused, soctlrt *rt, src **pc)
{
	src *metric = *pc;
	src *p = NULL;
	sr_clink(&p, sr_c(pc, so_ctlv, "dsn",  SR_CU32|SR_CRO, &rt->seq.dsn));
	sr_clink(&p, sr_c(pc, so_ctlv, "nsn",  SR_CU32|SR_CRO, &rt->seq.nsn));
	sr_clink(&p, sr_c(pc, so_ctlv, "bsn",  SR_CU32|SR_CRO, &rt->seq.bsn));
	sr_clink(&p, sr_c(pc, so_ctlv, "lsn",  SR_CU64|SR_CRO, &rt->seq.lsn));
	sr_clink(&p, sr_c(pc, so_ctlv, "lfsn", SR_CU32|SR_CRO, &rt->seq.lfsn));
	sr_clink(&p, sr_c(pc, so_ctlv, "tsn",  SR_CU32|SR_CRO, &rt->seq.tsn));
	return sr_c(pc, NULL, "metric", SR_CC, metric);
}

static inline int
so_ctldb_set(src *c srunused, srcstmt *s, va_list args)
{
	/* set(db) */
	so *e = s->ptr;
	if (s->op != SR_CSET) {
		sr_error(&e->error, "%s", "bad operation");
		return -1;
	}
	char *name = va_arg(args, char*);
	sodb *db = (sodb*)so_dbmatch(e, name);
	if (srunlikely(db)) {
		sr_error(&e->error, "database '%s' is exists", name);
		return -1;
	}
	db = (sodb*)so_dbnew(e, name);
	if (srunlikely(db == NULL))
		return -1;
	so_objindex_register(&e->db, &db->o);
	return 0;
}

static inline int
so_ctldb_get(src *c, srcstmt *s, va_list args srunused)
{
	/* get(db.name) */
	so *e = s->ptr;
	if (s->op != SR_CGET) {
		sr_error(&e->error, "%s", "bad operation");
		return -1;
	}
	assert(c->ptr != NULL);
	*s->result = c->ptr;
	return 0;
}

static inline int
so_ctldb_cmp(src *c, srcstmt *s, va_list args)
{
	if (s->op != SR_CSET)
		return so_ctlv(c, s, args);
	sodb *db = c->value;
	if (srunlikely(so_statusactive(&db->status))) {
		sr_error(s->r->e, "write to %s is offline-only", s->path);
		return -1;
	}
	char *v   = va_arg(args, char*);
	char *arg = va_arg(args, char*);
	int rc = sr_cmpset(&db->ctl.cmp, v);
	if (srunlikely(rc == -1))
		return -1;
	if (arg) {
		rc = sr_cmpsetarg(&db->ctl.cmp, arg);
		if (srunlikely(rc == -1))
			return -1;
	}
	return 0;
}

static inline int
so_ctldb_status(src *c, srcstmt *s, va_list args)
{
	sodb *db = c->value;
	char *status = so_statusof(&db->status);
	src ctl = {
		.name     = c->name,
		.flags    = c->flags,
		.function = NULL,
		.value    = status,
		.next     = NULL
	};
	return so_ctlv(&ctl, s, args);
}

static inline int
so_ctldb_branch(src *c, srcstmt *s, va_list args)
{
	if (s->op != SR_CSET)
		return so_ctlv(c, s, args);
	sodb *db = c->value;
	return so_scheduler_branch(db);
}

static inline int
so_ctldb_compact(src *c, srcstmt *s, va_list args)
{
	if (s->op != SR_CSET)
		return so_ctlv(c, s, args);
	sodb *db = c->value;
	return so_scheduler_compact(db);
}

static inline int
so_ctldb_lockdetect(src *c, srcstmt *s, va_list args)
{
	if (s->op != SR_CSET)
		return so_ctlv(c, s, args);
	sotx *tx = va_arg(args, sotx*);
	int rc = sx_deadlock(&tx->t);
	return rc;
}

static inline int
so_ctlv_dboffline(src *c, srcstmt *s, va_list args)
{
	sodb *db = c->ptr;
	if (srunlikely(s->op == SR_CSET && so_statusactive(&db->status))) {
		sr_error(s->r->e, "write to %s is offline-only", s->path);
		return -1;
	}
	return so_ctlv(c, s, args);
}

static inline src*
so_ctldb(so *e, soctlrt *rt srunused, src **pc)
{
	src *db = NULL;
	src *prev = NULL;
	src *p;
	srlist *i;
	sr_listforeach(&e->db.list, i)
	{
		sodb *o = (sodb*)srcast(i, soobj, link);
		si_profilerbegin(&o->ctl.rtp, &o->index);
		si_profiler(&o->ctl.rtp);
		si_profilerend(&o->ctl.rtp);
		src *index = *pc;
		p = NULL;
		sr_clink(&p, sr_c(pc, so_ctldb_cmp,    "cmp",              SR_CVOID,       o));
		sr_clink(&p, sr_c(pc, so_ctlv,         "memory_used",      SR_CU64|SR_CRO, &o->ctl.rtp.memory_used));
		sr_clink(&p, sr_c(pc, so_ctlv,         "node_count",       SR_CU32|SR_CRO, &o->ctl.rtp.total_node_count));
		sr_clink(&p, sr_c(pc, so_ctlv,         "node_size",        SR_CU64|SR_CRO, &o->ctl.rtp.total_node_size));
		sr_clink(&p, sr_c(pc, so_ctlv,         "count",            SR_CU64|SR_CRO, &o->ctl.rtp.count));
		sr_clink(&p, sr_c(pc, so_ctlv,         "count_dup",        SR_CU64|SR_CRO, &o->ctl.rtp.count_dup));
		sr_clink(&p, sr_c(pc, so_ctlv,         "read_disk",        SR_CU64|SR_CRO, &o->ctl.rtp.read_disk));
		sr_clink(&p, sr_c(pc, so_ctlv,         "read_cache",       SR_CU64|SR_CRO, &o->ctl.rtp.read_cache));
		sr_clink(&p, sr_c(pc, so_ctlv,         "branch_count",     SR_CU32|SR_CRO, &o->ctl.rtp.total_branch_count));
		sr_clink(&p, sr_c(pc, so_ctlv,         "branch_avg",       SR_CU32|SR_CRO, &o->ctl.rtp.total_branch_avg));
		sr_clink(&p, sr_c(pc, so_ctlv,         "branch_max",       SR_CU32|SR_CRO, &o->ctl.rtp.total_branch_max));
		sr_clink(&p, sr_c(pc, so_ctlv,         "branch_histogram", SR_CSZ|SR_CRO,  o->ctl.rtp.histogram_branch_ptr));
		src *database = *pc;
		p = NULL;
		sr_clink(&p,          sr_c(pc, so_ctlv,             "name",       SR_CSZ|SR_CRO,  o->ctl.name));
		sr_clink(&p,  sr_cptr(sr_c(pc, so_ctlv,             "id",         SR_CU32,        &o->ctl.id), o));
		sr_clink(&p,          sr_c(pc, so_ctldb_status,     "status",     SR_CSZ|SR_CRO,  o));
		sr_clink(&p,  sr_cptr(sr_c(pc, so_ctlv_dboffline,   "path",       SR_CSZREF,      &o->ctl.path), o));
		sr_clink(&p,  sr_cptr(sr_c(pc, so_ctlv_dboffline,   "sync",       SR_CU32,        &o->ctl.sync), o));
		sr_clink(&p,          sr_c(pc, so_ctldb_branch,     "branch",     SR_CVOID,       o));
		sr_clink(&p,          sr_c(pc, so_ctldb_compact,    "compact",    SR_CVOID,       o));
		sr_clink(&p,          sr_c(pc, so_ctldb_lockdetect, "lockdetect", SR_CVOID,       NULL));
		sr_clink(&p,          sr_c(pc, NULL,                "index",      SR_CC,          index));
		sr_clink(&prev, sr_cptr(sr_c(pc, so_ctldb_get, o->ctl.name, SR_CC, database), o));
		if (db == NULL)
			db = prev;
	}
	return sr_c(pc, so_ctldb_set, "db", SR_CC, db);
}

static inline int
so_ctlsnapshot_set(src *c, srcstmt *s, va_list args)
{
	if (s->op != SR_CSET)
		return so_ctlv(c, s, args);
	so *e = s->ptr;
	char *name = va_arg(args, char*);
	uint64_t lsn = sr_seq(&e->seq, SR_LSN);
	/* create snapshot object */
	sosnapshot *snapshot =
		(sosnapshot*)so_snapshotnew(e, lsn, name);
	if (srunlikely(snapshot == NULL))
		return -1;
	so_objindex_register(&e->snapshot, &snapshot->o);
	return 0;
}

static inline int
so_ctlsnapshot_setlsn(src *c, srcstmt *s, va_list args)
{
	int rc = so_ctlv(c, s, args);
	if (srunlikely(rc == -1))
		return -1;
	if (s->op != SR_CSET)
		return  0;
	sosnapshot *snapshot = c->ptr;
	so_snapshotupdate(snapshot);
	return 0;
}

static inline int
so_ctlsnapshot_get(src *c, srcstmt *s, va_list args srunused)
{
	/* get(snapshot.name) */
	so *e = s->ptr;
	if (s->op != SR_CGET) {
		sr_error(&e->error, "%s", "bad operation");
		return -1;
	}
	assert(c->ptr != NULL);
	*s->result = c->ptr;
	return 0;
}

static inline src*
so_ctlsnapshot(so *e, soctlrt *rt srunused, src **pc)
{
	src *snapshot = NULL;
	src *prev = NULL;
	srlist *i;
	sr_listforeach(&e->snapshot.list, i)
	{
		sosnapshot *s = (sosnapshot*)srcast(i, soobj, link);
		src *p = sr_cptr(sr_c(pc, so_ctlsnapshot_setlsn, "lsn", SR_CU64, &s->vlsn), s);
		sr_clink(&prev, sr_cptr(sr_c(pc, so_ctlsnapshot_get, s->name, SR_CC, p), s));
		if (snapshot == NULL)
			snapshot = prev;
	}
	return sr_c(pc, so_ctlsnapshot_set, "snapshot", SR_CC, snapshot);
}

static inline int
so_ctlbackup_on_complete(src *c, srcstmt *s, va_list args)
{
	so *e = s->ptr;
	if (s->op != SR_CSET)
		return so_ctlv(c, s, args);
	if (srunlikely(so_statusactive(&e->status))) {
		sr_error(s->r->e, "write to %s is offline-only", s->path);
		return -1;
	}
	char *v   = va_arg(args, char*);
	char *arg = va_arg(args, char*);
	int rc = sr_triggerset(&e->ctl.backup_on_complete, v);
	if (srunlikely(rc == -1))
		return -1;
	if (arg) {
		rc = sr_triggersetarg(&e->ctl.backup_on_complete, arg);
		if (srunlikely(rc == -1))
			return -1;
	}
	return 0;
}

static inline int
so_ctlbackup_run(src *c, srcstmt *s, va_list args)
{
	if (s->op != SR_CSET)
		return so_ctlv(c, s, args);
	so *e = s->ptr;
	return so_scheduler_backup(e);
}


static inline src*
so_ctlbackup(so *e, soctlrt *rt, src **pc)
{
	src *backup = *pc;
	src *p = NULL;
	sr_clink(&p, sr_c(pc, so_ctlv_offline, "path", SR_CSZREF, &e->ctl.backup_path));
	sr_clink(&p, sr_c(pc, so_ctlbackup_run, "run", SR_CVOID, NULL));
	sr_clink(&p, sr_c(pc, so_ctlbackup_on_complete, "on_complete", SR_CVOID, NULL));
	sr_clink(&p, sr_c(pc, so_ctlv, "active", SR_CU32|SR_CRO, &rt->backup_active));
	sr_clink(&p, sr_c(pc, so_ctlv, "last", SR_CU32|SR_CRO, &rt->backup_last));
	sr_clink(&p, sr_c(pc, so_ctlv, "last_complete", SR_CU32|SR_CRO, &rt->backup_last_complete));
	return sr_c(pc, NULL, "backup", SR_CC, backup);
}

static inline src*
so_ctldebug(so *e, soctlrt *rt srunused, src **pc)
{
	src *prev = NULL;
	src *p = NULL;
	prev = p;
	src *ei = *pc;
	sr_clink(&p, sr_c(pc, so_ctlv, "sd_build_0",      SR_CU32, &e->ei.e[0]));
	sr_clink(&p, sr_c(pc, so_ctlv, "sd_build_1",      SR_CU32, &e->ei.e[1]));
	sr_clink(&p, sr_c(pc, so_ctlv, "si_branch_0",     SR_CU32, &e->ei.e[2]));
	sr_clink(&p, sr_c(pc, so_ctlv, "si_compaction_0", SR_CU32, &e->ei.e[3]));
	sr_clink(&p, sr_c(pc, so_ctlv, "si_compaction_1", SR_CU32, &e->ei.e[4]));
	sr_clink(&p, sr_c(pc, so_ctlv, "si_compaction_2", SR_CU32, &e->ei.e[5]));
	sr_clink(&p, sr_c(pc, so_ctlv, "si_compaction_3", SR_CU32, &e->ei.e[6]));
	sr_clink(&p, sr_c(pc, so_ctlv, "si_compaction_4", SR_CU32, &e->ei.e[7]));
	sr_clink(&p, sr_c(pc, so_ctlv, "si_recover_0",    SR_CU32, &e->ei.e[8]));
	sr_clink(&prev, sr_c(pc, so_ctldb_set, "error_injection", SR_CC, ei));
	src *debug = prev;
	return sr_c(pc, NULL, "debug", SR_CC, debug);
}

static src*
so_ctlprepare(so *e, soctlrt *rt, src *c, int serialize)
{
	/* sophia */
	src *pc = c;
	src *sophia     = so_ctlsophia(e, rt, &pc);
	src *memory     = so_ctlmemory(e, rt, &pc);
	src *compaction = so_ctlcompaction(e, rt, &pc);
	src *scheduler  = so_ctlscheduler(e, rt, &pc);
	src *metric     = so_ctlmetric(e, rt, &pc);
	src *log        = so_ctllog(e, rt, &pc);
	src *snapshot   = so_ctlsnapshot(e, rt, &pc);
	src *backup     = so_ctlbackup(e, rt, &pc);
	src *db         = so_ctldb(e, rt, &pc);
	src *debug      = so_ctldebug(e, rt, &pc);

	sophia->next     = memory;
	memory->next     = compaction;
	compaction->next = scheduler;
	scheduler->next  = metric;
	metric->next     = log;
	log->next        = snapshot;
	snapshot->next   = backup;
	backup->next     = db;
	if (! serialize)
		db->next = debug;
	return sophia;
}

static int
so_ctlrt(so *e, soctlrt *rt)
{
	/* sophia */
	snprintf(rt->version, sizeof(rt->version),
	         "%d.%d.%d",
	         SR_VERSION_A - '0',
	         SR_VERSION_B - '0',
	         SR_VERSION_C - '0');

	/* memory */
	rt->memory_used = sr_quotaused(&e->quota);

	/* scheduler */
	sr_mutexlock(&e->sched.lock);
	rt->checkpoint_active    = e->sched.checkpoint;
	rt->checkpoint_lsn_last  = e->sched.checkpoint_lsn_last;
	rt->checkpoint_lsn       = e->sched.checkpoint_lsn;
	rt->backup_active        = e->sched.backup;
	rt->backup_last          = e->sched.backup_last;
	rt->backup_last_complete = e->sched.backup_last_complete;
	rt->gc_active            = e->sched.gc;
	sr_mutexunlock(&e->sched.lock);

	int v = sr_quotaused_percent(&e->quota);
	sizone *z = si_zonemap(&e->ctl.zones, v);
	memcpy(rt->zone, z->name, sizeof(rt->zone));

	/* log */
	rt->log_files = sl_poolfiles(&e->lp);

	/* metric */
	sr_seqlock(&e->seq);
	rt->seq = e->seq;
	sr_sequnlock(&e->seq);
	return 0;
}

static int
so_ctlset(soobj *obj, va_list args)
{
	so *e = so_of(obj);
	soctlrt rt;
	so_ctlrt(e, &rt);
	src ctl[1024];
	src *root;
	root = so_ctlprepare(e, &rt, ctl, 0);
	char *path = va_arg(args, char*);
	srcstmt stmt = {
		.op        = SR_CSET,
		.path      = path,
		.serialize = NULL,
		.result    = NULL,
		.ptr       = e,
		.r         = &e->r
	};
	return sr_cexecv(root, &stmt, args);
}

static void*
so_ctlget(soobj *obj, va_list args)
{
	so *e = so_of(obj);
	soctlrt rt;
	so_ctlrt(e, &rt);
	src ctl[1024];
	src *root;
	root = so_ctlprepare(e, &rt, ctl, 0);
	char *path   = va_arg(args, char*);
	void *result = NULL;
	srcstmt stmt = {
		.op        = SR_CGET,
		.path      = path,
		.serialize = NULL,
		.result    = &result,
		.ptr       = e,
		.r         = &e->r
	};
	int rc = sr_cexecv(root, &stmt, args);
	if (srunlikely(rc == -1))
		return NULL;
	return result;
}

int so_ctlserialize(soctl *c, srbuf *buf)
{
	so *e = so_of(&c->o);
	soctlrt rt;
	so_ctlrt(e, &rt);
	src ctl[1024];
	src *root;
	root = so_ctlprepare(e, &rt, ctl, 1);
	srcstmt stmt = {
		.op        = SR_CSERIALIZE,
		.path      = NULL,
		.serialize = buf,
		.result    = NULL,
		.ptr       = e,
		.r         = &e->r
	};
	return sr_cexec(root, &stmt);
}

static void*
so_ctlcursor(soobj *o, va_list args srunused)
{
	so *e = so_of(o);
	return so_ctlcursor_new(e);
}

static void*
so_ctltype(soobj *o srunused, va_list args srunused) {
	return "ctl";
}

static soobjif soctlif =
{
	.ctl      = NULL,
	.open     = NULL,
	.destroy  = NULL,
	.error    = NULL,
	.set      = so_ctlset,
	.get      = so_ctlget,
	.del      = NULL,
	.drop     = NULL,
	.begin    = NULL,
	.prepare  = NULL,
	.commit   = NULL,
	.cursor   = so_ctlcursor,
	.object   = NULL,
	.type     = so_ctltype
};

void so_ctlinit(soctl *c, void *e)
{
	so *o = e;
	so_objinit(&c->o, SOCTL, &soctlif, e);
	c->path              = NULL;
	c->path_create       = 1;
	c->memory_limit      = 0;
	c->node_size         = 64 * 1024 * 1024;
	c->page_size         = 64 * 1024;
	c->threads           = 5;
	c->log_enable        = 1;
	c->log_path          = NULL;
	c->log_rotate_wm     = 500000;
	c->log_sync          = 0;
	c->log_rotate_sync   = 1;
	c->two_phase_recover = 0;
	c->commit_lsn        = 0;
	sizone def = {
		.enable        = 1,
		.mode          = 3, /* branch + compact */
		.compact_wm    = 2,
		.branch_prio   = 1,
		.branch_wm     = 10 * 1024 * 1024,
		.branch_age    = 40,
		.branch_age_period = 40,
		.branch_age_wm = 1 * 1024 * 1024,
		.backup_prio   = 1,
		.gc_prio       = 1,
		.gc_period     = 60,
		.gc_wm         = 30
	};
	sizone redzone = {
		.enable        = 1,
		.mode          = 2, /* checkpoint */
		.compact_wm    = 4,
		.branch_prio   = 0,
		.branch_wm     = 0,
		.branch_age    = 0,
		.branch_age_period = 0,
		.branch_age_wm = 0,
		.backup_prio   = 0,
		.gc_prio       = 0,
		.gc_period     = 0,
		.gc_wm         = 0
	};
	si_zonemap_set(&o->ctl.zones,  0, &def);
	si_zonemap_set(&o->ctl.zones, 80, &redzone);

	c->backup_path = NULL;
	sr_triggerinit(&c->backup_on_complete);
	sr_triggerinit(&c->checkpoint_on_complete);
}

void so_ctlfree(soctl *c)
{
	so *e = so_of(&c->o);
	if (c->path) {
		sr_free(&e->a, c->path);
		c->path = NULL;
	}
	if (c->log_path) {
		sr_free(&e->a, c->log_path);
		c->log_path = NULL;
	}
	if (c->backup_path) {
		sr_free(&e->a, c->backup_path);
		c->backup_path = NULL;
	}
}

int so_ctlvalidate(soctl *c)
{
	so *e = so_of(&c->o);
	if (c->path == NULL) {
		sr_error(&e->error, "%s", "repository path is not set");
		return -1;
	}
	char path[1024];
	if (c->log_path == NULL) {
		snprintf(path, sizeof(path), "%s/log", c->path);
		c->log_path = sr_strdup(&e->a, path);
		if (srunlikely(c->log_path == NULL)) {
			sr_error(&e->error, "%s", "memory allocation failed");
			return -1;
		}
	}
	int i = 0;
	for (; i < 11; i++) {
		sizone *z = &e->ctl.zones.zones[i];
		if (! z->enable)
			continue;
		if (z->compact_wm <= 1) {
			sr_error(&e->error, "bad %d.compact_wm value", i * 10);
			return -1;
		}
	}
	return 0;
}
#line 1 "sophia/sophia/so_ctlcursor.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/










static int
so_ctlcursor_destroy(soobj *o, va_list args srunused)
{
	soctlcursor *c = (soctlcursor*)o;
	so *e = so_of(o);
	sr_buffree(&c->dump, &e->a);
	if (c->v)
		so_objdestroy(c->v);
	so_objindex_unregister(&e->ctlcursor, &c->o);
	sr_free(&e->a_ctlcursor, c);
	return 0;
}

static inline int
so_ctlcursor_set(soctlcursor *c)
{
	int type = c->pos->type;
	void *value = NULL;
	if (c->pos->valuelen > 0)
		value = sr_cvvalue(c->pos);
	src match = {
		.name     = sr_cvname(c->pos),
		.value    = value,
		.flags    = type,
		.ptr      = NULL,
		.function = NULL,
		.next     = NULL
	};
	so *e = so_of(&c->o);
	void *v = so_ctlreturn(&match, e);
	if (srunlikely(v == NULL))
		return -1;
	if (c->v)
		so_objdestroy(c->v);
	c->v = v;
	return 0;
}

static inline int
so_ctlcursor_next(soctlcursor *c)
{
	int rc;
	if (c->pos == NULL) {
		assert( sr_bufsize(&c->dump) >= (int)sizeof(srcv) );
		c->pos = (srcv*)c->dump.s;
	} else {
		int size = sizeof(srcv) + c->pos->namelen + c->pos->valuelen;
		c->pos = (srcv*)((char*)c->pos + size);
		if ((char*)c->pos >= c->dump.p)
			c->pos = NULL;
	}
	if (srunlikely(c->pos == NULL)) {
		if (c->v)
			so_objdestroy(c->v);
		c->v = NULL;
		return 0;
	}
	rc = so_ctlcursor_set(c);
	if (srunlikely(rc == -1))
		return -1;
	return 1;
}

static void*
so_ctlcursor_get(soobj *o, va_list args srunused)
{
	soctlcursor *c = (soctlcursor*)o;
	if (c->ready) {
		c->ready = 0;
		return c->v;
	}
	if (so_ctlcursor_next(c) == 0)
		return NULL;
	return c->v;
}

static void*
so_ctlcursor_obj(soobj *obj, va_list args srunused)
{
	soctlcursor *c = (soctlcursor*)obj;
	if (c->v == NULL)
		return NULL;
	return c->v;
}

static void*
so_ctlcursor_type(soobj *o srunused, va_list args srunused) {
	return "ctl_cursor";
}

static soobjif soctlcursorif =
{
	.ctl      = NULL,
	.open     = NULL,
	.destroy  = so_ctlcursor_destroy,
	.error    = NULL,
	.set      = NULL,
	.get      = so_ctlcursor_get,
	.del      = NULL,
	.drop     = NULL,
	.begin    = NULL,
	.prepare  = NULL,
	.commit   = NULL,
	.cursor   = NULL,
	.object   = so_ctlcursor_obj,
	.type     = so_ctlcursor_type
};

static inline int
so_ctlcursor_open(soctlcursor *c)
{
	so *e = so_of(&c->o);
	int rc = so_ctlserialize(&e->ctl, &c->dump);
	if (srunlikely(rc == -1))
		return -1;
	rc = so_ctlcursor_next(c);
	if (srunlikely(rc == -1))
		return -1;
	c->ready = 1;
	return 0;
}

soobj *so_ctlcursor_new(void *o)
{
	so *e = o;
	soctlcursor *c = sr_malloc(&e->a_ctlcursor, sizeof(soctlcursor));
	if (srunlikely(c == NULL)) {
		sr_error(&e->error, "%s", "memory allocation failed");
		return NULL;
	}
	so_objinit(&c->o, SOCTLCURSOR, &soctlcursorif, &e->o);
	c->pos = NULL;
	c->v = NULL;
	c->ready = 0;
	sr_bufinit(&c->dump);
	int rc = so_ctlcursor_open(c);
	if (srunlikely(rc == -1)) {
		so_objdestroy(&c->o);
		return NULL;
	}
	so_objindex_unregister(&e->ctlcursor, &c->o);
	return &c->o;
}
#line 1 "sophia/sophia/so_cursor.c"

/*
 * sophia databaso
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD Licenso
*/










static void*
so_cursorobj(soobj *obj, va_list args srunused)
{
	socursor *c = (socursor*)obj;
	if (srunlikely(! so_vhas(&c->v)))
		return NULL;
	return &c->v;
}

static inline int
so_cursorseek(socursor *c, void *key, int keysize)
{
	siquery q;
	si_queryopen(&q, &c->db->r, &c->cache,
	             &c->db->index, c->order, c->t.vlsn,
	             key, keysize);
	int rc = si_query(&q);
	so_vrelease(&c->v);
	if (rc == 1) {
		assert(q.result.v != NULL);
		sv result;
		rc = si_querydup(&q, &result);
		if (srunlikely(rc == -1)) {
			si_queryclose(&q);
			return -1;
		}
		so_vput(&c->v, &result);
		so_vimmutable(&c->v);
	}
	si_queryclose(&q);
	return rc;
}

static int
so_cursordestroy(soobj *o, va_list args srunused)
{
	socursor *c = (socursor*)o;
	so *e = so_of(o);
	sx_end(&c->t);
	si_cachefree(&c->cache, &c->db->r);
	if (c->key) {
		so_objdestroy(c->key);
		c->key = NULL;
	}
	so_vrelease(&c->v);
	so_objindex_unregister(&c->db->cursor, &c->o);
	sr_free(&e->a_cursor, c);
	return 0;
}

static void*
so_cursorget(soobj *o, va_list args srunused)
{
	socursor *c = (socursor*)o;
	if (srunlikely(c->ready)) {
		c->ready = 0;
		return &c->v;
	}
	if (srunlikely(c->order == SR_STOP))
		return 0;
	if (srunlikely(! so_vhas(&c->v)))
		return 0;
	int rc = so_cursorseek(c, svkey(&c->v.v), svkeysize(&c->v.v));
	if (srunlikely(rc <= 0))
		return NULL;
	return &c->v;
}

static void*
so_cursortype(soobj *o srunused, va_list args srunused) {
	return "cursor";
}

static soobjif socursorif =
{
	.ctl      = NULL,
	.open     = NULL,
	.destroy  = so_cursordestroy,
	.error    = NULL,
	.set      = NULL,
	.get      = so_cursorget,
	.del      = NULL,
	.drop     = NULL,
	.begin    = NULL,
	.prepare  = NULL,
	.commit   = NULL,
	.cursor   = NULL,
	.object   = so_cursorobj,
	.type     = so_cursortype
};

soobj *so_cursornew(sodb *db, uint64_t vlsn, va_list args)
{
	so *e = so_of(&db->o);
	soobj *keyobj = va_arg(args, soobj*);

	/* validate call */
	sov *o = (sov*)keyobj;
	if (srunlikely(o->o.id != SOV)) {
		sr_error(&e->error, "%s", "bad arguments");
		return NULL;
	}

	/* prepare cursor */
	socursor *c = sr_malloc(&e->a_cursor, sizeof(socursor));
	if (srunlikely(c == NULL)) {
		sr_error(&e->error, "%s", "memory allocation failed");
		goto error;
	}
	so_objinit(&c->o, SOCURSOR, &socursorif, &e->o);
	c->key   = keyobj;
	c->db    = db;
	c->ready = 0;
	c->order = o->order;
	so_vinit(&c->v, e, &db->o);
	si_cacheinit(&c->cache, &e->a_cursorcache);

	/* open cursor */
	void *key = svkey(&o->v);
	uint32_t keysize = svkeysize(&o->v);
	if (keysize == 0)
		key = NULL;
	sx_begin(&e->xm, &c->t, vlsn);
	int rc = so_cursorseek(c, key, keysize);
	if (srunlikely(rc == -1)) {
		sx_end(&c->t);
		goto error;
	}

	/* ensure correct iteration */
	srorder next = SR_GTE;
	switch (c->order) {
	case SR_LT:
	case SR_LTE:    next = SR_LT;
		break;
	case SR_GT:
	case SR_GTE:    next = SR_GT;
		break;
	case SR_RANDOM: next = SR_STOP;
		break;
	default: assert(0);
	}
	c->order = next;
	if (rc == 1)
		c->ready = 1;

	so_objindex_register(&db->cursor, &c->o);
	return &c->o;
error:
	if (keyobj)
		so_objdestroy(keyobj);
	if (c)
		sr_free(&e->a_cursor, c);
	return NULL;
}
#line 1 "sophia/sophia/so_db.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/










static int
so_dbctl_init(sodbctl *c, char *name, void *db)
{
	memset(c, 0, sizeof(*c));
	sodb *o = db;
	so *e = so_of(&o->o);
	c->name = sr_strdup(&e->a, name);
	if (srunlikely(c->name == NULL)) {
		sr_error(&e->error, "%s", "memory allocation failed");
		return -1;
	}
	c->parent  = db;
	c->created = 0;
	c->sync    = 1;
	sr_cmpset(&c->cmp, "string");
	return 0;
}

static int
so_dbctl_free(sodbctl *c)
{
	sodb *o = c->parent;
	so *e = so_of(&o->o);
	if (so_dbactive(o))
		return -1;
	if (c->name) {
		sr_free(&e->a, c->name);
		c->name = NULL;
	}
	if (c->path) {
		sr_free(&e->a, c->path);
		c->path = NULL;
	}
	return 0;
}

static int
so_dbctl_validate(sodbctl *c)
{
	sodb *o = c->parent;
	so *e = so_of(&o->o);
	if (c->path)
		return 0;
	char path[1024];
	snprintf(path, sizeof(path), "%s/%s", e->ctl.path, c->name);
	c->path = sr_strdup(&e->a, path);
	if (srunlikely(c->path == NULL)) {
		sr_error(&e->error, "%s", "memory allocation failed");
		return -1;
	}
	return 0;
}

static int
so_dbopen(soobj *obj, va_list args srunused)
{
	sodb *o = (sodb*)obj;
	so *e = so_of(&o->o);
	int status = so_status(&o->status);
	if (status == SO_RECOVER)
		goto online;
	if (status != SO_OFFLINE)
		return -1;
	o->r.cmp = &o->ctl.cmp;
	sx_indexset(&o->coindex, o->ctl.id, o->r.cmp);
	int rc = so_dbctl_validate(&o->ctl);
	if (srunlikely(rc == -1))
		return -1;
	rc = so_recoverbegin(o);
	if (srunlikely(rc == -1))
		return -1;
	if (so_status(&e->status) == SO_RECOVER)
		return 0;
online:
	so_recoverend(o);
	rc = so_scheduler_add(&e->sched, o);
	if (srunlikely(rc == -1))
		return -1;
	return 0;
}

static int
so_dbdestroy(soobj *obj, va_list args srunused)
{
	sodb *o = (sodb*)obj;
	so *e = so_of(&o->o);
	so_statusset(&o->status, SO_SHUTDOWN);
	int rcret = 0;
	int rc;
	rc = so_scheduler_del(&e->sched, o);
	if (srunlikely(rc == -1))
		rcret = -1;
	rc = so_objindex_destroy(&o->cursor);
	if (srunlikely(rc == -1))
		rcret = -1;
	sx_indexfree(&o->coindex, &e->xm);
	rc = si_close(&o->index, &o->r);
	if (srunlikely(rc == -1))
		rcret = -1;
	so_dbctl_free(&o->ctl);
	sd_cfree(&o->dc, &o->r);
	so_statusfree(&o->status);
	so_objindex_unregister(&e->db, &o->o);
	sr_free(&e->a_db, o);
	return rcret;
}

static int
so_dberror(soobj *obj, va_list args srunused)
{
	sodb *o = (sodb*)obj;
	int status = so_status(&o->status);
	if (status == SO_MALFUNCTION)
		return 1;
	return 0;
}

static int
so_dbset(soobj *obj, va_list args)
{
	sodb *o = (sodb*)obj;
	return so_txdbset(o, SVSET, args);
}

static void*
so_dbget(soobj *obj, va_list args)
{
	sodb *o = (sodb*)obj;
	return so_txdbget(o, 0, args);
}

static int
so_dbdel(soobj *obj, va_list args)
{
	sodb *o = (sodb*)obj;
	return so_txdbset(o, SVDELETE, args);
}

static void*
so_dbcursor(soobj *o, va_list args)
{
	sodb *db = (sodb*)o;
	return so_cursornew(db, 0, args);
}

static void*
so_dbobj(soobj *obj, va_list args srunused)
{
	sodb *o = (sodb*)obj;
	so *e = so_of(&o->o);
	return so_vnew(e, obj);
}

static void*
so_dbtype(soobj *o srunused, va_list args srunused) {
	return "database";
}

static soobjif sodbif =
{
	.ctl      = NULL,
	.open     = so_dbopen,
	.destroy  = so_dbdestroy,
	.error    = so_dberror,
	.set      = so_dbset,
	.get      = so_dbget,
	.del      = so_dbdel,
	.drop     = NULL,
	.begin    = NULL,
	.prepare  = NULL,
	.commit   = NULL,
	.cursor   = so_dbcursor,
	.object   = so_dbobj,
	.type     = so_dbtype
};

soobj *so_dbnew(so *e, char *name)
{
	sodb *o = sr_malloc(&e->a_db, sizeof(sodb));
	if (srunlikely(o == NULL)) {
		sr_error(&e->error, "%s", "memory allocation failed");
		return NULL;
	}
	memset(o, 0, sizeof(*o));
	so_objinit(&o->o, SODB, &sodbif, &e->o);
	so_objindex_init(&o->cursor);
	so_statusinit(&o->status);
	so_statusset(&o->status, SO_OFFLINE);
	o->r     = e->r;
	o->r.cmp = &o->ctl.cmp;
	int rc = so_dbctl_init(&o->ctl, name, o);
	if (srunlikely(rc == -1)) {
		sr_free(&e->a_db, o);
		return NULL;
	}
	rc = si_init(&o->index, &o->r, &e->quota);
	if (srunlikely(rc == -1)) {
		sr_free(&e->a_db, o);
		so_dbctl_free(&o->ctl);
		return NULL;
	}
	o->ctl.id = sr_seq(&e->seq, SR_DSNNEXT);
	sx_indexinit(&o->coindex, o);
	sd_cinit(&o->dc, &o->r);
	return &o->o;
}

soobj *so_dbmatch(so *e, char *name)
{
	srlist *i;
	sr_listforeach(&e->db.list, i) {
		sodb *db = (sodb*)srcast(i, soobj, link);
		if (strcmp(db->ctl.name, name) == 0)
			return &db->o;
	}
	return NULL;
}

soobj *so_dbmatch_id(so *e, uint32_t id)
{
	srlist *i;
	sr_listforeach(&e->db.list, i) {
		sodb *db = (sodb*)srcast(i, soobj, link);
		if (db->ctl.id == id)
			return &db->o;
	}
	return NULL;
}

int so_dbmalfunction(sodb *o)
{
	so_statusset(&o->status, SO_MALFUNCTION);
	return -1;
}
#line 1 "sophia/sophia/so_recover.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/










int so_recoverbegin(sodb *db)
{
	so_statusset(&db->status, SO_RECOVER);
	so *e = so_of(&db->o);
	/* open and recover repository */
	siconf *c = &db->indexconf;
	c->node_size      = e->ctl.node_size;
	c->node_page_size = e->ctl.page_size;
	c->path_backup    = e->ctl.backup_path;
	c->path           = db->ctl.path;
	c->name           = db->ctl.name;
	c->sync           = db->ctl.sync;
	int rc = si_open(&db->index, &db->r, &db->indexconf);
	if (srunlikely(rc == -1))
		goto error;
	db->ctl.created = rc;
	return 0;
error:
	so_dbmalfunction(db);
	return -1;
}

int so_recoverend(sodb *db)
{
	so_statusset(&db->status, SO_ONLINE);
	return 0;
}

static inline int
so_recoverlog(so *e, sl *log)
{
	soobj *transaction = NULL;
	sodb *db = NULL;
	sriter i;
	sr_iterinit(&i, &sl_iter, &e->r);
	int rc = sr_iteropen(&i, &log->file, 1);
	if (srunlikely(rc == -1))
		return -1;
	for (;;)
	{
		sv *v = sr_iterof(&i);
		if (srunlikely(v == NULL))
			break;

		/* reply transaction */
		uint64_t lsn = svlsn(v);
		transaction = so_objbegin(&e->o);
		if (srunlikely(transaction == NULL))
			goto error;

		while (sr_iterhas(&i)) {
			v = sr_iterof(&i);
			assert(svlsn(v) == lsn);
			/* match a database */
			uint32_t dsn = sl_vdsn(v);
			if (db == NULL || db->ctl.id != dsn)
				db = (sodb*)so_dbmatch_id(e, dsn);
			if (srunlikely(db == NULL)) {
				sr_malfunction(&e->error, "%s",
				               "database id %" PRIu32 "is not declared", dsn);
				goto rlb;
			}
			void *o = so_objobject(&db->o);
			if (srunlikely(o == NULL))
				goto rlb;
			so_objset(o, "key", svkey(v), svkeysize(v));
			so_objset(o, "value", svvalue(v), svvaluesize(v));
			so_objset(o, "log", log);
			if (svflags(v) == SVSET)
				rc = so_objset(transaction, o);
			else
			if (svflags(v) == SVDELETE)
				rc = so_objdelete(transaction, o);
			if (srunlikely(rc == -1))
				goto rlb;
			sr_gcmark(&log->gc, 1);
			sr_iternext(&i);
		}
		if (srunlikely(sl_itererror(&i)))
			goto rlb;

		rc = so_objprepare(transaction, lsn);
		if (srunlikely(rc != 0))
			goto error;
		rc = so_objcommit(transaction);
		if (srunlikely(rc != 0))
			goto error;
		rc = sl_itercontinue(&i);
		if (srunlikely(rc == -1))
			goto error;
		if (rc == 0)
			break;
	}
	sr_iterclose(&i);
	return 0;
rlb:
	so_objdestroy(transaction);
error:
	sr_iterclose(&i);
	return -1;
}

static inline int
so_recoverlogpool(so *e)
{
	srlist *i;
	sr_listforeach(&e->lp.list, i) {
		sl *log = srcast(i, sl, link);
		int rc = so_recoverlog(e, log);
		if (srunlikely(rc == -1))
			return -1;
		sr_gccomplete(&log->gc);
	}
	return 0;
}

int so_recover(so *e)
{
	slconf *lc = &e->lpconf;
	lc->enable         = e->ctl.log_enable;
	lc->path           = e->ctl.log_path;
	lc->rotatewm       = e->ctl.log_rotate_wm;
	lc->sync_on_rotate = e->ctl.log_rotate_sync;
	lc->sync_on_write  = e->ctl.log_sync;
	int rc = sl_poolopen(&e->lp, lc);
	if (srunlikely(rc == -1))
		return -1;
	if (e->ctl.two_phase_recover)
		return 0;
	/* recover log files */
	rc = so_recoverlogpool(e);
	if (srunlikely(rc == -1))
		goto error;
	rc = sl_poolrotate(&e->lp);
	if (srunlikely(rc == -1))
		goto error;
	return 0;
error:
	so_statusset(&e->status, SO_MALFUNCTION);
	return -1;
}

int so_recover_repository(so *e)
{
	seconf *ec = &e->seconf;
	ec->path        = e->ctl.path;
	ec->path_create = e->ctl.path_create;
	ec->path_backup = e->ctl.backup_path;
	ec->sync = 0;
	return se_open(&e->se, &e->r, &e->seconf);
}
#line 1 "sophia/sophia/so_scheduler.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/










static inline sizone*
so_zoneof(so *e)
{
	int p = sr_quotaused_percent(&e->quota);
	return si_zonemap(&e->ctl.zones, p);
}

int so_scheduler_branch(void *arg)
{
	sodb *db = arg;
	so *e = so_of(&db->o);
	sizone *z = so_zoneof(e);
	soworker stub;
	so_workerstub_init(&stub, &db->r);
	int rc;
	while (1) {
		uint64_t vlsn = sx_vlsn(&e->xm);
		siplan plan = {
			.explain   = SI_ENONE,
			.plan      = SI_BRANCH,
			.a         = z->branch_wm,
			.b         = 0,
			.c         = 0,
			.node      = NULL
		};
		rc = si_plan(&db->index, &plan);
		if (rc == 0)
			break;
		rc = si_execute(&db->index, &db->r, &stub.dc, &plan, vlsn);
		if (srunlikely(rc == -1))
			break;
	}
	so_workerstub_free(&stub, &db->r);
	return rc;
}

int so_scheduler_compact(void *arg)
{
	sodb *db = arg;
	so *e = so_of(&db->o);
	sizone *z = so_zoneof(e);
	soworker stub;
	so_workerstub_init(&stub, &db->r);
	int rc;
	while (1) {
		uint64_t vlsn = sx_vlsn(&e->xm);
		siplan plan = {
			.explain   = SI_ENONE,
			.plan      = SI_COMPACT,
			.a         = z->compact_wm,
			.b         = 0,
			.c         = 0,
			.node      = NULL
		};
		rc = si_plan(&db->index, &plan);
		if (rc == 0)
			break;
		rc = si_execute(&db->index, &db->r, &stub.dc, &plan, vlsn);
		if (srunlikely(rc == -1))
			break;
	}
	so_workerstub_free(&stub, &db->r);
	return rc;
}

int so_scheduler_checkpoint(void *arg)
{
	so *o = arg;
	soscheduler *s = &o->sched;
	uint64_t lsn = sr_seq(&o->seq, SR_LSN);
	sr_mutexlock(&s->lock);
	s->checkpoint_lsn = lsn;
	s->checkpoint = 1;
	sr_mutexunlock(&s->lock);
	return 0;
}

int so_scheduler_gc(void *arg)
{
	so *o = arg;
	soscheduler *s = &o->sched;
	sr_mutexlock(&s->lock);
	s->gc = 1;
	sr_mutexunlock(&s->lock);
	return 0;
}

int so_scheduler_backup(void *arg)
{
	so *e = arg;
	soscheduler *s = &e->sched;
	if (srunlikely(e->ctl.backup_path == NULL)) {
		sr_error(&e->error, "%s", "backup is not enabled");
		return -1;
	}
	/* begin backup procedure
	 * state 0
	 *
	 * disable log garbage-collection
	*/
	sl_poolgc_enable(&e->lp, 0);
	sr_mutexlock(&s->lock);
	if (srunlikely(s->backup > 0)) {
		sr_mutexunlock(&s->lock);
		sl_poolgc_enable(&e->lp, 1);
		/* in progress */
		return 0;
	}
	uint64_t bsn = sr_seq(&e->seq, SR_BSNNEXT);
	s->backup = 1;
	s->backup_bsn = bsn;
	sr_mutexunlock(&s->lock);
	return 0;
}

static inline int
so_backupstart(soscheduler *s)
{
	so *e = s->env;
	/*
	 * a. create backup_path/<bsn.incomplete> directory
	 * b. create database directories
	 * c. create log directory
	*/
	char path[1024];
	snprintf(path, sizeof(path), "%s/%" PRIu32 ".incomplete",
	         e->ctl.backup_path, s->backup_bsn);
	int rc = sr_filemkdir(path);
	if (srunlikely(rc == -1)) {
		sr_error(&e->error, "backup directory '%s' create error: %s",
		         path, strerror(errno));
		return -1;
	}
	int i = 0;
	while (i < s->count) {
		sodb *db = s->i[i];
		snprintf(path, sizeof(path), "%s/%" PRIu32 ".incomplete/%s",
		         e->ctl.backup_path, s->backup_bsn,
		         db->ctl.name);
		rc = sr_filemkdir(path);
		if (srunlikely(rc == -1)) {
			sr_error(&e->error, "backup directory '%s' create error: %s",
			         path, strerror(errno));
			return -1;
		}
		i++;
	}
	snprintf(path, sizeof(path), "%s/%" PRIu32 ".incomplete/log",
	         e->ctl.backup_path, s->backup_bsn);
	rc = sr_filemkdir(path);
	if (srunlikely(rc == -1)) {
		sr_error(&e->error, "backup directory '%s' create error: %s",
		         path, strerror(errno));
		return -1;
	}
	return 0;
}

static inline int
so_backupcomplete(soscheduler *s, soworker *w)
{
	/*
	 * a. rotate log file
	 * b. copy log files
	 * c. enable log gc
	 * d. rename <bsn.incomplete> into <bsn>
	 * e. set last backup, set COMPLETE
	 */
	so *e = s->env;

	/* force log rotation */
	sr_trace(&w->trace, "%s", "log rotation for backup");
	int rc = sl_poolrotate(&e->lp);
	if (srunlikely(rc == -1))
		return -1;

	/* copy log files */
	sr_trace(&w->trace, "%s", "log files backup");

	char path[1024];
	snprintf(path, sizeof(path), "%s/%" PRIu32 ".incomplete/log",
	         e->ctl.backup_path, s->backup_bsn);
	rc = sl_poolcopy(&e->lp, path, &w->dc.c);
	if (srunlikely(rc == -1)) {
		sr_errorrecover(&e->error);
		return -1;
	}

	/* enable log gc */
	sl_poolgc_enable(&e->lp, 1);

	/* complete backup */
	snprintf(path, sizeof(path), "%s/%" PRIu32 ".incomplete",
	         e->ctl.backup_path, s->backup_bsn);
	char newpath[1024];
	snprintf(newpath, sizeof(newpath), "%s/%" PRIu32,
	         e->ctl.backup_path, s->backup_bsn);
	rc = rename(path, newpath);
	if (srunlikely(rc == -1)) {
		sr_error(&e->error, "backup directory '%s' rename error: %s",
		         path, strerror(errno));
		return -1;
	}

	/* complete */
	s->backup_last = s->backup_bsn;
	s->backup_last_complete = 1;
	s->backup = 0;
	s->backup_bsn = 0;
	return 0;
}

static inline int
so_backuperror(soscheduler *s)
{
	so *e = s->env;
	sl_poolgc_enable(&e->lp, 1);
	s->backup = 0;
	s->backup_last_complete = 0;
	return 0;
}

int so_scheduler_call(void *arg)
{
	so *e = arg;
	soscheduler *s = &e->sched;
	soworker stub;
	so_workerstub_init(&stub, &e->r);
	int rc = so_scheduler(s, &stub);
	so_workerstub_free(&stub, &e->r);
	return rc;
}

int so_scheduler_init(soscheduler *s, void *env)
{
	sr_mutexinit(&s->lock);
	s->workers_branch       = 0;
	s->workers_backup       = 0;
	s->workers_gc           = 0;
	s->rotate               = 0;
	s->i                    = NULL;
	s->count                = 0;
	s->rr                   = 0;
	s->env                  = env;
	s->checkpoint_lsn       = 0;
	s->checkpoint_lsn_last  = 0;
	s->checkpoint           = 0;
	s->age                  = 0;
	s->age_last             = 0;
	s->backup_bsn           = 0;
	s->backup_last          = 0;
	s->backup_last_complete = 0;
	s->backup               = 0;
	s->gc                   = 0;
	s->gc_last              = 0;
	so_workersinit(&s->workers);
	return 0;
}

int so_scheduler_shutdown(soscheduler *s)
{
	so *e = s->env;
	int rcret = 0;
	int rc = so_workersshutdown(&s->workers, &e->r);
	if (srunlikely(rc == -1))
		rcret = -1;
	if (s->i) {
		sr_free(&e->a, s->i);
		s->i = NULL;
	}
	sr_mutexfree(&s->lock);
	return rcret;
}

int so_scheduler_add(soscheduler *s , void *db)
{
	sr_mutexlock(&s->lock);
	so *e = s->env;
	int count = s->count + 1;
	void **i = sr_malloc(&e->a, count * sizeof(void*));
	if (srunlikely(i == NULL)) {
		sr_mutexunlock(&s->lock);
		return -1;
	}
	memcpy(i, s->i, s->count * sizeof(void*));
	i[s->count] = db;
	void *iprev = s->i;
	s->i = i;
	s->count = count;
	sr_mutexunlock(&s->lock);
	if (iprev)
		sr_free(&e->a, iprev);
	return 0;
}

int so_scheduler_del(soscheduler *s, void *db)
{
	if (srunlikely(s->i == NULL))
		return 0;
	sr_mutexlock(&s->lock);
	so *e = s->env;
	int count = s->count - 1;
	if (srunlikely(count == 0)) {
		s->count = 0;
		sr_free(&e->a, s->i);
		s->i = NULL;
		sr_mutexunlock(&s->lock);
		return 0;
	}
	void **i = sr_malloc(&e->a, count * sizeof(void*));
	if (srunlikely(i == NULL)) {
		sr_mutexunlock(&s->lock);
		return -1;
	}
	int j = 0;
	int k = 0;
	while (j < s->count) {
		if (s->i[j] == db) {
			j++;
			continue;
		}
		i[k] = s->i[j];
		k++;
		j++;
	}
	void *iprev = s->i;
	s->i = i;
	s->count = count;
	if (srunlikely(s->rr >= s->count))
		s->rr = 0;
	sr_mutexunlock(&s->lock);
	sr_free(&e->a, iprev);
	return 0;
}

static void *so_worker(void *arg)
{
	soworker *self = arg;
	so *o = self->arg;
	for (;;)
	{
		int rc = so_active(o);
		if (srunlikely(rc == 0))
			break;
		rc = so_scheduler(&o->sched, self);
		if (srunlikely(rc == -1))
			break;
		if (srunlikely(rc == 0))
			sr_sleep(10000000); /* 10ms */
	}
	return NULL;
}

int so_scheduler_run(soscheduler *s)
{
	so *e = s->env;
	int rc;
	rc = so_workersnew(&s->workers, &e->r, e->ctl.threads,
	                   so_worker, e);
	if (srunlikely(rc == -1))
		return -1;
	return 0;
}

static int
so_schedule_plan(soscheduler *s, siplan *plan, sodb **dbret)
{
	int start = s->rr;
	int limit = s->count;
	int i = start;
	int rc_inprogress = 0;
	int rc;
	*dbret = NULL;
first_half:
	while (i < limit) {
		sodb *db = s->i[i];
		if (srunlikely(! so_dbactive(db))) {
			i++;
			continue;
		}
		rc = si_plan(&db->index, plan);
		switch (rc) {
		case 1:
			s->rr = i;
			*dbret = db;
			return 1;
		case 2: rc_inprogress = rc;
		case 0: break;
		}
		i++;
	}
	if (i > start) {
		i = 0;
		limit = start;
		goto first_half;
	}
	s->rr = 0;
	return rc_inprogress;
}

static int
so_schedule(soscheduler *s, sotask *task, soworker *w)
{
	sr_trace(&w->trace, "%s", "schedule");
	si_planinit(&task->plan);

	uint64_t now = sr_utime();
	so *e = s->env;
	sodb *db;
	sizone *zone = so_zoneof(e);
	assert(zone != NULL);

	task->checkpoint_complete = 0;
	task->backup_complete = 0;
	task->rotate = 0;
	task->gc = 0;

	sr_mutexlock(&s->lock);
	/* log gc and rotation */
	if (s->rotate == 0)
	{
		task->rotate = 1;
		s->rotate = 1;
	}

	/* checkpoint */
	int in_progress = 0;
	int rc;
checkpoint:
	if (s->checkpoint) {
		task->plan.plan = SI_CHECKPOINT;
		task->plan.a = s->checkpoint_lsn;
		rc = so_schedule_plan(s, &task->plan, &db);
		switch (rc) {
		case 1:
			s->workers_branch++;
			task->db = db;
			task->gc = 1;
			sr_mutexunlock(&s->lock);
			return 1;
		case 2: /* work in progress */
			in_progress = 1;
			break;
		case 0: /* complete checkpoint */
			s->checkpoint = 0;
			s->checkpoint_lsn_last = s->checkpoint_lsn;
			s->checkpoint_lsn = 0;
			task->checkpoint_complete = 1;
			break;
		}
	}

	/* apply zone policy */
	switch (zone->mode) {
	case 0:  /* compact_index */
	case 1:  /* compact_index + branch_count prio */
		assert(0);
		break;
	case 2:  /* checkpoint */
	{
		if (in_progress) {
			sr_mutexunlock(&s->lock);
			return 0;
		}
		uint64_t lsn = sr_seq(&e->seq, SR_LSN);
		s->checkpoint_lsn = lsn;
		s->checkpoint = 1;
		goto checkpoint;
	}
	default: /* branch + compact */
		assert(zone->mode == 3);
	}

	/* backup */
	if (s->backup && (s->workers_backup < zone->backup_prio))
	{
		/* backup procedure.
		 *
		 * state 0 (start)
		 * -------
		 *
		 * a. disable log gc
		 * b. mark to start backup (state 1)
		 *
		 * state 1 (background, delayed start)
		 * -------
		 *
		 * a. create backup_path/<bsn.incomplete> directory
		 * b. create database directories
		 * c. create log directory
		 * d. state 2
		 *
		 * state 2 (background, copy)
		 * -------
		 *
		 * a. schedule and execute node backup which bsn < backup_bsn
		 * b. state 3
		 *
		 * state 3 (background, completion)
		 * -------
		 *
		 * a. rotate log file
		 * b. copy log files
		 * c. enable log gc, schedule gc
		 * d. rename <bsn.incomplete> into <bsn>
		 * e. set last backup, set COMPLETE
		 *
		*/
		if (s->backup == 1) {
			/* state 1 */
			rc = so_backupstart(s);
			if (srunlikely(rc == -1)) {
				so_backuperror(s);
				goto backup_error;
			}
			s->backup = 2;
		}
		/* state 2 */
		task->plan.plan = SI_BACKUP;
		task->plan.a = s->backup_bsn;
		rc = so_schedule_plan(s, &task->plan, &db);
		switch (rc) {
		case 1:
			s->workers_backup++;
			task->db = db;
			sr_mutexunlock(&s->lock);
			return 1;
		case 2: /* work in progress */
			break;
		case 0: /* state 3 */
			rc = so_backupcomplete(s, w);
			if (srunlikely(rc == -1)) {
				so_backuperror(s);
				goto backup_error;
			}
			task->gc = 1;
			task->backup_complete = 1;
			break;
		}
backup_error:;
	}

	/* garbage-collection */
	if (s->gc) {
		if (s->workers_gc < zone->gc_prio) {
			task->plan.plan = SI_GC;
			task->plan.a = sx_vlsn(&e->xm);
			task->plan.b = zone->gc_wm;
			rc = so_schedule_plan(s, &task->plan, &db);
			switch (rc) {
			case 1:
				s->workers_gc++;
				task->db = db;
				sr_mutexunlock(&s->lock);
				return 1;
			case 2: /* work in progress */
				break;
			case 0: /* state 3 */
				s->gc = 0;
				s->gc_last = now;
				break;
			}
		}
	} else {
		if (zone->gc_prio && zone->gc_period) {
			if ( (now - s->gc_last) >= (zone->gc_period * 1000000) ) {
				s->gc = 1;
			}
		}
	}

	/* index aging */
	if (s->age) {
		if (s->workers_branch < zone->branch_prio) {
			task->plan.plan = SI_AGE;
			task->plan.a = zone->branch_age * 1000000; /* ms */
			task->plan.b = zone->branch_age_wm;
			rc = so_schedule_plan(s, &task->plan, &db);
			switch (rc) {
			case 1:
				s->workers_branch++;
				task->db = db;
				sr_mutexunlock(&s->lock);
				return 1;
			case 0:
				s->age = 0;
				s->age_last = now;
				break;
			}
		}
	} else {
		if (zone->branch_prio && zone->branch_age_period) {
			if ( (now - s->age_last) >= (zone->branch_age_period * 1000000) ) {
				s->age = 1;
			}
		}
	}

	/* branching */
	if (s->workers_branch < zone->branch_prio)
	{
		/* schedule branch task using following
		 * priority:
		 *
		 * a. peek node with the largest in-memory index
		 *    which is equal or greater then branch
		 *    watermark.
		 *    If nothing is found, stick to b.
		 *
		 * b. peek node with the largest in-memory index,
		 *    which has oldest update time.
		 *
		 * c. if no branch work is needed, schedule a
		 *    compaction job
		 *
		 */
		task->plan.plan = SI_BRANCH;
		task->plan.a = zone->branch_wm;
		rc = so_schedule_plan(s, &task->plan, &db);
		if (rc == 1) {
			s->workers_branch++;
			task->db = db;
			task->gc = 1;
			sr_mutexunlock(&s->lock);
			return 1;
		}
	}

	/* compaction */
	task->plan.plan = SI_COMPACT;
	task->plan.a = zone->compact_wm;
	rc = so_schedule_plan(s, &task->plan, &db);
	if (rc == 1) {
		task->db = db;
		sr_mutexunlock(&s->lock);
		return 1;
	}

	sr_mutexunlock(&s->lock);
	return 0;
}

static int
so_gc(soscheduler *s, soworker *w)
{
	sr_trace(&w->trace, "%s", "log gc");
	so *e = s->env;
	int rc = sl_poolgc(&e->lp);
	if (srunlikely(rc == -1))
		return -1;
	return 0;
}

static int
so_rotate(soscheduler *s, soworker *w)
{
	sr_trace(&w->trace, "%s", "log rotation");
	so *e = s->env;
	int rc = sl_poolrotate_ready(&e->lp, e->ctl.log_rotate_wm);
	if (rc) {
		rc = sl_poolrotate(&e->lp);
		if (srunlikely(rc == -1))
			return -1;
	}
	return 0;
}

static int
so_execute(sotask *t, soworker *w)
{
	si_plannertrace(&t->plan, &w->trace);
	sodb *db = t->db;
	so *e = (so*)db->o.env;
	uint64_t vlsn = sx_vlsn(&e->xm);
	return si_execute(&db->index, &db->r, &w->dc, &t->plan, vlsn);
}

static int
so_complete(soscheduler *s, sotask *t)
{
	sr_mutexlock(&s->lock);
	switch (t->plan.plan) {
	case SI_BRANCH:
	case SI_AGE:
	case SI_CHECKPOINT:
		s->workers_branch--;
		break;
	case SI_BACKUP:
		s->workers_backup--;
		break;
	case SI_GC:
		s->workers_gc--;
		break;
	}
	if (t->rotate == 1)
		s->rotate = 0;
	sr_mutexunlock(&s->lock);
	return 0;
}

int so_scheduler(soscheduler *s, soworker *w)
{
	sotask task;
	int rc = so_schedule(s, &task, w);
	int job = rc;
	if (task.rotate) {
		rc = so_rotate(s, w);
		if (srunlikely(rc == -1))
			goto error;
	}
	so *e = s->env;
	if (task.checkpoint_complete) {
		sr_triggerrun(&e->ctl.checkpoint_on_complete, &e->o);
	}
	if (task.backup_complete) {
		sr_triggerrun(&e->ctl.backup_on_complete, &e->o);
	}
	if (job) {
		rc = so_execute(&task, w);
		if (srunlikely(rc == -1)) {
			if (task.plan.plan != SI_BACKUP) {
				if (task.db)
					so_dbmalfunction(task.db);
				goto error;
			}
			sr_mutexlock(&s->lock);
			so_backuperror(s);
			sr_mutexunlock(&s->lock);
		}
	}
	if (task.gc) {
		rc = so_gc(s, w);
		if (srunlikely(rc == -1))
			goto error;
	}
	so_complete(s, &task);
	sr_trace(&w->trace, "%s", "sleep");
	return job;
error:
	sr_trace(&w->trace, "%s", "malfunction");
	return -1;
}
#line 1 "sophia/sophia/so_snapshot.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/










static int
so_snapshotfree(sosnapshot *s)
{
	so *e = so_of(&s->o);
	sx_end(&s->t);
	if (srlikely(s->name)) {
		sr_free(&e->a, s->name);
		s->name = NULL;
	}
	sr_free(&e->a_snapshot, s);
	return 0;
}

static int
so_snapshotdestroy(soobj *o, va_list args srunused)
{
	sosnapshot *s = (sosnapshot*)o;
	so *e = so_of(o);
	so_objindex_unregister(&e->snapshot, &s->o);
	so_snapshotfree(s);
	return 0;
}

static void*
so_snapshotget(soobj *o, va_list args)
{
	sosnapshot *s = (sosnapshot*)o;
	so *e = so_of(o);
	va_list va;
	va_copy(va, args);
	sov *v = va_arg(va, sov*);
	va_end(va);
	if (srunlikely(v->o.id != SOV)) {
		sr_error(&e->error, "%s", "bad arguments");
		return NULL;
	}
	sodb *db = (sodb*)v->parent;
	return so_txdbget(db, s->vlsn, args);
}

static void*
so_snapshotcursor(soobj *o, va_list args)
{
	sosnapshot *s = (sosnapshot*)o;
	so *e = so_of(o);
	va_list va;
	va_copy(va, args);
	sov *v = va_arg(va, sov*);
	va_end(va);
	if (srunlikely(v->o.id != SOV))
		goto error;
	if (srunlikely(v->parent == NULL || v->parent->id != SODB))
		goto error;
	sodb *db = (sodb*)v->parent;
	return so_cursornew(db, s->vlsn, args);
error:
	sr_error(&e->error, "%s", "bad arguments");
	return NULL;
}

static void*
so_snapshottype(soobj *o srunused, va_list args srunused) {
	return "snapshot";
}

static soobjif sosnapshotif =
{
	.ctl      = NULL,
	.open     = NULL,
	.destroy  = so_snapshotdestroy,
	.error    = NULL,
	.set      = NULL,
	.get      = so_snapshotget,
	.del      = NULL,
	.drop     = so_snapshotdestroy,
	.begin    = NULL,
	.prepare  = NULL,
	.commit   = NULL,
	.cursor   = so_snapshotcursor,
	.object   = NULL,
	.type     = so_snapshottype
};

soobj *so_snapshotnew(so *e, uint64_t vlsn, char *name)
{
	srlist *i;
	sr_listforeach(&e->snapshot.list, i) {
		sosnapshot *s = (sosnapshot*)srcast(i, soobj, link);
		if (srunlikely(strcmp(s->name, name) == 0)) {
			sr_error(&e->error, "snapshot '%s' already exists", name);
			return NULL;
		}
	}
	sosnapshot *s = sr_malloc(&e->a_snapshot, sizeof(sosnapshot));
	if (srunlikely(s == NULL)) {
		sr_error(&e->error, "%s", "memory allocation failed");
		return NULL;
	}
	so_objinit(&s->o, SOSNAPSHOT, &sosnapshotif, &e->o);
	s->vlsn = vlsn;
	s->name = sr_strdup(&e->a, name);
	if (srunlikely(s->name == NULL)) {
		sr_free(&e->a_snapshot, s);
		sr_error(&e->error, "%s", "memory allocation failed");
		return NULL;
	}
	sx_begin(&e->xm, &s->t, vlsn);
	return &s->o;
}

int so_snapshotupdate(sosnapshot *s)
{
	so *e = so_of(&s->o);
	sx_end(&s->t);
	sx_begin(&e->xm, &s->t, s->vlsn);
	return 0;
}
#line 1 "sophia/sophia/so_tx.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/










int so_txdbset(sodb *db, uint8_t flags, va_list args)
{
	/* validate call */
	sov *o = va_arg(args, sov*);
	so *e = so_of(&db->o);
	if (srunlikely(o->o.id != SOV)) {
		sr_error(&e->error, "%s", "bad arguments");
		return -1;
	}
	sv *ov = &o->v;
	if (srunlikely(ov->v == NULL)) {
		sr_error(&e->error, "%s", "bad arguments");
		goto error;
	}
	soobj *parent = o->parent;
	if (srunlikely(parent != &db->o)) {
		sr_error(&e->error, "%s", "bad object parent");
		goto error;
	}
	int status = so_status(&db->status);
	if (srunlikely(! so_statusactive_is(status)))
		goto error;
	if (srunlikely(status == SO_RECOVER))
		goto error;

	/* prepare object */
	svlocal l;
	l.flags       = flags;
	l.lsn         = 0;
	l.key         = svkey(ov);
	l.keysize     = svkeysize(ov);
	l.value       = svvalue(ov);
	l.valuesize   = svvaluesize(ov);
	sv vp;
	svinit(&vp, &sv_localif, &l, NULL);

	/* ensure quota */
	sr_quota(&e->quota, SR_QADD, sv_vsizeof(&vp));

	/* concurrency */
	sxstate s = sx_setstmt(&e->xm, &db->coindex, &vp);
	int rc = 1; /* rlb */
	switch (s) {
	case SXLOCK: rc = 2;
	case SXROLLBACK:
		so_objdestroy(&o->o);
		return rc;
	default:
		break;
	}
	svv *v = sv_valloc(db->r.a, &vp);
	if (srunlikely(v == NULL)) {
		sr_error(&e->error, "%s", "memory allocation failed");
		goto error;
	}

	/* log write */
	svlogv lv;
	lv.id = db->ctl.id;
	lv.next = 0;
	svinit(&lv.v, &sv_vif, v, NULL);
	svlog log;
	sv_loginit(&log);
	sv_logadd(&log, db->r.a, &lv, db);
	svlogindex *logindex = (svlogindex*)log.index.s;
	sltx tl;
	sl_begin(&e->lp, &tl);
	sl_prepare(&e->lp, &log, 0);
	rc = sl_write(&tl, &log);
	if (srunlikely(rc == -1)) {
		sl_rollback(&tl);
		goto error;
	}
	v->log = tl.l;
	sl_commit(&tl);

	/* commit */
	uint64_t vlsn = sx_vlsn(&e->xm);
	uint64_t now = sr_utime();
	sitx tx;
	si_begin(&tx, &db->r, &db->index, vlsn, now, &log, logindex);
	si_write(&tx, 0);
	si_commit(&tx);

	so_objdestroy(&o->o);
	return 0;
error:
	so_objdestroy(&o->o);
	return -1;
}

void *so_txdbget(sodb *db, uint64_t vlsn, va_list args)
{
	so *e = so_of(&db->o);
	/* validate call */
	sov *o = va_arg(args, sov*);
	if (srunlikely(o->o.id != SOV)) {
		sr_error(&e->error, "%s", "bad arguments");
		return NULL;
	}
	uint32_t keysize = svkeysize(&o->v);
	void *key = svkey(&o->v);
	if (srunlikely(key == NULL)) {
		sr_error(&e->error, "%s", "bad arguments");
		goto error;
	}
	soobj *parent = o->parent;
	if (srunlikely(parent != &db->o)) {
		sr_error(&e->error, "%s", "bad object parent");
		goto error;
	}
	if (srunlikely(! so_dbactive(db)))
		goto error;

	sx_getstmt(&e->xm, &db->coindex);
	if (srlikely(vlsn == 0))
		vlsn = sr_seq(db->r.seq, SR_LSN);

	sicache cache;
	si_cacheinit(&cache, &e->a_cursorcache);
	siquery q;
	si_queryopen(&q, &db->r, &cache, &db->index,
	             SR_EQ, vlsn, key, keysize);
	sv result;
	int rc = si_query(&q);
	if (rc == 1) {
		rc = si_querydup(&q, &result);
	}
	si_queryclose(&q);
	si_cachefree(&cache, &db->r);

	so_objdestroy(&o->o);
	if (srunlikely(rc <= 0))
		return NULL;
	soobj *ret = so_vdup(e, &db->o, &result);
	if (srunlikely(ret == NULL))
		sv_vfree(&e->a, (svv*)result.v);
	return ret;
error:
	so_objdestroy(&o->o);
	return NULL;
}

static int
so_txdo(soobj *obj, uint8_t flags, va_list args)
{
	sotx *t = (sotx*)obj;
	so *e = so_of(obj);

	/* validate call */
	sov *o = va_arg(args, sov*);
	if (srunlikely(o->o.id != SOV)) {
		sr_error(&e->error, "%s", "bad arguments");
		return -1;
	}
	sv *ov = &o->v;
	if (srunlikely(ov->v == NULL)) {
		sr_error(&e->error, "%s", "bad arguments");
		goto error;
	}
	soobj *parent = o->parent;
	if (parent == NULL || parent->id != SODB) {
		sr_error(&e->error, "%s", "bad object parent");
		goto error;
	}
	sodb *db = (sodb*)parent;
	if (t->t.s == SXPREPARE) {
		sr_error(&e->error, "%s", "transaction is in 'prepare' state (read-only)");
		goto error;
	}
	if (srunlikely(! so_dbactive(db)))
		goto error;

	/* prepare object */
	svlocal l;
	l.flags       = flags;
	l.lsn         = svlsn(ov);
	l.key         = svkey(ov);
	l.keysize     = svkeysize(ov);
	l.value       = svvalue(ov);
	l.valuesize   = svvaluesize(ov);
	sv vp;
	svinit(&vp, &sv_localif, &l, NULL);

	/* ensure quota */
	sr_quota(&e->quota, SR_QADD, sv_vsizeof(&vp));

	svv *v = sv_valloc(db->r.a, &vp);
	if (srunlikely(v == NULL)) {
		sr_error(&e->error, "%s", "memory allocation failed");
		goto error;
	}
	v->log = o->log;
	int rc = sx_set(&t->t, &db->coindex, v);
	so_objdestroy(&o->o);
	return rc;
error:
	so_objdestroy(&o->o);
	return -1;
}

static int
so_txset(soobj *o, va_list args)
{
	return so_txdo(o, SVSET, args);
}

static int
so_txdelete(soobj *o, va_list args)
{
	return so_txdo(o, SVDELETE, args);
}

static void*
so_txget(soobj *obj, va_list args)
{
	sotx *t = (sotx*)obj;
	so *e = so_of(obj);

	/* validate call */
	sov *o = va_arg(args, sov*);
	if (srunlikely(o->o.id != SOV)) {
		sr_error(&e->error, "%s", "bad arguments");
		return NULL;
	}
	void *key = svkey(&o->v);
	if (srunlikely(key == NULL)) {
		sr_error(&e->error, "%s", "bad arguments");
		return NULL;
	}
	soobj *parent = o->parent;
	if (parent == NULL || parent->id != SODB) {
		sr_error(&e->error, "%s", "bad object parent");
		goto error;
	}
	sodb *db = (sodb*)parent;
	if (srunlikely(! so_dbactive(db)))
		goto error;

	soobj *ret;
	sv result;
	int rc = sx_get(&t->t, &db->coindex, &o->v, &result);
	switch (rc) {
	case -1:
	case  2: /* delete */
		so_objdestroy(&o->o);
		return NULL;
	case  1:
		ret = so_vdup(e, &db->o, &result);
		if (srunlikely(ret == NULL))
			sv_vfree(&e->a, (svv*)result.v);
		so_objdestroy(&o->o);
		return ret;
	}

	sicache cache;
	si_cacheinit(&cache, &e->a_cursorcache);
	siquery q;
	si_queryopen(&q, &db->r, &cache, &db->index,
	             SR_EQ, t->t.vlsn,
	             key, svkeysize(&o->v));
	rc = si_query(&q);
	if (rc == 1) {
		rc = si_querydup(&q, &result);
	}
	si_queryclose(&q);
	si_cachefree(&cache, &db->r);

	so_objdestroy(&o->o);
	if (srunlikely(rc <= 0))
		return NULL;
	ret = so_vdup(e, &db->o, &result);
	if (srunlikely(ret == NULL))
		sv_vfree(&e->a, (svv*)result.v);
	return ret;
error:
	so_objdestroy(&o->o);
	return NULL;
}

static inline void
so_txend(sotx *t)
{
	so *e = so_of(&t->o);
	so_objindex_unregister(&e->tx, &t->o);
	sr_free(&e->a_tx, t);
}

static int
so_txrollback(soobj *o, va_list args srunused)
{
	sotx *t = (sotx*)o;
	sx_rollback(&t->t);
	sx_end(&t->t);
	so_txend(t);
	return 0;
}

static sxstate
so_txprepare_trigger(sx *t, sv *v, void *arg0, void *arg1)
{
	sotx *te srunused = arg0;
	sodb *db = arg1;
	so *e = so_of(&db->o);
	uint64_t lsn = sr_seq(e->r.seq, SR_LSN);
	if (t->vlsn == lsn)
		return SXPREPARE;
	sicache cache;
	si_cacheinit(&cache, &e->a_cursorcache);
	siquery q;
	si_queryopen(&q, &db->r, &cache, &db->index,
	             SR_UPDATE, t->vlsn,
	             svkey(v), svkeysize(v));
	int rc;
	rc = si_query(&q);
	si_queryclose(&q);
	si_cachefree(&cache, &db->r);
	if (srunlikely(rc))
		return SXROLLBACK;
	return SXPREPARE;
}

static int
so_txprepare(soobj *o, va_list args srunused)
{
	sotx *t = (sotx*)o;
	so *e = so_of(o);
	int status = so_status(&e->status);
	if (srunlikely(! so_statusactive_is(status)))
		return -1;
	if (t->t.s == SXPREPARE)
		return 0;
	/* resolve conflicts */
	sxpreparef prepare_trigger = so_txprepare_trigger;
	if (srunlikely(status == SO_RECOVER))
		prepare_trigger = NULL;
	sxstate s = sx_prepare(&t->t, prepare_trigger, t);
	if (s == SXLOCK)
		return 2;
	if (s == SXROLLBACK) {
		so_objdestroy(&t->o);
		return 1;
	}
	assert(s == SXPREPARE);
	/* assign lsn */
	uint64_t lsn = 0;
	if (status == SO_RECOVER || e->ctl.commit_lsn)
		lsn = va_arg(args, uint64_t);
	sl_prepare(&e->lp, &t->t.log, lsn);
	return 0;
}

static int
so_txcommit(soobj *o, va_list args)
{
	sotx *t = (sotx*)o;
	so *e = so_of(o);
	int status = so_status(&e->status);
	if (srunlikely(! so_statusactive_is(status)))
		return -1;

	/* prepare transaction for commit */
	assert (t->t.s == SXPREPARE || t->t.s == SXREADY);
	int rc;
	if (t->t.s == SXREADY) {
		rc = so_txprepare(o, args);
		if (srunlikely(rc != 0))
			return rc;
	}
	assert(t->t.s == SXPREPARE);

	if (srunlikely(! sv_logcount(&t->t.log))) {
		sx_commit(&t->t);
		sx_end(&t->t);
		so_txend(t);
		return 0;
	}
	sx_commit(&t->t);

	/* log commit */
	if (status == SO_ONLINE) {
		sltx tl;
		sl_begin(&e->lp, &tl);
		rc = sl_write(&tl, &t->t.log);
		if (srunlikely(rc == -1)) {
			sl_rollback(&tl);
			so_objdestroy(&t->o);
			return -1;
		}
		sl_commit(&tl);
	}

	/* prepare commit */
	int check_if_exists;
	uint64_t vlsn;
	if (srunlikely(status == SO_RECOVER)) {
		check_if_exists = 1;
		vlsn = sr_seq(e->r.seq, SR_LSN);
	} else {
		check_if_exists = 0;
		vlsn = sx_vlsn(&e->xm);
	}

	/* multi-index commit */
	uint64_t now = sr_utime();

	svlogindex *i   = (svlogindex*)t->t.log.index.s;
	svlogindex *end = (svlogindex*)t->t.log.index.p;
	while (i < end) {
		sodb *db = i->ptr;
		sitx ti;
		si_begin(&ti, &db->r, &db->index, vlsn, now, &t->t.log, i);
		si_write(&ti, check_if_exists);
		si_commit(&ti);
		i++;
	}
	sx_end(&t->t);

	so_txend(t);
	return 0;
}

static void*
so_txtype(soobj *o srunused, va_list args srunused) {
	return "transaction";
}

static soobjif sotxif =
{
	.ctl      = NULL,
	.open     = NULL,
	.destroy  = so_txrollback,
	.error    = NULL,
	.set      = so_txset,
	.del      = so_txdelete,
	.drop     = so_txrollback,
	.get      = so_txget,
	.begin    = NULL,
	.prepare  = so_txprepare,
	.commit   = so_txcommit,
	.cursor   = NULL,
	.object   = NULL,
	.type     = so_txtype
};

soobj *so_txnew(so *e)
{
	sotx *t = sr_malloc(&e->a_tx, sizeof(sotx));
	if (srunlikely(t == NULL)) {
		sr_error(&e->error, "%s", "memory allocation failed");
		return NULL;
	}
	so_objinit(&t->o, SOTX, &sotxif, &e->o);
	sx_begin(&e->xm, &t->t, 0);
	so_objindex_register(&e->tx, &t->o);
	return &t->o;
}
#line 1 "sophia/sophia/so_v.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/










static int
so_vdestroy(soobj *obj, va_list args srunused)
{
	sov *v = (sov*)obj;
	if (v->flags & SO_VIMMUTABLE)
		return 0;
	so_vrelease(v);
	sr_free(&so_of(obj)->a_v, v);
	return 0;
}

static int
so_vset(soobj *obj, va_list args)
{
	sov *v = (sov*)obj;
	so *e = so_of(obj);
	if (srunlikely(v->flags & SO_VRO)) {
		sr_error(&e->error, "%s", "object is read-only");
		return -1;
	}
	char *name = va_arg(args, char*);
	if (strcmp(name, "key") == 0) {
		if (v->v.i != &sv_localif) {
			sr_error(&e->error, "%s", "bad object operation");
			return -1;
		}
		v->lv.key = va_arg(args, char*);
		v->lv.keysize = va_arg(args, int);
		return 0;
	} else
	if (strcmp(name, "value") == 0) {
		if (v->v.i != &sv_localif) {
			sr_error(&e->error, "%s", "bad object operation");
			return -1;
		}
		v->lv.value = va_arg(args, char*);
		v->lv.valuesize = va_arg(args, int);
		return 0;
	} else
	if (strcmp(name, "log") == 0) {
		v->log = va_arg(args, void*);
		return 0;
	} else
	if (strcmp(name, "order") == 0) {
		char *order = va_arg(args, void*);
		srorder cmp = sr_orderof(order);
		if (srunlikely(cmp == SR_STOP)) {
			sr_error(&e->error, "%s", "bad order name");
			return -1;
		}
		v->order = cmp;
		return 0;
	}
	return -1;
}

static void*
so_vget(soobj *obj, va_list args)
{
	sov *v = (sov*)obj;
	so *e = so_of(obj);
	char *name = va_arg(args, char*);
	if (strcmp(name, "key") == 0) {
		void *key = svkey(&v->v);
		if (srunlikely(key == NULL))
			return NULL;
		int *keysize = va_arg(args, int*);
		if (keysize)
			*keysize = svkeysize(&v->v);
		return key;
	} else
	if (strcmp(name, "value") == 0) {
		void *value = svvalue(&v->v);
		if (srunlikely(value == NULL))
			return NULL;
		int *valuesize = va_arg(args, int*);
		if (valuesize)
			*valuesize = svvaluesize(&v->v);
		return value;
	} else
	if (strcmp(name, "lsn") == 0) {
		uint64_t *lsnp = NULL;
		if (v->v.i == &sv_localif)
			lsnp = &v->lv.lsn;
		else
		if (v->v.i == &sv_vif)
			lsnp = &((svv*)(v->v.v))->lsn;
		else
		if (v->v.i == &sx_vif)
			lsnp = &((sxv*)(v->v.v))->v->lsn;
		else {
			assert(0);
		}
		int *valuesize = va_arg(args, int*);
		if (valuesize)
			*valuesize = sizeof(uint64_t);
		return lsnp;
	} else
	if (strcmp(name, "order") == 0) {
		src order = {
			.name     = "order",
			.value    = sr_ordername(v->order),
			.flags    = SR_CSZ,
			.ptr      = NULL,
			.function = NULL,
			.next     = NULL
		};
		void *o = so_ctlreturn(&order, e);
		if (srunlikely(o == NULL))
			return NULL;
		return o;
	}
	return NULL;
}

static void*
so_vtype(soobj *o srunused, va_list args srunused) {
	return "object";
}

static soobjif sovif =
{
	.ctl      = NULL,
	.open     = NULL,
	.destroy  = so_vdestroy,
	.error    = NULL,
	.set      = so_vset,
	.get      = so_vget,
	.del      = NULL,
	.drop     = NULL,
	.begin    = NULL,
	.prepare  = NULL,
	.commit   = NULL,
	.cursor   = NULL,
	.object   = NULL,
	.type     = so_vtype
};

soobj *so_vinit(sov *v, so *e, soobj *parent)
{
	memset(v, 0, sizeof(*v));
	so_objinit(&v->o, SOV, &sovif, &e->o);
	svinit(&v->v, &sv_localif, &v->lv, NULL);
	v->order = SR_GTE;
	v->parent = parent;
	return &v->o;
}

soobj *so_vnew(so *e, soobj *parent)
{
	sov *v = sr_malloc(&e->a_v, sizeof(sov));
	if (srunlikely(v == NULL)) {
		sr_error(&e->error, "%s", "memory allocation failed");
		return NULL;
	}
	return so_vinit(v, e, parent);
}

soobj *so_vrelease(sov *v)
{
	so *e = so_of(&v->o);
	if (v->flags & SO_VALLOCATED)
		sv_vfree(&e->a, (svv*)v->v.v);
	v->flags = 0;
	v->v.v = NULL;
	return &v->o;
}

soobj *so_vput(sov *o, sv *v)
{
	o->flags = SO_VALLOCATED|SO_VRO;
	o->v = *v;
	return &o->o;
}

soobj *so_vdup(so *e, soobj *parent, sv *v)
{
	sov *ret = (sov*)so_vnew(e, parent);
	if (srunlikely(ret == NULL))
		return NULL;
	ret->flags = SO_VALLOCATED|SO_VRO;
	ret->v = *v;
	return &ret->o;
}

int so_vimmutable(sov *v)
{
	v->flags |= SO_VIMMUTABLE;
	return 0;
}
#line 1 "sophia/sophia/so_worker.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/










int so_workersinit(soworkers *w)
{
	sr_listinit(&w->list);
	w->n = 0;
	return 0;
}

static inline int
so_workershutdown(soworker *w, sr *r)
{
	int rc = sr_threadjoin(&w->t);
	if (srunlikely(rc == -1))
		sr_malfunction(r->e, "failed to join a thread: %s",
		               strerror(errno));
	sd_cfree(&w->dc, r);
	sr_tracefree(&w->trace);
	sr_free(r->a, w);
	return rc;
}

int so_workersshutdown(soworkers *w, sr *r)
{
	int rcret = 0;
	int rc;
	srlist *i, *n;
	sr_listforeach_safe(&w->list, i, n) {
		soworker *p = srcast(i, soworker, link);
		rc = so_workershutdown(p, r);
		if (srunlikely(rc == -1))
			rcret = -1;
	}
	return rcret;
}

static inline soworker*
so_workernew(sr *r, int id, srthreadf f, void *arg)
{
	soworker *p = sr_malloc(r->a, sizeof(soworker));
	if (srunlikely(p == NULL)) {
		sr_malfunction(r->e, "%s", "memory allocation failed");
		return NULL;
	}
	snprintf(p->name, sizeof(p->name), "%d", id);
	p->arg = arg;
	sd_cinit(&p->dc, r);
	sr_listinit(&p->link);
	sr_traceinit(&p->trace);
	sr_trace(&p->trace, "%s", "init");
	int rc = sr_threadnew(&p->t, f, p);
	if (srunlikely(rc == -1)) {
		sr_malfunction(r->e, "failed to create thread: %s",
		               strerror(errno));
		sr_free(r->a, p);
		return NULL;
	}
	return p;
}

int so_workersnew(soworkers *w, sr *r, int n, srthreadf f, void *arg)
{
	int i = 0;
	int id = 0;
	while (i < n) {
		soworker *p = so_workernew(r, id, f, arg);
		if (srunlikely(p == NULL))
			return -1;
		sr_listappend(&w->list, &p->link);
		w->n++;
		i++;
		id++;
	}
	return 0;
}
#line 1 "sophia/sophia/sophia.c"

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/










static inline void
sp_error_unsupported_method(soobj *o, const char *method, ...)
{
	assert(o->env != NULL);
	assert(o->env->id == SOENV);
	va_list args;
	va_start(args, method);
	so *e = (so*)o->env;
	sr_error(&e->error, "unsupported %s(%s) operation",
	         (char*)method,
	         (char*)o->i->type(o, args));
	va_end(args);
}

SP_API void*
sp_env(void)
{
	return so_new();
}

SP_API void*
sp_ctl(void *o, ...)
{
	soobj *obj = o;
	if (srunlikely(obj->i->ctl == NULL)) {
		sp_error_unsupported_method(o, __FUNCTION__);
		return NULL;
	}
	va_list args;
	va_start(args, o);
	so_apilock(obj->env);
	void *h = obj->i->ctl(o, args);
	so_apiunlock(obj->env);
	va_end(args);
	return h;
}

SP_API void*
sp_object(void *o, ...)
{
	soobj *obj = o;
	if (srunlikely(obj->i->object == NULL)) {
		sp_error_unsupported_method(o, __FUNCTION__);
		return NULL;
	}
	va_list args;
	va_start(args, o);
	so_apilock(obj->env);
	void *h = obj->i->object(o, args);
	so_apiunlock(obj->env);
	va_end(args);
	return h;
}

SP_API int
sp_open(void *o, ...)
{
	soobj *obj = o;
	if (srunlikely(obj->i->open == NULL)) {
		sp_error_unsupported_method(o, __FUNCTION__);
		return -1;
	}
	va_list args;
	va_start(args, o);
	so_apilock(obj->env);
	int rc = obj->i->open(o, args);
	so_apiunlock(obj->env);
	va_end(args);
	return rc;
}

SP_API int
sp_destroy(void *o, ...)
{
	soobj *obj = o;
	if (srunlikely(obj->i->destroy == NULL)) {
		sp_error_unsupported_method(o, __FUNCTION__);
		return -1;
	}
	va_list args;
	va_start(args, o);
	soobj *env = obj->env;
	int rc;
	if (srunlikely(env == o)) {
		rc = obj->i->destroy(o, args);
		va_end(args);
		return rc;
	}
	so_apilock(env);
	rc = obj->i->destroy(o, args);
	so_apiunlock(env);
	va_end(args);
	return rc;
}

SP_API int sp_error(void *o, ...)
{
	soobj *obj = o;
	if (srunlikely(obj->i->error == NULL)) {
		sp_error_unsupported_method(o, __FUNCTION__);
		return -1;
	}
	va_list args;
	va_start(args, o);
	so_apilock(obj->env);
	int rc = obj->i->error(o, args);
	so_apiunlock(obj->env);
	va_end(args);
	return rc;
}

SP_API int
sp_set(void *o, ...)
{
	soobj *obj = o;
	if (srunlikely(obj->i->set == NULL)) {
		sp_error_unsupported_method(o, __FUNCTION__);
		return -1;
	}
	va_list args;
	va_start(args, o);
	so_apilock(obj->env);
	int rc = obj->i->set(o, args);
	so_apiunlock(obj->env);
	va_end(args);
	return rc;
}

SP_API void*
sp_get(void *o, ...)
{
	soobj *obj = o;
	if (srunlikely(obj->i->get == NULL)) {
		sp_error_unsupported_method(o, __FUNCTION__);
		return NULL;
	}
	va_list args;
	va_start(args, o);
	so_apilock(obj->env);
	void *h = obj->i->get(o, args);
	so_apiunlock(obj->env);
	va_end(args);
	return h;
}

SP_API int
sp_delete(void *o, ...)
{
	soobj *obj = o;
	if (srunlikely(obj->i->del == NULL)) {
		sp_error_unsupported_method(o, __FUNCTION__);
		return -1;
	}
	soobj *env = obj->env;
	va_list args;
	va_start(args, o);
	so_apilock(env);
	int rc = obj->i->del(o, args);
	so_apiunlock(env);
	va_end(args);
	return rc;
}

SP_API int
sp_drop(void *o, ...)
{
	soobj *obj = o;
	if (srunlikely(obj->i->drop == NULL)) {
		sp_error_unsupported_method(o, __FUNCTION__);
		return -1;
	}
	soobj *env = obj->env;
	va_list args;
	va_start(args, o);
	so_apilock(env);
	int rc = obj->i->drop(o, args);
	so_apiunlock(env);
	va_end(args);
	return rc;
}

SP_API void*
sp_begin(void *o, ...)
{
	soobj *obj = o;
	if (srunlikely(obj->i->begin == NULL)) {
		sp_error_unsupported_method(o, __FUNCTION__);
		return NULL;
	}
	va_list args;
	va_start(args, o);
	so_apilock(obj->env);
	void *h = obj->i->begin(o, args);
	so_apiunlock(obj->env);
	va_end(args);
	return h;
}

SP_API int
sp_prepare(void *o, ...)
{
	soobj *obj = o;
	if (srunlikely(obj->i->prepare == NULL)) {
		sp_error_unsupported_method(o, __FUNCTION__);
		return -1;
	}
	soobj *env = obj->env;
	va_list args;
	va_start(args, o);
	so_apilock(env);
	int rc = obj->i->prepare(o, args);
	so_apiunlock(env);
	va_end(args);
	return rc;
}

SP_API int
sp_commit(void *o, ...)
{
	soobj *obj = o;
	if (srunlikely(obj->i->commit == NULL)) {
		sp_error_unsupported_method(o, __FUNCTION__);
		return -1;
	}
	soobj *env = obj->env;
	va_list args;
	va_start(args, o);
	so_apilock(env);
	int rc = obj->i->commit(o, args);
	so_apiunlock(env);
	va_end(args);
	return rc;
}

SP_API void*
sp_cursor(void *o, ...)
{
	soobj *obj = o;
	if (srunlikely(obj->i->cursor == NULL)) {
		sp_error_unsupported_method(o, __FUNCTION__);
		return NULL;
	}
	va_list args;
	va_start(args, o);
	so_apilock(obj->env);
	void *cursor = obj->i->cursor(o, args);
	so_apiunlock(obj->env);
	va_end(args);
	return cursor;
}

SP_API void *sp_type(void *o, ...)
{
	soobj *obj = o;
	if (srunlikely(obj->i->type == NULL)) {
		sp_error_unsupported_method(o, __FUNCTION__);
		return NULL;
	}
	va_list args;
	va_start(args, o);
	so_apilock(obj->env);
	void *h = obj->i->type(o, args);
	so_apiunlock(obj->env);
	va_end(args);
	return h;
}
/* vim: foldmethod=marker
*/
/* }}} */
