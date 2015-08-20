#ifndef SD_MERGE_H_
#define SD_MERGE_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct sdmergeconf sdmergeconf;
typedef struct sdmerge sdmerge;

struct sdmergeconf {
	uint32_t size_stream;
	uint64_t size_node;
	uint32_t size_page;
	uint32_t checksum;
	uint32_t compression;
	uint32_t compression_key;
	uint64_t offset;
	uint64_t vlsn;
	uint32_t save_delete;
	uint32_t save_update;
};

struct sdmerge {
	sdindex index;
	ssiter *merge;
	ssiter i;
	uint64_t processed;
	sdmergeconf *conf;
	sr *r;
	sdbuild *build;
};

int sd_mergeinit(sdmerge*, sr*, ssiter*, sdbuild*, svupdate*, sdmergeconf*);
int sd_mergefree(sdmerge*);
int sd_merge(sdmerge*);
int sd_mergecommit(sdmerge*, sdid*);

#endif
