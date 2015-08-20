#ifndef SY_CONF_H_
#define SY_CONF_H_

/*
 * sophia database
 * sphia.org
 *
 * Copyright (c) Dmitry Simonenko
 * BSD License
*/

typedef struct syconf syconf;

struct syconf {
	char *path;
	int   path_create;
	char *path_backup;
	int   sync;
};

#endif
