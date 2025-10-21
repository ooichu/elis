/*
 * Copyright (c) 2020 rxi
 * Copyright (c) 2023 ooichu
 *
 * This software may be used free of charge under the MIT license, see "elis.c"
 * for details.
 */

#ifndef ELIS_H
#define ELIS_H

#include <stdio.h>

#define ELIS_VERSION "1.0"

#ifndef ELIS_STACK_SIZE
#define ELIS_STACK_SIZE 256
#endif

#ifndef ELIS_PAGE_SIZE
#define ELIS_PAGE_SIZE 4096
#endif

#ifndef ELIS_NUMBER_TYPE
#define ELIS_NUMBER_TYPE float
#endif

#ifndef ELIS_NUMBER_FORMAT
#define ELIS_NUMBER_FORMAT "%.7g"
#endif

typedef struct elis_State elis_State;
typedef struct elis_Object elis_Object;
typedef struct elis_OnError elis_OnError;
typedef ELIS_NUMBER_TYPE elis_Number;
typedef struct elis_GCHooks elis_GCHooks;

typedef void *(*elis_Allocator)(void *ptr, size_t size, void *udata);
typedef elis_Object *(*elis_CFunction)(elis_State *S, elis_Object *obj);
typedef char (*elis_Reader)(elis_State *S, void *udata);
typedef void (*elis_Writer)(elis_State *S, void *udata, char c);

struct elis_OnError {
  void (*callback)(elis_State *S, const char *msg, elis_Object *lst, void *udata);
  void *userdata;
};

struct elis_GCHooks {
  elis_CFunction mark, free;
};

enum {
  ELIS_PAIR, ELIS_NIL, ELIS_NUMBER, ELIS_STRING, ELIS_SYMBOL, ELIS_FUNCTION,
  ELIS_MACRO, ELIS_BUILTIN, ELIS_CFUNCTION, ELIS_USERDATA, ELIS_FREE
};

extern const char *const elis_typenames[];

elis_State *elis_init(elis_Allocator alloc, void *udata);
void elis_free(elis_State *S);
elis_OnError *elis_on_error(elis_State *S);
void elis_error(elis_State *S, const char *msg);

void elis_push_gc(elis_State *S, elis_Object *obj);
void elis_restore_gc(elis_State *S, int idx);
int elis_save_gc(elis_State *S);
void elis_mark(elis_State *S, elis_Object *obj);

elis_Object *elis_cons(elis_State *S, elis_Object *car, elis_Object *cdr);
elis_Object *elis_list(elis_State *S, elis_Object **objs, int cnt);
elis_Object *elis_bool(elis_State *S, int obj);
elis_Object *elis_number(elis_State *S, elis_Number num);
elis_Object *elis_string(elis_State *S, const char *str);
elis_Object *elis_substring(elis_State *S, const char *str, size_t len);
elis_Object *elis_symbol(elis_State *S, const char *name);
elis_Object *elis_cfunction(elis_State *S, elis_CFunction func);
elis_Object *elis_userdata(elis_State *S, void *udata, const elis_GCHooks *hooks);

int elis_nil(elis_State *S, elis_Object *obj);
int elis_type(elis_State *S, elis_Object *obj);
int elis_is(elis_State *S, elis_Object *a, elis_Object *b);
elis_Object *elis_car(elis_State *S, elis_Object *obj);
elis_Object *elis_cdr(elis_State *S, elis_Object *obj);
elis_Number elis_to_number(elis_State *S, elis_Object *obj);
const char *elis_to_string(elis_State *S, elis_Object *obj);
void *elis_to_userdata(elis_State *S, elis_Object *obj, const elis_GCHooks **hooks);

void elis_set(elis_State *S, elis_Object *sym, elis_Object *val);
void elis_set_car(elis_State *S, elis_Object *obj, elis_Object *val);
void elis_set_cdr(elis_State *S, elis_Object *obj, elis_Object *val);

elis_Object *elis_read(elis_State *S, elis_Reader func, void *udata);
elis_Object *elis_read_fp(elis_State *S, FILE *fp);
void elis_write(elis_State *S, elis_Object *obj, elis_Writer func, void *udata);
void elis_write_fp(elis_State *S, elis_Object *obj, FILE *fp);

elis_Object *elis_eval(elis_State *S, elis_Object *obj);
elis_Object *elis_apply(elis_State *S, elis_Object *func, elis_Object *args);
elis_Object *elis_next_arg(elis_State *S, elis_Object **args);

#endif
