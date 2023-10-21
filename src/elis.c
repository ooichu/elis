/*
 * Copyright (c) 2023 ooichu
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software
 * and associated documentation files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included in all copies or
 * substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING
 * BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
 * DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

#include "elis.h"

#include <stdlib.h>
#include <string.h>

struct elis_Object {
  union {
    elis_Object *o;
    elis_CFunction f;
    elis_Number n;
    struct { void *p; elis_Handlers *h; } *u;
    char *s, t[sizeof(void *)];
  } car, cdr;
};

static const union { size_t u; char c; } endian = { 0x1 };

#define TAG(x)       ((x)->car.t[!endian.c * (sizeof(void *) - 1)])
#define CAR(x)       ((x)->car.o)
#define CDR(x)       ((x)->cdr.o)
#define NUMBER(x)    ((x)->cdr.n)
#define CFUNCTION(x) ((x)->cdr.f)
#define STRING(x)    ((x)->cdr.s)
#define BUILTIN(x)   ((x)->cdr.t[0])
#define USERDATA(x)  ((x)->cdr.u->p)
#define HANDLERS(x)  ((x)->cdr.u->h)

#define TYPE(x)        (TAG(x) & 0x1 ? TAG(x) >> 2 : ELIS_PAIR)
#define SET_TYPE(x, t) (TAG(x) = ((t) << 2) | 0x1)
#define MARKED(x)      (TAG(x) & 0x2)
#define MARK(x)        (TAG(x) |= 0x2)
#define UNMARK(x)      (TAG(x) &= ~0x2)

static elis_Object nil = { { (elis_Object *) ((ELIS_NIL << 2) | 0x1) }, { NULL } };

const char *const elis_typenames[] = {
  "pair", "nil", "number", "string", "symbol", "function", "macro", "builtin", "cfunction",
  "userdata", "free"
};

enum {
  LIST, CONS, CAR, CDR, SETCAR, SETCDR, IF, WHILE, DO, AND, OR, NOT, FUNC, MACRO, QUOTE, GENSYM,
  PRINT, EVAL, APPLY, SET, LET, IS, ATOM, LT, LTE, ADD, SUB, MUL, DIV, MOD, IDIV, NUM_BUILTINS
};

static const char *const builtins[] = {
  "list", "cons", "car", "cdr", "setcar", "setcdr", "if", "while", "do", "and", "or", "not",
  "func", "macro", "quote", "gensym", "print", "eval", "apply", "=", "let", "is", "atom", "<",
  "<=", "+", "-", "*", "/", "%", "//"
};

struct elis_State {
  int gc_stack_idx, next_char;
  elis_Object *calls, *free, *pages, *symbols, *t, *quote, *gc_stack[ELIS_STACK_SIZE];
  size_t mark_stack_size;
  elis_Object **mark_stack;
  elis_Allocator allocator;
  elis_Error error;
  void *userdata;
};

static void *check_for_memout(void *ptr) {
  if (!ptr) {
    fputs("error: memory out\n", stderr);
    exit(EXIT_FAILURE);
  }
  return ptr;
}

static void *allocator(void *ptr, size_t size, void *udata) {
  (void) udata;
  /* due standard, we can't rely on `realloc()` behavior with zero `ptr` or `size` */
  if (!ptr) return check_for_memout(malloc(size));
  if (size) return check_for_memout(realloc(ptr, size));
  free(ptr);
  return NULL;
}

#define ALLOCATE(ptr, size) (S->allocator((ptr), (size), S->userdata))

static void free_object(elis_State *S, elis_Object *obj) {
  SET_TYPE(obj, ELIS_FREE);
  CDR(obj) = S->free;
  S->free = obj;
}

static void collect_garbage(elis_State *S) {
  int i;
  elis_Object *page;
  /* mark roots */
  for (i = 0; i < S->gc_stack_idx; ++i) elis_mark(S, S->gc_stack[i]);
  elis_mark(S, S->symbols);
  /* sweep all pages */
  for (page = S->pages; page != &nil; page = CDR(page)) {
    for (i = 1; i < ELIS_PAGE_SIZE; ++i) {
      elis_Object *obj = &page[i];
      if (!MARKED(obj)) {
        if (TYPE(obj) == ELIS_FREE) {
          /* skip already freed objects */
          continue;
        } else if (TYPE(obj) == ELIS_STRING) {
          /* if object is string -- deallocate string data */
          ALLOCATE(STRING(obj), 0);
        } else if (TYPE(obj) == ELIS_USERDATA) {
          /* if object is userdata -- try to call `free` handler and free additional part */
          if (HANDLERS(obj)->free) HANDLERS(obj)->free(S, obj);
          ALLOCATE(CDR(obj), 0);
        }
        /* mark object as free and add it to free list */
        free_object(S, obj);
      } else {
        UNMARK(obj);
      }
    }
  }
}

static elis_Object *make_object(elis_State *S) {
  elis_Object *obj;
  /* collect garbage if has no more free objects */
  if (S->free == &nil) {
    collect_garbage(S);
    /* allocate new page if free objects still not found */
    if (S->free == &nil) {
      elis_Object *page = (elis_Object *) ALLOCATE(NULL, ELIS_PAGE_SIZE * sizeof(*page));
      /* add new page to page list */
      CDR(page) = S->pages;
      S->pages = page;
      /* add all new objects to free list */
      obj = page + ELIS_PAGE_SIZE;
      while (++page != obj) free_object(S, page);
    }
  }
  /* take free object from free list and push to stack */
  obj = S->free;
  S->free = CDR(obj);
  elis_push_gc(S, obj);
  return obj;
}

#define MARK_STACK_INIT 256

elis_State *elis_init(elis_Allocator alloc, void *udata) {
  size_t i;
  elis_State *S;
  /* use default allocator if custom allocator not provided */
  if (!alloc) alloc = allocator;
  /* allocate state and bind allocator */
  S = (elis_State *) alloc(NULL, sizeof(*S), udata);
  memset(S, 0, sizeof(*S));
  S->allocator = alloc;
  S->userdata = udata;
  /* allocate mark stack */
  S->mark_stack_size = MARK_STACK_INIT;
  S->mark_stack = (elis_Object **) ALLOCATE(NULL, S->mark_stack_size * sizeof(*S->mark_stack));
  /* init internal lists */
  S->pages = &nil;
  S->calls = &nil;
  S->symbols = &nil;
  S->free = &nil;
  /* create frequently used symbols */
  S->t = elis_symbol(S, "t");
  S->quote = elis_symbol(S, "quote");
  elis_set(S, S->t, S->t);
  /* register builtins */
  for (i = 0; i < NUM_BUILTINS; ++i) {
    elis_Object *obj = make_object(S);
    SET_TYPE(obj, ELIS_BUILTIN);
    BUILTIN(obj) = i;
    elis_set(S, elis_symbol(S, builtins[i]), obj);
    elis_restore_gc(S, 0);
  } 
  return S;
}

void elis_free(elis_State *S) {
  elis_Object *page, *next;
  if (!S) return;
  /* reset roots and collect garbage */
  S->gc_stack_idx = 0;
  S->symbols = &nil;
  collect_garbage(S);
  /* free all pages and state */
  for (page = S->pages; page != &nil; page = next) {
    next = CDR(page);
    ALLOCATE(page, 0);
  }
  ALLOCATE(S->mark_stack, 0);
  ALLOCATE(S, 0);
}

elis_Error elis_on_error(elis_State *S, elis_Error func) {
  elis_Error error = S->error;
  S->error = func;
  return error;
}

#define BACKTRACE_LINE_MAX 64

static void trace(elis_State *S, void *udata, char chr) {
  unsigned *i = (unsigned *) udata;
  (void) S;
  /* limit trace line to `BACKTRACE_LINE_MAX` characters */
  if (*i < BACKTRACE_LINE_MAX) {
    fputc(chr, stderr);
    if (chr != '\0' && ++(*i) == BACKTRACE_LINE_MAX) fprintf(stderr, "...");
  }
}

void elis_error(elis_State *S, const char *msg) {
  elis_Object *lst = S->calls;
  /* detach call frames */
  S->calls = &nil;
  /* call error handler if possible */
  if (S->error) S->error(S, msg, lst);
  /* print error message and traceback */
  fprintf(stderr, "error: %s\n", msg);
  for (; lst != &nil; lst = CDR(lst)) {
    unsigned i = 0;
    fprintf(stderr, "=> ");
    elis_write(S, CAR(lst), trace, &i);
    fprintf(stderr, "\n");
  }
  exit(EXIT_FAILURE);
}

void elis_push_gc(elis_State *S, elis_Object *obj) {
  if (S->gc_stack_idx == ELIS_STACK_SIZE) elis_error(S, "stack overflow");
  S->gc_stack[S->gc_stack_idx++] = obj;
}

void elis_restore_gc(elis_State *S, int idx) {
  S->gc_stack_idx = idx;
}

int elis_save_gc(elis_State *S) {
  return S->gc_stack_idx;
}

static void push_mark_stack(elis_State *S, elis_Object *obj, size_t *i) {
  if (S->mark_stack_size == *i) {
    S->mark_stack_size <<= 1;
    S->mark_stack = (elis_Object **) ALLOCATE(S->mark_stack, S->mark_stack_size * sizeof(*S->mark_stack));
  }
  S->mark_stack[(*i)++] = obj;
}

void elis_mark(elis_State *S, elis_Object *obj) {
  size_t i = 0;
restart:
  if (!MARKED(obj)) {
    elis_Object *tmp = CAR(obj);
    MARK(obj);
    switch (TYPE(obj)) {
      case ELIS_PAIR:
        push_mark_stack(S, tmp, &i);
        /* fall through */
      case ELIS_SYMBOL:
      case ELIS_FUNCTION:
      case ELIS_MACRO:
        obj = CDR(obj);
        goto restart;
      case ELIS_USERDATA:
        if (HANDLERS(obj)->mark) HANDLERS(obj)->mark(S, obj);
        break;
    }
  }
  if (i != 0) {
    obj = S->mark_stack[--i];
    goto restart;
  }
}

elis_Object *elis_cons(elis_State *S, elis_Object *car, elis_Object *cdr) {
  elis_Object *obj = make_object(S);
  CAR(obj) = car;
  CDR(obj) = cdr;
  return obj;
}

elis_Object *elis_list(elis_State *S, elis_Object **objs, int cnt) {
  elis_Object *res = &nil;
  while (cnt) res = elis_cons(S, objs[--cnt], res);
  return res;
}

elis_Object *elis_bool(elis_State *S, int obj) {
  return obj ? S->t : &nil;
}

elis_Object *elis_number(elis_State *S, elis_Number num) {
  elis_Object *obj = make_object(S);
  SET_TYPE(obj, ELIS_NUMBER);
  NUMBER(obj) = num;
  return obj;
}

elis_Object *elis_string(elis_State *S, const char *str) {
  return elis_substring(S, str, strlen(str));
}

elis_Object *elis_substring(elis_State *S, const char *str, size_t len) {
  elis_Object *obj = make_object(S);
  SET_TYPE(obj, ELIS_STRING);
  STRING(obj) = (char *) ALLOCATE(NULL, len + 1);
  memcpy(STRING(obj), str, len);
  STRING(obj)[len] = '\0';
  return obj;
}

elis_Object *elis_symbol(elis_State *S, const char *name) {
  elis_Object *obj;
  /* anonymous symbol? */
  if (!name) {
    obj = make_object(S);
    CDR(obj) = elis_cons(S, &nil, &nil);
  } else {
    /* try to find already existing symbol */
    for (obj = S->symbols; obj != &nil; obj = CDR(obj)) {
      if (!strcmp(STRING(CAR(CDR(CAR(obj)))), name)) return CAR(obj);
    }
    /* create new object and add it to `symbols` */
    obj = make_object(S);
    CDR(obj) = elis_cons(S, elis_string(S, name), &nil);
    S->symbols = elis_cons(S, obj, S->symbols);
  }
  SET_TYPE(obj, ELIS_SYMBOL);
  return obj;
}

elis_Object *elis_cfunction(elis_State *S, elis_CFunction func) {
  elis_Object *obj = make_object(S);
  SET_TYPE(obj, ELIS_CFUNCTION);
  CFUNCTION(obj) = func;
  return obj;
}

static elis_Handlers empty_handlers = { NULL, NULL };

elis_Object *elis_userdata(elis_State *S, void *udata, elis_Handlers *hdls) {
  elis_Object *obj = make_object(S);
  SET_TYPE(obj, ELIS_USERDATA);
  CDR(obj) = (elis_Object *) ALLOCATE(NULL, sizeof(*obj->cdr.u));
  USERDATA(obj) = udata;
  HANDLERS(obj) = hdls ? hdls : &empty_handlers;
  return obj;
}

int elis_type(elis_State *S, elis_Object *obj) {
  (void) S;
  return TYPE(obj);
}

int elis_nil(elis_State *S, elis_Object *obj) {
  (void) S;
  return obj == &nil;
}

int elis_is(elis_State *S, elis_Object *a, elis_Object *b) {
  (void) S;
  if (a == b) return 1;
  if (TYPE(a) == TYPE(b)) {
    if (TYPE(a) == ELIS_NUMBER) return NUMBER(a) == NUMBER(b);
    if (TYPE(a) == ELIS_STRING) return !strcmp(STRING(a), STRING(b));
  }
  return 0;
}

static elis_Object *check_type(elis_State *S, elis_Object *obj, int type) {
  char buf[40];
  if (TYPE(obj) != type) {
    sprintf(buf, "expected %s, got %s", elis_typenames[type], elis_typenames[TYPE(obj)]);
    elis_error(S, buf);
  }
  return obj;
}

elis_Object *elis_car(elis_State *S, elis_Object *obj) {
  if (obj == &nil) return obj;
  return CAR(check_type(S, obj, ELIS_PAIR));
}

elis_Object *elis_cdr(elis_State *S, elis_Object *obj) {
  if (obj == &nil) return obj;
  return CDR(check_type(S, obj, ELIS_PAIR));
}

void *elis_to_userdata(elis_State *S, elis_Object *obj, elis_Handlers **hdlrs) {
  check_type(S, obj, ELIS_USERDATA);
  if (hdlrs) *hdlrs = HANDLERS(obj) == &empty_handlers ? NULL : HANDLERS(obj);
  return USERDATA(obj);
}

elis_Number elis_to_number(elis_State *S, elis_Object *obj) {
  return NUMBER(check_type(S, obj, ELIS_NUMBER));
}

const char *elis_to_string(elis_State *S, elis_Object *obj) {
  if (TYPE(obj) == ELIS_SYMBOL) {
    obj = CAR(CDR(obj));
    if (obj == &nil) return "";
  }
  return STRING(check_type(S, obj, ELIS_STRING));
}

#define END_OF_SEXPR ((elis_Object *) 1)

static elis_Object *read_object(elis_State *S, elis_Reader func, void *udata) {
  char buf[64];
  elis_Object *obj;
  /* get next character */
  int chr = S->next_char ? S->next_char : func(S, udata);
  S->next_char = '\0';
  /* skip whitespaces */
  while (chr && strchr(" \n\t\r", chr)) chr = func(S, udata);
  /* parse lexeme */
  switch (chr) {
    case '\0':
      break;
    case ')':
      return END_OF_SEXPR;
    case ';':
      while (chr && chr != '\n' && chr != '\r') chr = func(S, udata);
      return read_object(S, func, udata);
    case '\'':
      obj = elis_read(S, func, udata);
      if (!obj) elis_error(S, "stray `'`");
      return elis_cons(S, S->quote, elis_cons(S, obj, &nil));
    case '(': {
      int gc = elis_save_gc(S);
      elis_Object *res = &nil, **tail = &res;
      elis_push_gc(S, res); /* to cause error on too deep nesting */
      while ((obj = read_object(S, func, udata)) != END_OF_SEXPR) {
        if (!obj) elis_error(S, "unclosed list");
        if (TYPE(obj) == ELIS_SYMBOL && !strcmp(STRING(CAR(CDR(obj))), ".")) {
          /* dotted pair */
          *tail = elis_read(S, func, udata);
        } else {
          /* normal list */
          *tail = elis_cons(S, obj, &nil);
          tail = &CDR(*tail);
        }
        elis_restore_gc(S, gc);
        elis_push_gc(S, res);
      }
      return res;
    }
    case '"': {
      size_t len = 0, size = sizeof(buf);
      char *str = (char *) ALLOCATE(NULL, size);
      /* collect string */
      while ((chr = func(S, udata)) != '"') {
        if (chr == '\0') elis_error(S, "unclosed string");
        /* need to stretch buffer? */
        if (len == size) {
          size <<= 1;
          str = (char *) ALLOCATE(str, size + 1);
        }
        /* is escape sequence? */
        if (chr == '\\') {
          chr = func(S, udata);
          if (strchr("nrt", chr)) chr = strchr("n\nr\rt\t", chr)[1];
        }
        str[len++] = chr;
      }
      /* terminate string and compact buffer */
      str[len] = '\0';
      str = (char *) ALLOCATE(str, len + 1);
      /* create string object */
      obj = make_object(S);
      SET_TYPE(obj, ELIS_STRING);
      STRING(obj) = str;
      return obj;
    }
    default: {
      char *ptr = buf;
      elis_Number num;
      /* collect lexeme to the fixed buffer */
      do {
        if (ptr == buf + sizeof(buf) - 1) elis_error(S, "symbol too long");
        *ptr++ = chr;
        chr = func(S, udata);
      } while (chr && !strchr(" \n\t\r\"'();", chr));
      *ptr = '\0';
      S->next_char = chr;
      /* try to parse number */
      num = strtod(buf, &ptr);
      if (ptr != buf && *ptr == '\0') return elis_number(S, num);
      /* is nil? */
      if (!strcmp(buf, "nil")) return &nil;
      /* okay, it's symbol */
      return elis_symbol(S, buf);
    }
  }
  return NULL;
}
  
elis_Object *elis_read(elis_State *S, elis_Reader read, void *udata) {
  elis_Object* obj = read_object(S, read, udata);
  if (obj == END_OF_SEXPR) elis_error(S, "extra `)`");
  return obj;  
}

static char read_fp(elis_State *S, void *udata) {
  int chr = fgetc((FILE *) udata);
  (void) S;
  return chr == EOF ? '\0' : chr;
}

elis_Object *elis_read_fp(elis_State *S, FILE *fp) {
  return elis_read(S, read_fp, fp);  
}

static void write_string(elis_State *S, elis_Writer func, void *udata, const char *str) {
  while (*str) func(S, udata, *str++);
}

static void write_object(elis_State *S, elis_Object *obj, elis_Writer func, void *udata) {
  char buf[32];
  switch (TYPE(obj)) {
    case ELIS_PAIR:
      if (MARKED(obj)) {
        write_string(S, func, udata, "...");
        break;
      }
      func(S, udata, '(');
      for (;;) {
        /* mark `obj` and write `CAR(obj)` */
        elis_Object *tmp = CAR(obj);
        MARK(obj);
        write_object(S, tmp, func, udata);
        /* write `CDR(obj)` if isn't circular list */
        obj = CDR(obj);
        if (TYPE(obj) != ELIS_PAIR) break;
        func(S, udata, ' ');
        if (MARKED(obj)) {
          write_string(S, func, udata, "...");
          break;
        }
      }
      if (obj != &nil && !MARKED(obj)) {
        write_string(S, func, udata, " . ");
        write_object(S, obj, func, udata);
      }
      func(S, udata, ')');
      break;
    case ELIS_NIL:
      write_string(S, func, udata, "nil");
      break;
    case ELIS_NUMBER:
      sprintf(buf, ELIS_NUMBER_FORMAT, NUMBER(obj));
      write_string(S, func, udata, buf);
      break;
    case ELIS_STRING:
      func(S, udata, '"');
      write_string(S, func, udata, STRING(obj));
      func(S, udata, '"');
      break;
    case ELIS_SYMBOL:
      /* isn't anonymous symbol? */
      if (CAR(CDR(obj)) != &nil) {
        write_string(S, func, udata, STRING(CAR(CDR(obj))));
        break;
      }
      /* fall through */
    default:
      sprintf(buf, "[%s %p]", elis_typenames[TYPE(obj)], (void *) obj);
      write_string(S, func, udata, buf);
      break;
  }
}

static void unmark_pairs(elis_Object *obj) {
  for (; obj != &nil && MARKED(obj); obj = CDR(obj)) {
    UNMARK(obj);
    unmark_pairs(CAR(obj));
  }
}

void elis_write(elis_State *S, elis_Object *obj, elis_Writer func, void *udata) {
  write_object(S, obj, func, udata);
  unmark_pairs(obj);
}

static void write_fp(elis_State *S, void *udata, char chr) {
  (void) S;
  fputc(chr, (FILE *) udata);
}

void elis_write_fp(elis_State *S, elis_Object *obj, FILE *fp) {
  elis_write(S, obj, write_fp, fp);
}

static elis_Object *lookup(elis_Object *sym, elis_Object *env) {
  /* try to find sym in enviroment */
  for (; env != &nil; env = CDR(env)) {
    elis_Object *obj = CAR(env);
    if (CAR(obj) == sym) return obj;
  }
  /* return global value */
  return CDR(sym);
}

static elis_Object *eval(elis_State *S, elis_Object *obj, elis_Object *env, elis_Object **new_env);

static elis_Object *eval_list(elis_State *S, elis_Object *lst, elis_Object *env) {
  elis_Object *res = &nil, **tail = &res;
  for (; lst != &nil; tail = &CDR(*tail)) {
    *tail = elis_cons(S, eval(S, elis_next_arg(S, &lst), env, NULL), &nil);
  }
  return res;
}

static elis_Object *do_list(elis_State *S, elis_Object *lst, elis_Object *env) {
  int gc = elis_save_gc(S);
  elis_Object *res = &nil;
  while (lst != &nil) {
    elis_restore_gc(S, gc);
    elis_push_gc(S, lst);
    elis_push_gc(S, env);
    res = eval(S, elis_next_arg(S, &lst), env, &env);
  }
  return res;
}

static elis_Object *bind(elis_State *S, elis_Object *prm, elis_Object *args, elis_Object *env) {
  for (; TYPE(prm) == ELIS_PAIR; prm = CDR(prm), args = elis_cdr(S, args)) {
    env = elis_cons(S, elis_cons(S, CAR(prm), elis_car(S, args)), env);
  }
  return prm == &nil ? env : elis_cons(S, elis_cons(S, prm, args), env);
}

static void set(elis_State *S, elis_Object *sym, elis_Object *val, elis_Object *env) {
  CDR(lookup(check_type(S, sym, ELIS_SYMBOL), env)) = val;
}

#define COMPARE_OP(expr, eval_arg) {                                                     \
  elis_Number a = elis_to_number(S, eval_arg);                                           \
  elis_Number b = elis_to_number(S, eval_arg);                                           \
  res = elis_bool(S, expr);                                                              \
}

#define ARITH_OP(expr, eval_arg) {                                                       \
  elis_Number a = elis_to_number(S, eval_arg);                                           \
  while (args != &nil) {                                                                 \
    elis_Number b = elis_to_number(S, eval_arg);                                         \
    a = expr;                                                                            \
  }                                                                                      \
  res = elis_number(S, a);                                                               \
}

#define CALL(eval_arg, eval_list, restore) {                                             \
  int gc = elis_save_gc(S);                                                              \
  elis_Object *res = &nil, *func = eval(S, CAR(obj), env, NULL), *args = CDR(obj);       \
  /* allowed to call only functions, macros, builtins and cfunctions */                  \
  switch (TYPE(func)) {                                                                  \
    case ELIS_FUNCTION:                                                                  \
      args = eval_list;                                                                  \
      /* fall through */                                                                 \
    case ELIS_MACRO: {                                                                   \
      elis_Object *local = CDR(func), *params = CDR(local);                              \
      res = do_list(S, CDR(params), bind(S, CAR(params), args, CAR(local)));             \
      if (TYPE(func) == ELIS_FUNCTION) break;                                            \
      *obj = *check_type(S, res, ELIS_PAIR);                                             \
      elis_restore_gc(S, gc);                                                            \
      S->calls = restore;                                                                \
      return eval(S, obj, env, new_env);                                                 \
    }                                                                                    \
    case ELIS_BUILTIN:                                                                   \
      switch (BUILTIN(func)) {                                                           \
        case LIST:                                                                       \
          res = eval_list;                                                               \
          break;                                                                         \
        case CONS:                                                                       \
          obj = eval_arg;                                                                \
          res = elis_cons(S, obj, eval_arg);                                             \
          break;                                                                         \
        case CAR:                                                                        \
          res = elis_car(S, eval_arg);                                                   \
          break;                                                                         \
        case CDR:                                                                        \
          res = elis_cdr(S, eval_arg);                                                   \
          break;                                                                         \
        case SETCAR:                                                                     \
          obj = eval_arg;                                                                \
          elis_setcar(S, obj, eval_arg);                                                 \
          break;                                                                         \
        case SETCDR:                                                                     \
          obj = eval_arg;                                                                \
          elis_setcdr(S, obj, eval_arg);                                                 \
          break;                                                                         \
        case IF:                                                                         \
          while (args != &nil) {                                                         \
            obj = eval_arg;                                                              \
            if (obj != &nil) {                                                           \
              res = args == &nil ? obj : eval_arg;                                       \
              break;                                                                     \
            }                                                                            \
            if (args == &nil) break;                                                     \
            args = CDR(args);                                                            \
          }                                                                              \
          break;                                                                         \
        case WHILE: {                                                                    \
          int gc = elis_save_gc(S);                                                      \
          obj = elis_next_arg(S, &args);                                                 \
          while (eval(S, obj, env, NULL) != &nil) {                                      \
            do_list(S, args, env);                                                       \
            elis_restore_gc(S, gc);                                                      \
          }                                                                              \
          break;                                                                         \
        }                                                                                \
        case DO:                                                                         \
          res = do_list(S, args, env);                                                   \
          break;                                                                         \
        case AND:                                                                        \
          while (args != &nil && (res = eval_arg) != &nil);                              \
          break;                                                                         \
        case OR:                                                                         \
          while (args != &nil && (res = eval_arg) == &nil);                              \
          break;                                                                         \
        case NOT:                                                                        \
          res = elis_bool(S, eval_arg == &nil);                                          \
          break;                                                                         \
        case FUNC:                                                                       \
        case MACRO:                                                                      \
          res = make_object(S);                                                          \
          SET_TYPE(res, BUILTIN(func) == FUNC ? ELIS_FUNCTION : ELIS_MACRO);             \
          CDR(res) = elis_cons(S, env, args);                                            \
          elis_next_arg(S, &args);                                                       \
          break;                                                                         \
        case QUOTE:                                                                      \
          res = elis_next_arg(S, &args);                                                 \
          break;                                                                         \
        case GENSYM:                                                                     \
          res = elis_symbol(S, NULL);                                                    \
          break;                                                                         \
        case PRINT:                                                                      \
          while (args != &nil) {                                                         \
            obj = eval_arg;                                                              \
            if (TYPE(obj) != ELIS_STRING) {                                              \
              elis_write_fp(S, obj, stdout);                                             \
            } else {                                                                     \
              printf("%s", STRING(obj));                                                 \
            }                                                                            \
            fputc(' ', stdout);                                                          \
          }                                                                              \
          printf("\n");                                                                  \
          break;                                                                         \
        case EVAL:                                                                       \
          res = eval(S, eval_arg, env, new_env);                                         \
          break;                                                                         \
        case APPLY: {                                                                    \
          elis_Object call;                                                              \
          CAR(&call) = elis_next_arg(S, &args);                                          \
          CDR(&call) = eval_arg;                                                         \
          res = apply(S, &call, env, new_env);                                           \
          break;                                                                         \
        }                                                                                \
        case SET:                                                                        \
          do {                                                                           \
            obj = elis_next_arg(S, &args), func = eval_arg;                              \
            for (; TYPE(obj) == ELIS_PAIR; obj = CDR(obj), func = elis_cdr(S, func)) {   \
              set(S, CAR(obj), elis_car(S, func), env);                                  \
            }                                                                            \
            if (obj != &nil) set(S, obj, func, env);                                     \
          } while (args != &nil);                                                        \
          break;                                                                         \
        case LET:                                                                        \
          if (!new_env) elis_error(S, "attempt to bind local in global scope");          \
          do {                                                                           \
            obj = elis_next_arg(S, &args);                                               \
            env = bind(S, obj, eval_arg, env);                                           \
          } while (args != &nil);                                                        \
          *new_env = env;                                                                \
          break;                                                                         \
        case IS:                                                                         \
          obj = eval_arg;                                                                \
          res = elis_bool(S, elis_is(S, obj, eval_arg));                                 \
          break;                                                                         \
        case ATOM:                                                                       \
          obj = eval_arg;                                                                \
          res = elis_bool(S, TYPE(obj) != ELIS_PAIR);                                    \
          break;                                                                         \
        case LT:                                                                         \
          COMPARE_OP(a < b, eval_arg);                                                   \
          break;                                                                         \
        case LTE:                                                                        \
          COMPARE_OP(a <= b, eval_arg);                                                  \
          break;                                                                         \
        case ADD:                                                                        \
          ARITH_OP(a + b, eval_arg);                                                     \
          break;                                                                         \
        case SUB:                                                                        \
          ARITH_OP(a - b, eval_arg);                                                     \
          break;                                                                         \
        case MUL:                                                                        \
          ARITH_OP(a * b, eval_arg);                                                     \
          break;                                                                         \
        case DIV:                                                                        \
          ARITH_OP(a / b, eval_arg);                                                     \
          break;                                                                         \
        case MOD:                                                                        \
          ARITH_OP(a - b * (long) (a / b), eval_arg);                                    \
          break;                                                                         \
        case IDIV:                                                                       \
          ARITH_OP(b ? (long) (a / b) : (elis_error(S, "divide by zero"), 0), eval_arg); \
          break;                                                                         \
      }                                                                                  \
      break;                                                                             \
    case ELIS_CFUNCTION:                                                                 \
      res = CFUNCTION(func)(S, eval_list);                                               \
      break;                                                                             \
    default:                                                                             \
      elis_error(S, "tried to call non-callable value");                                 \
  }                                                                                      \
  /* restore previous call frame */                                                      \
  elis_restore_gc(S, gc);                                                                \
  elis_push_gc(S, res);                                                                  \
  S->calls = restore;                                                                    \
  return res;                                                                            \
}

static elis_Object *apply(elis_State *S, elis_Object *obj, elis_Object *env, elis_Object **new_env);

static elis_Object *eval(elis_State *S, elis_Object *obj, elis_Object *env, elis_Object **new_env) {
  elis_Object call;
  /* symbol evaluates to it's object */
  if (TYPE(obj) == ELIS_SYMBOL) return CDR(lookup(obj, env));
  /* other atoms evaluate to themselves */
  if (TYPE(obj) != ELIS_PAIR) return obj;
  /* create new call frame */
  CAR(&call) = obj;
  CDR(&call) = S->calls;
  S->calls = &call;
  /* call function */
  CALL(eval(S, elis_next_arg(S, &args), env, NULL), eval_list(S, args, env), CDR(&call));
}

static elis_Object *apply(elis_State *S, elis_Object *obj, elis_Object *env, elis_Object **new_env) {
  /* function call like in `eval`, but call frame isn't created and arguments isn't evaluated */
  CALL(elis_next_arg(S, &args), args, S->calls);
}

elis_Object *elis_eval(elis_State *S, elis_Object *obj) {
  return eval(S, obj, &nil, NULL);
}

elis_Object *elis_apply(elis_State *S, elis_Object *func, elis_Object *args) {
  elis_Object call;
  CAR(&call) = func;
  CDR(&call) = args;
  return apply(S, &call, &nil, NULL);
}

elis_Object *elis_next_arg(elis_State *S, elis_Object **args) {
  elis_Object *obj = *args;
  if (TYPE(obj) != ELIS_PAIR) {
    if (obj == &nil) elis_error(S, "too few arguments");
    elis_error(S, "dotted pair in argument list");
  }
  *args = CDR(obj);
  return CAR(obj);
}

void elis_set(elis_State *S, elis_Object *sym, elis_Object *obj) {
  CDR(CDR(check_type(S, sym, ELIS_SYMBOL))) = obj;
}

void elis_setcar(elis_State *S, elis_Object *obj, elis_Object *val) {
  CAR(check_type(S, obj, ELIS_PAIR)) = val;
}

void elis_setcdr(elis_State *S, elis_Object *obj, elis_Object *val) {
  CDR(check_type(S, obj, ELIS_PAIR)) = val;
}

#ifdef ELIS_TESTBED

#include <setjmp.h>

static jmp_buf jmpbuf;

static void on_error(elis_State *S, const char *msg, elis_Object *calls) {
  (void) S;
  (void) calls;
  fprintf(stderr, "error: %s\n", msg);
  longjmp(jmpbuf, -1);
}

int main(int argc, char **argv) {
  elis_Object *obj;
  elis_State *S = elis_init(NULL, NULL);
  FILE *fp = argc > 1 ? fopen(argv[1], "rb") : stdin;
  if (!fp) elis_error(S, "could not open input file");
  /* use error handler to recover from errors in REPL mode */
  if (fp == stdin) {
    elis_on_error(S, on_error);
    setjmp(jmpbuf);
  }
  /* REPL - read, eval, print, loop */
  for (;;) {
    elis_restore_gc(S, 0);
    if (fp == stdin) printf("> ");
    obj = elis_read_fp(S, fp);
    if (!obj) break;
    obj = elis_eval(S, obj);
    if (fp == stdin) {
      elis_write_fp(S, obj, stdout);
      printf("\n");
    }
  }
  return EXIT_SUCCESS;
}

#endif
