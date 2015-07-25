#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <stdio.h>
#include <assert.h>

#include "ool.h"

void
list_insert(struct list *nd, struct list *before)
{
  struct list *p = before->prev;

  nd->prev = p;
  nd->next = before;

  p->next = before->prev = nd;
}

void
list_erase(struct list *nd)
{
  struct list *p = nd->prev, *q = nd->next;

  p->next = q;
  q->prev = p;

  nd->prev = nd->next = 0;
}

/***************************************************************************/

void obj_free(obj_t obj);

obj_t
obj_retain(obj_t obj)
{
  if (obj != 0) {
    ++obj->ref_cnt;
    
    assert(obj->ref_cnt != 0);
  }

  return (obj);
}

void
obj_release(obj_t obj)
{
  if (obj == 0)  return;

  assert(obj->ref_cnt != 0);

  if (--obj->ref_cnt == 0)  obj_free(obj);
}

void
obj_assign(obj_t *dst, obj_t src)
{
  obj_t temp = *dst;

  *dst = obj_retain(src);
  obj_release(temp);
}

/***************************************************************************/

void
method_call_frame_push(struct method_call_frame *mcfr, obj_t *result, obj_t cl, obj_t sel, unsigned argc, obj_t *argv)
{
  mcfr->prev   = mcfp;
  mcfr->result = result;
  mcfr->cl     = cl;
  mcfr->sel    = sel;
  mcfr->argc   = argc;
  mcfr->argv   = argv;

  mcfp = mcfr;

  frame_push(mcfr->base, FRAME_TYPE_METHOD_CALL);
}

void
method_call_frame_pop(void)
{
  frame_pop();

  mcfp = mcfp->prev;
}

void
module_frame_push(struct module_frame *modfr, obj_t module)
{
  modfr->prev   = modfp;
  modfr->module = module;

  modfp = modfr;

  frame_push(modfr->base, FRAME_TYPE_MODULE);
}

void
module_frame_pop(void)
{
  modfp = modfp->prev;
}

unsigned err_depth;

void
double_err(void)
{
  fprintf(stderr, "Double error\n");
  
  abort();
}

void
method_argc_err(void)
{
  if (++err_depth > 1)  double_err();

  fprintf(stderr, "Incorrect number of arguments\n");
  
  error();
}

void
method_bad_arg_err(obj_t arg)
{
  WORK_FRAME_DECL(work, 1);

  if (++err_depth > 1)  double_err();

  WORK_FRAME_PUSH(work);

  inst_method_call(&WORK(work, 0), consts.str_tostring, 1, &arg);

  fprintf(stderr, "Bad argument: %s\n", STR(WORK(work, 0))->data);

  WORK_FRAME_POP();
  
  error();
}

/***************************************************************************/

struct {
  unsigned long long mem_alloc_cnt, mem_alloc_bytes;
  unsigned long long mem_free_cnt,  mem_free_bytes;
} stats[1];

void
ool_mem_free(void *p, unsigned size)
{
  ++stats->mem_free_cnt;
  stats->mem_free_bytes += size;
}

void *
ool_mem_alloc(unsigned size)
{
  ++stats->mem_alloc_cnt;
  stats->mem_alloc_bytes += size;

  return (malloc(size));
}

void *
ool_mem_allocz(unsigned size)
{
  void *result = ool_mem_alloc(size);

  memset(result, 0, size);

  return (result);
}

/***************************************************************************/

void
obj_free(obj_t obj)
{
  obj_t cl;

  for (cl = inst_of(obj); cl; cl = CLASS(cl)->parent) {
    if (CLASS(cl)->walk)  (*CLASS(cl)->walk)(obj, obj_release);
  }

  for (cl = inst_of(obj); cl; cl = CLASS(cl)->parent) {
    if (CLASS(cl)->free)  (*CLASS(cl)->free)(obj);
  }

  ool_mem_free(obj, CLASS(inst_of(obj))->inst_size);
}

void
inst_alloc(obj_t *dst, obj_t cl)
{
  obj_t    p;
  unsigned size = CLASS(cl)->inst_size;

  if (size == 0) {
    fprintf(stderr, "Cannot instantiate class %s\n", STR(CLASS(cl)->name)->data);
    error();
  }

  if (list_empty(CLASS(cl)->inst_cache)) {
    p = (obj_t) ool_mem_allocz(size);
  } else {
    struct list *q = list_first(CLASS(cl)->inst_cache);

    list_erase(q);

    p = CONTAINER_OF(q, struct obj, list_node);
  }

  obj_assign(&p->inst_of, cl);
  
  obj_assign(dst, p);
}

/***************************************************************************/

void
inst_init_parent(obj_t self, obj_t cl, unsigned argc, va_list ap)
{
  obj_t parent = CLASS(cl)->parent;

  if (parent == 0)  return;

  (*CLASS(parent)->init)(self, parent, argc, ap);
}

/***************************************************************************/

void
object_init(obj_t self, obj_t cl, unsigned argc, va_list ap)
{
  assert(argc == 0);
}

void
cm_obj_inst_of(void)
{
  obj_assign(MC_RESULT, inst_of(MC_ARG(0)));
}

void
cm_obj_copy(void)
{
  obj_assign(MC_RESULT, MC_ARG(0));
}

void
cm_obj_quote(void)
{
  obj_assign(MC_RESULT, MC_ARG(0));
}

void
cm_obj_eval(void)
{
  obj_assign(MC_RESULT, MC_ARG(0));
}

void
cm_obj_tostring(void)
{
  if (MC_ARGC != 1)  method_argc_err();

  if (MC_ARG(0) != 0) {
    char     *s = STR(CLASS(inst_of(MC_ARG(0)))->name)->data;
    unsigned n  = 1 + strlen(s) + 1 + 18 + 1 + 1;
    char     buf[n];

    sprintf(buf, "<%s@%p>", s, MC_ARG(0));

    str_newc(MC_RESULT, 1, n, buf);

    return;
  }

  str_newc(MC_RESULT, 1, 5, "#nil");
}

/***************************************************************************/

void
bool_init(obj_t self, obj_t cl, unsigned argc, va_list ap)
{
  assert(argc > 0);

  BOOL(self)->val = (va_arg(ap, unsigned) != 0);  --argc;

  inst_init_parent(self, cl, argc, ap);
}

static inline void
_bool_init(obj_t *dst, unsigned argc, ...)
{
  va_list ap;

  va_start(ap, argc);

  bool_init(*dst, consts.cl_bool, argc, ap);

  va_end(ap);
}

void
bool_new(obj_t *dst, unsigned val)
{
  inst_alloc(dst, consts.cl_bool);
  _bool_init(dst, 1, val);
}

void
cm_bool_and(void)
{
  if (MC_ARGC != 2)  method_argc_err();
  if (inst_of(MC_ARG(0)) != consts.cl_bool)  method_bad_arg_err(MC_ARG(0));
  if (inst_of(MC_ARG(1)) != consts.cl_bool)  method_bad_arg_err(MC_ARG(1));

  bool_new(MC_RESULT, BOOL(MC_ARG(0))->val && BOOL(MC_ARG(1))->val);
}

void
cm_bool_or(void)
{
  if (MC_ARGC != 2)  method_argc_err();
  if (inst_of(MC_ARG(0)) != consts.cl_bool)  method_bad_arg_err(MC_ARG(0));
  if (inst_of(MC_ARG(1)) != consts.cl_bool)  method_bad_arg_err(MC_ARG(1));

  bool_new(MC_RESULT, BOOL(MC_ARG(0))->val || BOOL(MC_ARG(1))->val);
}

void
cm_bool_not(void)
{
  if (MC_ARGC != 1)  method_argc_err();
  if (inst_of(MC_ARG(0)) != consts.cl_bool)  method_bad_arg_err(MC_ARG(0));

  bool_new(MC_RESULT, !BOOL(MC_ARG(0))->val);
}

/***************************************************************************/

void
int_init(obj_t self, obj_t cl, unsigned argc, va_list ap)
{
  assert(argc > 0);

  INT(self)->val = va_arg(ap, intval_t);  --argc;

  inst_init_parent(self, cl, argc, ap);
}

static inline void
_int_init(obj_t self, unsigned argc, ...)
{
  va_list ap;

  va_start(ap, argc);

  int_init(self, consts.cl_int, argc, ap);

  va_end(ap);
}


void
int_new(obj_t *dst, intval_t val)
{
  inst_alloc(dst, consts.cl_int);
  _int_init(*dst, 1, val);
}

void
cm_int_add(void)
{
  if (MC_ARGC != 2)  method_argc_err();
  if (inst_of(MC_ARG(0)) != consts.cl_int)  method_bad_arg_err(MC_ARG(0));
  if (inst_of(MC_ARG(1)) != consts.cl_int)  method_bad_arg_err(MC_ARG(1));

  int_new(MC_RESULT, INT(MC_ARG(0))->val + INT(MC_ARG(1))->val);
}

void
cm_int_tostring(void)
{
  char buf[32];

  if (MC_ARGC != 1)  method_argc_err();
  if (inst_of(MC_ARG(0)) != consts.cl_int)  method_bad_arg_err(MC_ARG(0));

  snprintf(buf, sizeof(buf), "%lld", INT(MC_ARG(0))->val);
  
  str_newc(MC_RESULT, 1, strlen(buf) + 1, buf);
}

/***************************************************************************/

void
str_init(obj_t self, obj_t cl, unsigned argc, va_list ap)
{
  obj_t arg;

  WORK_FRAME_DECL(work, 1);

  assert(argc > 0);

  arg = va_arg(ap, obj_t);  --argc;

  WORK_FRAME_PUSH(work);

  inst_method_call(&WORK(work, 0), consts.str_tostring, 1, &arg);

  if (STR(self)->data)  ool_mem_free(STR(self)->data, STR(self)->size);

  STR(self)->size = STR(WORK(work, 0))->size;
  STR(self)->data = ool_mem_alloc(STR(self)->size);
  memcpy(STR(self)->data, STR(WORK(work, 0))->data, STR(self)->size);
  
  WORK_FRAME_POP();

  inst_init_parent(self, cl, argc, ap);
}

void
str_newc(obj_t *result, unsigned argc, ...)
{
  va_list  ap;
  unsigned k, n, len;
  char     *s, *q;

  WORK_FRAME_DECL(work, 1);

  WORK_FRAME_PUSH(work);

  va_start(ap, argc);

  for (len = 1, n = argc; n; --n) {
    len += va_arg(ap, unsigned) - 1;
    s   =  va_arg(ap, char *);
  }

  va_end(ap);

  inst_alloc(&WORK(work, 0), consts.cl_str);
  STR(WORK(work, 0))->size = len;
  STR(WORK(work, 0))->data = ool_mem_alloc(len);

  va_start(ap, argc);

  for (q = STR(WORK(work, 0))->data, n = argc; n; --n) {
    len = va_arg(ap, unsigned) - 1;
    memcpy(q, va_arg(ap, char *), len);
    q += len;
  }
  *q = 0;

  va_end(ap);

  obj_assign(result, WORK(work, 0));

  WORK_FRAME_POP();
}

void
str_newv(obj_t *result, unsigned argc, obj_t *argv)
{
  unsigned k, n, len;
  obj_t    *p;
  char     *s, *q;

  WORK_FRAME_DECL(work, 1);

  WORK_FRAME_PUSH(work);

  for (len = 1, p = argv, n = argc; n; --n, ++p) {
    len += STR(*p)->size - 1;
  }

  inst_alloc(&WORK(work, 0), consts.cl_str);
  STR(WORK(work, 0))->size = len;
  STR(WORK(work, 0))->data = ool_mem_alloc(len);

  for (q = STR(WORK(work, 0))->data, p = argv, n = argc; n; --n, ++p) {
    len = STR(*p)->size - 1;
    memcpy(q, STR(*p)->data, len);
    q += len;
  }
  *q = 0;

  obj_assign(result, WORK(work, 0));

  WORK_FRAME_POP();
}



void
str_free(obj_t obj)
{
  ool_mem_free(STR(obj)->data, STR(obj)->size);
}

unsigned
str_hash(obj_t s)
{
  unsigned result;
  char     *p, c;

  assert(inst_of(s) == consts.cl_str);

  for (result = 0, p = STR(s)->data; c = *p; ++p) {
    result += c;
  }

  return (result);
}

unsigned
str_eq(obj_t s1, obj_t s2)
{
  assert(inst_of(s1) == consts.cl_str && inst_of(s2) == consts.cl_str);

  return (STR(s1)->size == STR(s2)->size && strcmp(STR(s1)->data, STR(s2)->data) == 0);
}

obj_t *
strdict_find(obj_t dict, obj_t key, obj_t **bucket)
{
  obj_t *p = &DICT(dict)->base->base->data[str_hash(key) & (DICT(dict)->base->base->size - 1)], q;

  if (bucket)  *bucket = p;

  for ( ; q = *p; p = &CDR(q)) {
    if (str_eq(CAR(CAR(q)), key))  return (p);
  }

  return (0);
}

enum {
  STRDICT_SIZE_DFLT = 32
};

void _dict_new(obj_t *dst, obj_t *(*find)(obj_t, obj_t, obj_t **), unsigned size);
void dict_new(obj_t *dst, unsigned size);

void
strdict_new(obj_t *dst, unsigned size)
{
  _dict_new(dst, strdict_find, size == 0 ? STRDICT_SIZE_DFLT : size);
}


obj_t
str_env_find(obj_t s)
{
  obj_t d, q;

  {
    struct block_frame *p;

    for (p = blkfp; p; p = p->prev) {
      if ((q = dict_at(d = p->dict, s)) != 0) {
	return (q);
      }
    }
  }

  {
    struct module_frame *p;
    
    for (p = modfp; p; p = p->prev) {
      if ((q = dict_at(d = OBJ(MODULE(p->module)->base), s)) != 0) {
	return (q);
      }
    }
  }

  return (0);
}

obj_t
str_env_top(void)
{
  return (blkfp ? blkfp->dict : OBJ(MODULE(modfp->module)->base));
}

obj_t
str_eval(obj_t s)
{
  obj_t p;

  if (p = str_env_find(s))  return (CDR(p));

  fprintf(stderr, "Variable not bound: %s\n", STR(s)->data);

  error();
}

void
str_bind(obj_t s, obj_t val)
{
  obj_t p;

  if (p = str_env_find(s)) {
    obj_assign(&CDR(p), val);

    return;
  }

  dict_at_put(str_env_top(), s, val);
}

void
cm_str_hash(void)
{
  if (MC_ARGC != 1)  method_argc_err();
  if (inst_of(MC_ARG(0)) != consts.cl_str)  method_bad_arg_err(MC_ARG(0));

  int_new(MC_RESULT, str_hash(MC_ARG(0)));
}

void
cm_str_equal(void)
{
  if (MC_ARGC != 2)  method_argc_err();
  if (inst_of(MC_ARG(0)) != consts.cl_str)  method_bad_arg_err(MC_ARG(0));

  bool_new(MC_RESULT,
	   inst_of(MC_ARG(1)) == consts.cl_str
	   && STR(MC_ARG(0))->size == STR(MC_ARG(1))->size
	   && memcmp(STR(MC_ARG(0))->data, STR(MC_ARG(1))->data, STR(MC_ARG(0))->size) == 0
	   );
}

void
cm_str_tostring(void)
{
  obj_assign(MC_RESULT, MC_ARG(0));
}

void
cm_str_eval(void)
{
  if (MC_ARGC != 1)                         method_argc_err();
  if (inst_of(MC_ARG(0)) != consts.cl_str)  method_bad_arg_err(MC_ARG(0));

  obj_assign(MC_RESULT, str_eval(MC_ARG(0)));
}

void
cm_str_set(void)
{
  WORK_FRAME_DECL(work, 1);

  WORK_FRAME_PUSH(work);

  inst_method_call(&WORK(work, 0), consts.str_eval, 1, &MC_ARG(1));

  str_bind(MC_ARG(0), WORK(work, 0));

  obj_assign(MC_RESULT, WORK(work, 0));
  
  WORK_FRAME_POP();
}

/***************************************************************************/

void
dptr_new(obj_t *result, obj_t cl, obj_t car, obj_t cdr)
{
  WORK_FRAME_DECL(work, 1);

  WORK_FRAME_PUSH(work);

  inst_alloc(&WORK(work, 0), cl);
  obj_assign(&CAR(WORK(work, 0)), car);
  obj_assign(&CDR(WORK(work, 0)), cdr);

  obj_assign(result, WORK(work, 0));
  
  WORK_FRAME_POP();
}

void
dptr_init(obj_t self, obj_t cl, unsigned argc, va_list ap)
{
}

void
dptr_walk(obj_t obj, void (*func)(obj_t obj))
{
  (*func)(CAR(obj));
  (*func)(CDR(obj));
}

/***************************************************************************/

void
pair_new(obj_t *result, obj_t car, obj_t cdr)
{
  dptr_new(result, consts.cl_pair, car, cdr);
}

void
cm_pair_tostring(void)
{
  WORK_FRAME_DECL(work, 5);

  WORK_FRAME_PUSH(work);

  str_newc(&WORK(work, 0), 1, 2, "(");
  inst_method_call(&WORK(work, 1), consts.str_tostring, 1, &CAR(MC_ARG(0)));
  str_newc(&WORK(work, 2), 1, 3, ", ");
  inst_method_call(&WORK(work, 3), consts.str_tostring, 1, &CDR(MC_ARG(0)));
  str_newc(&WORK(work, 4), 1, 2, ")");

  str_newv(MC_RESULT, 5, &WORK(work, 0));

  WORK_FRAME_POP();
}

/***************************************************************************/

void
list_new(obj_t *result, obj_t car, obj_t cdr)
{
  dptr_new(result, consts.cl_list, car, cdr);
}

unsigned
is_list(obj_t obj)
{
  return (obj == 0 || inst_of(obj) == consts.cl_list);
}

unsigned
list_len(obj_t li)
{
  unsigned result;

  for (result = 0; li != 0; li = CDR(li), ++result);

  return (result);
}

void
cm_list_tostring(void)
{
  unsigned n, nn, i;
  obj_t    p, *q;

  n = list_len(MC_ARG(0));
  nn = 1 + (n > 1 ? 2 * n - 1 : n) + 1;

  WORK_FRAME_DECL(work, 1 + nn);

  _work_frame_push(work->base, 1 + nn);

  str_newc(&WORK(work, 0), 1, 2, " ");

  q = &WORK(work, 1);

  str_newc(q, 1, 2, "(");  ++q;
  for (i = 0, p = MC_ARG(0); p; p = CDR(p), ++i) {
    if (i > 0) {
      obj_assign(q, WORK(work, 0));  ++q;
    }
    
    inst_method_call(q, consts.str_tostring, 1, &CAR(p));  ++q;
  }
  str_newc(q, 1, 2, ")");

  str_newv(MC_RESULT, nn, &WORK(work, 1));

  WORK_FRAME_POP();
}

/***************************************************************************/

void
array_init(obj_t self, obj_t cl, unsigned argc, va_list ap)
{
  unsigned size;

  assert(argc > 0);

  size = va_arg(ap, unsigned);  --argc;

  ARRAY(self)->size = size;
  ARRAY(self)->data = ool_mem_allocz(size * sizeof(ARRAY(self)->data[0]));

  inst_init_parent(self, cl, argc, ap);
}

static inline void
_array_init(obj_t self, unsigned argc, ...)
{
  va_list ap;

  va_start(ap, argc);

  array_init(self, consts.cl_array, argc, ap);

  va_end(ap);
}

void
array_new(obj_t *dst, unsigned size)
{
  inst_alloc(dst, consts.cl_array);
  _array_init(*dst, 1, size);
}


void
array_copy(obj_t *dst, obj_t src)
{
  obj_t    *p, *q;
  unsigned n;

  WORK_FRAME_DECL(work, 1);

  WORK_FRAME_PUSH(work);

  array_new(&WORK(work, 0), ARRAY(src)->size);
  
  for (q = ARRAY(WORK(work, 0))->data, p = ARRAY(src)->data, n = ARRAY(src)->size;
       n;
       --n, ++p, ++q
       ) {
    inst_method_call(q, consts.str_copy, 1, p);
  }

  obj_assign(dst, WORK(work, 0));

  WORK_FRAME_POP();
}

void
array_walk(obj_t a, void (*func)(obj_t obj))
{
  obj_t    *p;
  unsigned n;

  for (p = ARRAY(a)->data, n = ARRAY(a)->size; n; --n, ++p) {
    (*func)(*p);
  }
}

void
array_free(obj_t a)
{
  ool_mem_free(ARRAY(a)->data, ARRAY(a)->size * sizeof(ARRAY(a)->data[0]));
}

/***************************************************************************/

void
set_init(obj_t self, obj_t cl, unsigned argc, va_list ap)
{
  inst_init_parent(self, cl, argc, ap);
}

/***************************************************************************/

enum {
  DICT_DFLT_SIZE = 32
};

unsigned
round_up_to_power_of_2(unsigned n)
{
  unsigned nn;

  if (n <= 2)  return (n);

  for (--n;;) {
    nn = n & (n - 1);
    if (nn == 0)  return (n << 1);
    n = nn;
  }
}

obj_t *
dict_find(obj_t dict, obj_t key, obj_t **bucket)
{
  obj_t *result = 0, *p, q;

  WORK_FRAME_DECL(work, 1);

  WORK_FRAME_PUSH(work);

  inst_method_call(&WORK(work, 0), consts.str_hash, 1, &key);
  p = &DICT(dict)->base->base->data[INT(WORK(work, 0))->val & (DICT(dict)->base->base->size - 1)];

  if (bucket)  *bucket = p;

  for ( ; q = *p; p = &CDR(q)) {
    inst_method_call(&WORK(work, 0), consts.str_equalc, 1, &key);
    if (BOOL(WORK(work, 0))->val) {
      result = p;
      break;
    }
  }

  WORK_FRAME_POP();

  return (result);
}


void
dict_init(obj_t self, obj_t cl, unsigned argc, va_list ap)
{
  assert(argc > 0);

  DICT(self)->find = va_arg(ap, obj_t *(*)(obj_t, obj_t, obj_t **));
  --argc;
  
  inst_init_parent(self, cl, argc, ap);
}

static inline void
_dict_init(obj_t self, unsigned argc, ...)
{
  va_list ap;

  va_start(ap, argc);

  dict_init(self, consts.cl_dict, argc, ap);

  va_end(ap);
}

void
_dict_new(obj_t *dst, obj_t *(*find)(obj_t, obj_t, obj_t **), unsigned size)
{
  inst_alloc(dst, consts.cl_dict);
  _dict_init(*dst, 2, find, round_up_to_power_of_2(size));
}

void
dict_new(obj_t *dst, unsigned size)
{
  inst_alloc(dst, consts.cl_dict);
  _dict_init(*dst, 2, dict_find, round_up_to_power_of_2(size));
}



obj_t
dict_at(obj_t dict, obj_t key)
{
  obj_t *p = (*DICT(dict)->find)(dict, key, 0);

  return (p ? CAR(*p) : 0);
}

void
dict_at_put(obj_t dict, obj_t key, obj_t val)
{
  obj_t *b;
  obj_t *p = (*DICT(dict)->find)(dict, key, &b);

  if (p == 0) {
    WORK_FRAME_DECL(work, 2);

    WORK_FRAME_PUSH(work);

    pair_new(&WORK(work, 0), key, val);
    list_new(&WORK(work, 1), WORK(work, 0), *b);

    obj_assign(b, WORK(work, 1));

    ++DICT(dict)->base->cnt;

    WORK_FRAME_POP();

    return;
  }

  if (inst_of(key) == consts.cl_str && STR(key)->size > 1 && STR(key)->data[0] == '#') {
    fprintf(stderr, "Attempt to set constant: %s\n", STR(key)->data);

    error();
  }

  obj_assign(&CDR(CAR(*p)), val);
}

void
dict_del(obj_t dict, obj_t key)
{
  obj_t *b;
  obj_t *p = (*DICT(dict)->find)(dict, key, &b);

  if (p == 0)  return;

  obj_assign(p, CDR(*p));
}

/***************************************************************************/

void
method_call_init(obj_t self, obj_t cl, unsigned argc, va_list ap)
{
  obj_assign(&METHOD_CALL(self)->sel,  va_arg(ap, obj_t));  --argc;
  obj_assign(&METHOD_CALL(self)->args, va_arg(ap, obj_t));  --argc;

  inst_init_parent(self, cl, argc, ap);
}

static inline void
_method_call_init(obj_t self, unsigned argc, ...)
{
  va_list ap;

  va_start(ap, argc);

  method_call_init(self, consts.cl_method_call, argc, ap);

  va_end(ap);
}

void
method_call_new(obj_t *dst, obj_t sel, obj_t args)
{
  inst_alloc(dst, consts.cl_method_call);
  _method_call_init(*dst, 2, sel, args);
}

void
cm_mc_eval(void)
{
  unsigned n, k;
  obj_t    sel, p, *q;
  unsigned quotef = false, macrof = false;

  if (MC_ARGC != 1)  method_argc_err();
  if (inst_of(MC_ARG(0)) != consts.cl_method_call)  method_bad_arg_err(MC_ARG(0));
  
  sel = METHOD_CALL(MC_ARG(0))->sel;

  if (quotef = (STR(sel)->size >= 2 && STR(sel)->data[0] == '&')) {
    macrof = STR(sel)->size >= 3 && STR(sel)->data[1] == '&';
  }
  
  n = list_len(METHOD_CALL(MC_ARG(0))->args);

  {
    WORK_FRAME_DECL(work, n);

    _work_frame_push(work->base, n);

    for (p = METHOD_CALL(MC_ARG(0))->args, q = &WORK(work, 0), k = n;
	 k > 0; 
	 --k, ++q, p = CDR(p)
	 ) {
      if (quotef) {
	obj_assign(q, CAR(p));
      } else {
	inst_method_call(q, consts.str_eval, 1, &CAR(p));
      }
    }

    if (macrof) {
      inst_method_call(&WORK(work, 0), sel, n, &WORK(work, 0));
      inst_method_call(MC_RESULT, consts.str_eval, 1, &WORK(work, 0));
    } else {
      inst_method_call(MC_RESULT, sel, n, &WORK(work, 0));
    }
    
    WORK_FRAME_POP();
  }
}

void
cm_mc_tostring(void)
{
  unsigned n, nn, k, i;
  obj_t    p, *q;
  char     *r, *rr;

  n = list_len(METHOD_CALL(MC_ARG(0))->args);
  nn = 1 + (n > 1 ? 4 * n - 3 : 4 * n - 1) + 1;

  WORK_FRAME_DECL(work, 1 + nn);

  _work_frame_push(work->base, 1 + nn);

  str_newc(&WORK(work, 0), 1, 2, " ");

  q = &WORK(work, 1);

  r = STR(METHOD_CALL(MC_ARG(0))->sel)->data;
  str_newc(q, 1, 2, "[");  ++q;
  for (i = 0, p = METHOD_CALL(MC_ARG(0))->args; i < 2 || p != 0; ++i) {
    if (i > 0) {
      obj_assign(q, WORK(work, 0));  ++q;
    }

    if (i & 1) {
      if ((rr = index(r, ':')) != 0) {
	++rr;

	{
	  unsigned ss = rr - r;
	  char     buf[ss + 1];
	  
	  memcpy(buf, r, ss);
	  buf[ss] = 0;
	  str_newc(q, 1, ss + 1, buf);
	  
	  r = rr;
	}
      } else {
	str_newc(q, 1, strlen(r) + 1, r);
      }

      ++q;

      continue;
    }

    inst_method_call(q, consts.str_tostring, 1, &CAR(p));  ++q;  p = CDR(p);
  }
  str_newc(q, 1, 2, "]");
  
  str_newv(MC_RESULT, nn, &WORK(work, 1));

  WORK_FRAME_POP();  
}

/***************************************************************************/

void
block_init(obj_t self, obj_t cl, unsigned argc, va_list ap)
{
  assert(argc > 1);
  
  obj_assign(&BLOCK(self)->args, va_arg(ap, obj_t));  --argc;
  BLOCK(self)->argc = list_len(BLOCK(self)->args);
  obj_assign(&BLOCK(self)->body, va_arg(ap, obj_t));  --argc;

  inst_init_parent(self, cl, argc, ap);
}

static inline void
_block_init(obj_t self, unsigned argc, ...)
{
  va_list ap;

  va_start(ap, argc);

  block_init(self, consts.cl_block, argc, ap);

  va_end(ap);
}

void
block_new(obj_t *dst, obj_t args, obj_t body)
{
  inst_alloc(dst, consts.cl_block);
  _block_init(*dst, 2, args, body);
}

void
cm_blk_eval(void)
{
  obj_t p, q;

  WORK_FRAME_DECL(work, 2);

  if (!is_list(MC_ARG(1)))  method_bad_arg_err(MC_ARG(1));
  if (list_len(MC_ARG(1)) != BLOCK(MC_ARG(0))->argc)  method_argc_err();

  WORK_FRAME_PUSH(work);

  strdict_new(&WORK(work, 0), 64);

  {
    struct block_frame blkfr[1];

    block_frame_push(blkfr, WORK(work, 0));

    for (p = BLOCK(MC_ARG(0))->args, q = MC_ARG(1); p; p = CDR(p), q = CDR(q)) {
      inst_method_call(&WORK(work, 1), consts.str_eval, 1, &CAR(q));
      dict_at_put(WORK(work, 0), CAR(p), WORK(work, 1));
    }

    for (p = BLOCK(MC_ARG(0))->body; p; p = CDR(p)) {
      inst_method_call(&WORK(work, 1), consts.str_eval, 1, &CAR(p));      
    }

    obj_assign(MC_RESULT, WORK(work, 1));

    block_frame_pop();
  }
  
  WORK_FRAME_POP();
}

/***************************************************************************/

void
module_init(obj_t self, obj_t cl, unsigned argc, va_list ap)
{
  assert(argc > 1);

  obj_assign(&MODULE(self)->name,   va_arg(ap, obj_t));  --argc;
  obj_assign(&MODULE(self)->parent, va_arg(ap, obj_t));  --argc;

  inst_init_parent(self, cl, argc, ap);
}

static inline void
_module_init(obj_t self, unsigned argc, ...)
{
  va_list ap;

  va_start(ap, argc);

  module_init(self, consts.cl_module, argc, ap);

  va_end(ap);    
}

void
module_new(obj_t *dst, obj_t name, obj_t parent)
{
  WORK_FRAME_DECL(work, 1);

  WORK_FRAME_PUSH(work);

  inst_alloc(&WORK(work, 0), consts.cl_module);
  _module_init(WORK(work, 0), 2, name, parent);

  obj_assign(dst, WORK(work, 0));

  WORK_FRAME_POP();
}

void
cm_module_tostring(void)
{
  obj_assign(MC_RESULT, MODULE(MC_ARG(0))->name);
}

/***************************************************************************/

void
code_method_new(obj_t *result, void (*func)(void))
{
  inst_alloc(result, consts.cl_code_method);

  CODE_METHOD(*result)->func = func;
}

void
code_method_init(obj_t self, obj_t cl, unsigned argc, va_list ap)
{
}

/***************************************************************************/

obj_t
method_find(obj_t cl, unsigned dofs, obj_t sel, obj_t *found_cl)
{
  obj_t p;

  *found_cl = cl;

  for ( ; cl; cl = CLASS(cl)->parent) {
    if (p = dict_at(*(obj_t *)((char *) cl + dofs), sel)) {
      *found_cl = cl;
      return (CDR(p));
    }
  }
  
  return (0);
}

obj_t
_method_run(obj_t m, obj_t *result, obj_t cl, obj_t sel, unsigned argc, obj_t *argv)
{
  if (inst_of(m) == consts.cl_code_method) {
    (*CODE_METHOD(m)->func)();
  } else if (inst_of(m) == consts.cl_block) {
    obj_t *p;

    WORK_FRAME_DECL(work, 2);

    WORK_FRAME_PUSH(work);

    obj_assign(&WORK(work, 0), m);

    for (p = &WORK(work, 1); argc; --argc, ++argv) {
      list_new(p, *argv, 0);
      p = &CDR(*p);
    }

    inst_method_call(result, consts.str_evalc, 2, &WORK(work, 0));

    WORK_FRAME_POP();
  } else {
    fprintf(stderr, "Invalid method definition\n");

    error();
  }
}

obj_t
method_run(obj_t m, obj_t *result, obj_t cl, obj_t sel, unsigned argc, obj_t *argv)
{
  if (modfp->module != CLASS(cl)->module) {
    struct module_frame fr[1];

    module_frame_push(fr, CLASS(cl)->module);

    _method_run(m, result, cl, sel, argc, argv);

    module_frame_pop();
  } else {
    _method_run(m, result, cl, sel, argc, argv);
  }
}

obj_t
inst_method_call(obj_t *result, obj_t sel, unsigned argc, obj_t *argv)
{
  obj_t cl;
  obj_t m = method_find(inst_of(argv[0]), offsetof(struct class, inst_methods), sel, &cl);
  struct method_call_frame mcfr[1];

  method_call_frame_push(mcfr, result, cl, sel, argc, argv);

  if (m == 0) {
    fprintf(stderr, "Method not found: %s.%s\n", STR(CLASS(inst_of(argv[0]))->name)->data, STR(sel)->data);
    
    error();
  }

  method_run(m, result, cl, sel, argc, argv);

  method_call_frame_pop();
}

/***************************************************************************/

void
cm_metaclass_tostring(void)
{
  obj_assign(MC_RESULT, CLASS(MC_ARG(0))->name);
}

void
cm_metaclass_new(void)
{
}

/***************************************************************************/

void
backtrace(void)
{
  struct method_call_frame *p;
  obj_t                    *a;
  unsigned                 n;

  WORK_FRAME_DECL(work, 1);

  WORK_FRAME_PUSH(work);

  for (p = mcfp; p; p = p->prev) {
    fprintf(stderr, "%s.%s.%s(",
	    STR(MODULE(CLASS(p->cl)->module)->name)->data,
	    STR(CLASS(p->cl)->name)->data,
	    STR(p->sel)->data
	    );
    
    for (a = p->argv, n = p->argc; n; --n, ++a) {
      if (n < p->argc)  fprintf(stderr, ", ");
      inst_method_call(&WORK(work, 0), consts.str_tostring, 1, a);
      fprintf(stderr, "%s", STR(WORK(work, 0))->data);
    }

    fprintf(stderr, ")\n");
  }

  WORK_FRAME_POP();
}

void
error(void)
{
  backtrace();

  abort();
}

/***************************************************************************/

struct {
  obj_t *var;
  char  *str;
} init_str_tbl[] = {
  { &consts.str_addc,        "add:" },
  { &consts.str_array,       "#Array" },
  { &consts.str_atc,         "at:" },
  { &consts.str_block,       "#Block" },
  { &consts.str_boolean,     "#Boolean" },
  { &consts.str_code_method, "#Code_Method" },
  { &consts.str_copy,        "copy" },
  { &consts.str_dict,        "#Dictionary" },
  { &consts.str_dptr,        "#Dptr" },
  { &consts.str_equalc,      "equal:" },
  { &consts.str_eval,        "eval" },
  { &consts.str_evalc,       "eval:" },
  { &consts.str_hash,        "hash" },
  { &consts.str_inst_of,     "instance-of" },
  { &consts.str_integer,     "#Integer" },
  { &consts.str_list,        "#List" },
  { &consts.str_main,        "#main" },
  { &consts.str_metaclass,   "#Metaclass" },
  { &consts.str_method_call, "#Method_Call" },
  { &consts.str_module,      "#Module" },
  { &consts.str_newc_instance_variablesc, "new:instance-variables:" },
  { &consts.str_object,      "#Object" },
  { &consts.str_pair,        "#Pair" },
  { &consts.str_quote,       "&quote" },
  { &consts.str_set,         "#Set" },
  { &consts.str_setc,        "&set:" },
  { &consts.str_string,      "#String" },
  { &consts.str_tostring,    "tostring" }
};

struct {
  obj_t    *var;
  obj_t    *name;
  obj_t    *parent;
  unsigned inst_size;
  void     (*init)(obj_t self, obj_t cl, unsigned argc, va_list ap);
  void     (*copy)(obj_t *dst, obj_t src);
  void     (*walk)(obj_t obj, void (*func)(obj_t obj));
  void     (*free)(obj_t obj);
} init_cl_tbl[] = {
  { &consts.cl_object,      &consts.str_object,      0,                 0,                               object_init },
  { &consts.cl_bool,        &consts.str_boolean,     &consts.cl_object, sizeof(struct inst_bool),        bool_init },
  { &consts.cl_int,         &consts.str_integer,     &consts.cl_object, sizeof(struct inst_int),         int_init },
  { &consts.cl_str,         &consts.str_string,      &consts.cl_object, sizeof(struct inst_str),         str_init },
  { &consts.cl_dptr,        &consts.str_dptr,        &consts.cl_object, 0,                               dptr_init },
  { &consts.cl_pair,        &consts.str_pair,        &consts.cl_dptr,   sizeof(struct inst_dptr),        inst_init_parent },
  { &consts.cl_list,        &consts.str_list,        &consts.cl_dptr,   sizeof(struct inst_dptr),        inst_init_parent },
  { &consts.cl_array,       &consts.str_array,       &consts.cl_object, sizeof(struct inst_array),       array_init },
  { &consts.cl_set,         &consts.str_set,         &consts.cl_array,  sizeof(struct inst_set),         set_init },
  { &consts.cl_dict,        &consts.str_dict,        &consts.cl_set,    sizeof(struct inst_dict),        dict_init },
  { &consts.cl_code_method, &consts.str_code_method, &consts.cl_object, sizeof(struct inst_code_method), code_method_init },
  { &consts.cl_method_call, &consts.str_method_call, &consts.cl_object, sizeof(struct inst_method_call), method_call_init },
  { &consts.cl_block,       &consts.str_block,       &consts.cl_object, sizeof(struct inst_block),       block_init },
  { &consts.cl_module,      &consts.str_module,      &consts.cl_dict,   sizeof(struct inst_module),      module_init }
};

struct {
  obj_t    *var;
  unsigned dofs;
  obj_t    *sel;
  void     (*func)(void);
} init_method_tbl[] = {
  { &consts.metaclass, offsetof(struct class, cl_methods), &consts.str_newc_instance_variablesc,  cm_metaclass_new },

  { &consts.metaclass, offsetof(struct class, inst_methods), &consts.str_tostring,  cm_metaclass_tostring },

  { &consts.cl_object, offsetof(struct class, inst_methods), &consts.str_inst_of,  cm_obj_inst_of },
  { &consts.cl_object, offsetof(struct class, inst_methods), &consts.str_quote,    cm_obj_quote },
  { &consts.cl_object, offsetof(struct class, inst_methods), &consts.str_eval,     cm_obj_eval },
  { &consts.cl_object, offsetof(struct class, inst_methods), &consts.str_copy,     cm_obj_copy },
  { &consts.cl_object, offsetof(struct class, inst_methods), &consts.str_tostring, cm_obj_tostring },

  { &consts.cl_int, offsetof(struct class, inst_methods), &consts.str_addc,     cm_int_add },
  { &consts.cl_int, offsetof(struct class, inst_methods), &consts.str_tostring, cm_int_tostring },

  { &consts.cl_str, offsetof(struct class, inst_methods), &consts.str_eval,     cm_str_eval },
  { &consts.cl_str, offsetof(struct class, inst_methods), &consts.str_tostring, cm_str_tostring },
  { &consts.cl_str, offsetof(struct class, inst_methods), &consts.str_setc,     cm_str_set },

  { &consts.cl_pair, offsetof(struct class, inst_methods), &consts.str_tostring, cm_pair_tostring },

  { &consts.cl_list, offsetof(struct class, inst_methods), &consts.str_tostring, cm_list_tostring },

  { &consts.cl_method_call, offsetof(struct class, inst_methods), &consts.str_tostring, cm_mc_tostring },
  { &consts.cl_method_call, offsetof(struct class, inst_methods), &consts.str_eval,     cm_mc_eval },

  { &consts.cl_module, offsetof(struct class, inst_methods), &consts.str_tostring, cm_module_tostring },

  { &consts.cl_block, offsetof(struct class, inst_methods), &consts.str_evalc, cm_blk_eval }
};


void
init_dict(obj_t d, unsigned size)
{
  DICT(d)->base->base->size = size;
  DICT(d)->base->base->data = ool_mem_allocz(size * sizeof(obj_t));
  DICT(d)->find             = strdict_find;
}

void
init_cl(obj_t cl, unsigned dict_size)
{
  obj_t obj;

  obj_assign(&cl->inst_of, consts.metaclass);
  obj_assign(&CLASS(cl)->cl_vars, obj = (obj_t) ool_mem_allocz(sizeof(struct inst_dict)));
  init_dict(obj, dict_size);
  obj_assign(&CLASS(cl)->cl_methods, obj = (obj_t) ool_mem_allocz(sizeof(struct inst_dict)));
  init_dict(obj, dict_size);
  obj_assign(&CLASS(cl)->inst_vars, obj = (obj_t) ool_mem_allocz(sizeof(struct inst_dict)));
  init_dict(obj, dict_size);
  obj_assign(&CLASS(cl)->inst_methods, obj = (obj_t) ool_mem_allocz(sizeof(struct inst_dict)));
  init_dict(obj, dict_size);
}


void
init_cl_2(obj_t cl)
{
  obj_assign(&CLASS(cl)->cl_vars->inst_of,      consts.cl_dict);
  obj_assign(&CLASS(cl)->cl_methods->inst_of,   consts.cl_dict);
  obj_assign(&CLASS(cl)->inst_vars->inst_of,    consts.cl_dict);
  obj_assign(&CLASS(cl)->inst_methods->inst_of, consts.cl_dict);
}

void
init(void)
{
  unsigned i;

  WORK_FRAME_DECL(work, 2);

  WORK_FRAME_PUSH(work);

  /* Create main module */

  obj_assign(&consts.module_main, (obj_t) ool_mem_allocz(sizeof(struct inst_module)));
  init_dict(consts.module_main, 64);

  /* Create metaclass */

  obj_assign(&consts.metaclass, (obj_t) ool_mem_allocz(sizeof(struct class)));
  init_cl(consts.metaclass, 32);

  /* Create classes, pass 1 - Allocate classes, some init */

  for (i = 0; i < ARRAY_SIZE(init_cl_tbl); ++i) {
    obj_t cl;

    obj_assign(init_cl_tbl[i].var, cl = (obj_t) ool_mem_allocz(sizeof(struct class)));
    init_cl(cl, 32);
    obj_assign(&cl->inst_of, consts.metaclass);
    obj_assign(&CLASS(cl)->module, consts.module_main);
    obj_assign(&CLASS(cl)->parent, init_cl_tbl[i].parent ? *init_cl_tbl[i].parent : 0);
    CLASS(cl)->inst_size = init_cl_tbl[i].inst_size;
    list_init(CLASS(cl)->inst_cache);
    CLASS(cl)->init = init_cl_tbl[i].init;
    CLASS(cl)->walk = init_cl_tbl[i].walk;
    CLASS(cl)->free = init_cl_tbl[i].free;
  }

  /* Create classes, pass 2 - Fix-up instance-ofs */

  obj_assign(&consts.module_main->inst_of, consts.cl_module);
  init_cl_2(consts.metaclass);
  for (i = 0; i < ARRAY_SIZE(init_cl_tbl); ++i) {
    init_cl_2(*init_cl_tbl[i].var);
  }

  /* Fix up metaclass parentage */

  obj_assign(&CLASS(consts.metaclass)->parent, consts.cl_object);

  /* Create strings */

  for (i = 0; i < ARRAY_SIZE(init_str_tbl); ++i) {
    str_newc(init_str_tbl[i].var, 1, strlen(init_str_tbl[i].str) + 1, init_str_tbl[i].str);
  }

  /* Create classes, pass 3 - Create methods */

  for (i = 0; i < ARRAY_SIZE(init_method_tbl); ++i) {
    code_method_new(&WORK(work, 1), init_method_tbl[i].func);
    dict_at_put(*(obj_t *)((char *)(*init_method_tbl[i].var) + init_method_tbl[i].dofs), *init_method_tbl[i].sel, WORK(work, 1));
  }

  /* Add everything to main module */

  obj_assign(&MODULE(consts.module_main)->name, consts.str_main);
  dict_at_put(consts.module_main, consts.str_main, consts.module_main);

  obj_assign(&CLASS(consts.metaclass)->name, consts.str_metaclass);
  dict_at_put(consts.module_main, consts.str_metaclass, consts.metaclass);

  for (i = 0; i < ARRAY_SIZE(init_cl_tbl); ++i) {
    obj_t cl = *init_cl_tbl[i].var, nm = *init_cl_tbl[i].name;

    obj_assign(&CLASS(cl)->name, nm);
    dict_at_put(consts.module_main, nm, cl);
  }

  WORK_FRAME_POP();
}

int
main(void)
{
  struct module_frame modfr[1];

  WORK_FRAME_DECL(work, 10);

  init();

  module_frame_push(modfr, consts.module_main);

  WORK_FRAME_PUSH(work);

#if 1
  {
    struct stream_file str[1];
    struct parse_ctxt  pc[1];

    stream_file_init(str, stdin);

    parse_ctxt_init(pc, str->base);

    for (;;) {
      parse(&WORK(work, 0), pc);

      inst_method_call(&WORK(work, 1), consts.str_eval, 1, &WORK(work, 0));
      inst_method_call(&WORK(work, 2), consts.str_tostring, 1, &WORK(work, 1));

      puts(STR(WORK(work, 2))->data);
    }
  }
#endif

#if 0
  inst_new(&WORK(work, consts.cl_int, 0), 13);
  inst_new(&WORK(work, consts.cl_int, 1), 42);

  inst_method_call(&WORK(work, 2), consts.str_addc, 2, &WORK(work, 0));
  inst_method_call(&WORK(work, 3), consts.str_tostring, 1, &WORK(work, 2));

  printf("%s\n", STR(WORK(work, 3))->data);

#endif

#if 0
  inst_new(&WORK(work, consts.cl_int, 0), 13);
  str_newc(&WORK(work, 1), 1, 4, "foo");

  inst_method_call(&WORK(work, 2), consts.str_addc, 1, &WORK(work, 0));
  inst_method_call(&WORK(work, 3), consts.str_tostring, 1, &WORK(work, 2));

  printf("%s\n", STR(WORK(work, 3))->data);

#endif

#if 0
  printf("%s\n", STR(MODULE(str_eval(consts.str_main))->name)->data);
#endif

#if 0
  inst_new(&WORK(work, consts.cl_int, 0), 13);
  str_newc(&WORK(work, 1), 1, 4, "foo");
  inst_method_call(&WORK(work, 2), WORK(work, 1), 1, &WORK(work, 0));
#endif

  WORK_FRAME_POP();

  module_frame_pop();
    
  return (0);
}
