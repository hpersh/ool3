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
  if (++err_depth > 1)  double_err();

  WORK_FRAME_DECL(work, 1);

  work_frame_push(work);

  inst_method_call(&WORK(work, 0), consts.str_tostring, 1, &arg);

  fprintf(stderr, "Bad argument: %s\n", STR(WORK(work, 0))->data);

  work_frame_pop();
  
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

  void *result = malloc(size);

  assert(result != 0);
  
  return (result);
}

void *
ool_mem_allocz(unsigned size)
{
  void *result = ool_mem_alloc(size);

  memset(result, 0, size);

  return (result);
}

/***************************************************************************/

obj_t
base_class_same_inst_size(obj_t cl)
{
  obj_t    result;
  unsigned s = CLASS(cl)->inst_size;

  for (cl = CLASS(result = cl)->parent; cl != 0 && CLASS(cl)->inst_size == s; cl = CLASS(cl)->parent) {
    result = cl;
  }

  return (result);
}

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
}

void
inst_alloc(obj_t *dst, obj_t cl)
{
  if (CLASS(cl)->flags & CLASS_FLAG_NO_INST) {
    fprintf(stderr, "Cannot instantiate class %s\n", STR(CLASS(cl)->name)->data);
    error();
  }

  unsigned    size        = CLASS(cl)->inst_size;
  struct list *inst_cache = CLASS(cl)->inst_cache;
  obj_t       p;

  if (list_empty(inst_cache)) {
    p = (obj_t) ool_mem_allocz(size);
  } else {
    struct list *q = list_first(inst_cache);

    list_erase(q);

    p = CONTAINER_OF(q, struct obj, list_node);

    memset(p, 0, size);
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

void
inst_init(obj_t self, unsigned argc, ...)
{
  obj_t   cl = inst_of(self);
  va_list ap;

  va_start(ap, argc);

  (*CLASS(cl)->init)(self, cl, argc, ap);

  va_end(ap);
}

/***************************************************************************/

void
object_init(obj_t self, obj_t cl, unsigned argc, va_list ap)
{
  assert(argc == 0);
}

void
object_free(obj_t obj)
{
  obj_t cl = inst_of(obj);

  obj_release(cl);
  
  list_insert(obj->list_node, CLASS(cl)->inst_cache);
}

void
cm_obj_inst_of(void)
{
  if (MC_ARGC != 1)  method_argc_err();

  obj_assign(MC_RESULT, inst_of(MC_ARG(0)));
}

void
cm_obj_quote(void)
{
  if (MC_ARGC != 1)  method_argc_err();
  
  obj_assign(MC_RESULT, MC_ARG(0));
}

void
cm_obj_eval(void)
{
  if (MC_ARGC != 1)  method_argc_err();
  
  obj_assign(MC_RESULT, MC_ARG(0));
}

void
cm_obj_tostring(void)
{
  if (MC_ARGC != 1)  method_argc_err();

  if (MC_ARG(0) == 0) {
    str_newc(MC_RESULT, 1, 5, "#nil");

    return;
  }  

  char     *s = STR(CLASS(inst_of(MC_ARG(0)))->name)->data;
  unsigned n  = 1 + strlen(s) + 1 + 18 + 1 + 1;
  char     buf[n];
  
  snprintf(buf, n, "<%s@%p>", s, MC_ARG(0));
  
  str_newc(MC_RESULT, 1, strlen(buf) + 1, buf);
}

void
cm_obj_while(void)
{
  if (MC_ARGC != 2)  method_argc_err();

  WORK_FRAME_DECL(work, 2);
  
  work_frame_push(work);
  
  for (;;) {
    inst_method_call(&WORK(work, 0), consts.str_eval, 1, &MC_ARG(0));
    if (inst_of(WORK(work, 0)) == consts.cl_bool && !BOOL(WORK(work, 0))->val)  break;
    
    inst_method_call(&WORK(work, 1), consts.str_eval, 1, &MC_ARG(1));      
  }
  
  obj_assign(MC_RESULT, WORK(work, 1));
  
  work_frame_pop();
}

void
cm_obj_new(void)
{
  inst_alloc(MC_RESULT, MC_ARG(0));
}

obj_t *
inst_var_find(obj_t inst, obj_t inst_var)
{
  obj_t p = dict_at(CLASS(inst_of(inst))->inst_vars, inst_var);

  if (p == 0) {
    fprintf(stderr, "No such instance variable\n");

    error();
  }

  return ((obj_t *)((char *) inst + INT(CDR(p))->val));
}

void
cm_obj_at(void)
{
  obj_assign(MC_RESULT, *inst_var_find(MC_ARG(0), MC_ARG(1)));
}

void
cm_obj_atput(void)
{
  obj_assign(inst_var_find(MC_ARG(0), MC_ARG(1)), MC_ARG(2));

  obj_assign(MC_RESULT, MC_ARG(2));
}

/***************************************************************************/

void
bool_init(obj_t self, obj_t cl, unsigned argc, va_list ap)
{
  assert(argc > 0);

  BOOL(self)->val = (va_arg(ap, unsigned) != 0);  --argc;

  inst_init_parent(self, cl, argc, ap);
}

void
bool_new(obj_t *dst, unsigned val)
{
  inst_alloc(dst, consts.cl_bool);
  inst_init(*dst, 1, val);
}

void
cm_bool_newc(void)
{
  if (MC_ARGC != 2)  method_argc_err();
  
  obj_t cl = inst_of(MC_ARG(1));
  
  if (cl == consts.cl_bool) {
    obj_assign(MC_RESULT, MC_ARG(1));
    
    return;
  }

  unsigned val = 0;
  
  if (MC_ARG(1) != 0) {
    if (cl == consts.cl_int) {
      val = (INT(MC_ARG(1))->val != 0);
    } else if (cl == consts.cl_str) {
      val = (strcmp(STR(MC_ARG(1))->data, "#true") == 0);
    } else if (cl == consts.cl_list) {
      val = 1;
    } else  method_bad_arg_err(MC_ARG(1));
  }
	       
  bool_new(MC_RESULT, val);
}

void
cm_bool_tostring(void)
{
  if (MC_ARGC != 1)  method_argc_err();
  if (inst_of(MC_ARG(0)) != consts.cl_bool)  method_bad_arg_err(MC_ARG(0));

  char     *s;
  unsigned n;
  
  if (BOOL(MC_ARG(0))->val) {
    s = "#true";
    n = 6;
  } else {
    s = "#false";
    n = 7;
  }
  
  str_newc(MC_RESULT, 1, n, s);
}

void
cm_bool_eq(void)
{
  if (MC_ARGC != 2)  method_argc_err();
  if (inst_of(MC_ARG(0)) != consts.cl_bool)  method_bad_arg_err(MC_ARG(0));

  bool_new(MC_RESULT,
	   inst_of(MC_ARG(1)) == consts.cl_bool
	   && BOOL(MC_ARG(0))->val == BOOL(MC_ARG(1))->val
	   );
}

void
cm_bool_hash(void)
{
  if (MC_ARGC != 1)  method_argc_err();
  if (inst_of(MC_ARG(0)) != consts.cl_bool)  method_bad_arg_err(MC_ARG(0));

  int_new(MC_RESULT, BOOL(MC_ARG(0))->val);
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

void
int_new(obj_t *dst, intval_t val)
{
  inst_alloc(dst, consts.cl_int);
  inst_init(*dst, 1, val);
}

void
cm_int_new(void)
{
  if (MC_ARGC != 2)  method_argc_err();

  obj_t cl = inst_of(MC_ARG(1));

  if (cl == consts.cl_int) {
    obj_assign(MC_RESULT, MC_ARG(1));
    
    return;
  }

  intval_t val = 0;
  
  if (cl == consts.cl_bool) {
    val = (BOOL(MC_ARG(1))->val != 0);
  } else if (cl == consts.cl_float) {
    val = (intval_t) FLOAT(MC_ARG(1))->val;
  } else if (cl == consts.cl_str) {
    sscanf(STR(MC_ARG(1))->data, "%lld", &val);
  } else  method_bad_arg_err(MC_ARG(1));

  int_new(MC_RESULT, val);
}

void
cm_int_eq(void)
{
  if (MC_ARGC != 2)  method_argc_err();
  if (inst_of(MC_ARG(0)) != consts.cl_int)  method_bad_arg_err(MC_ARG(0));

  bool_new(MC_RESULT,
	   inst_of(MC_ARG(1)) == consts.cl_int
	   && INT(MC_ARG(0))->val == INT(MC_ARG(1))->val
	   );
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
cm_int_lt(void)
{
  if (MC_ARGC != 2)  method_argc_err();
  if (inst_of(MC_ARG(0)) != consts.cl_int)  method_bad_arg_err(MC_ARG(0));
  if (inst_of(MC_ARG(1)) != consts.cl_int)  method_bad_arg_err(MC_ARG(1));

  bool_new(MC_RESULT, INT(MC_ARG(0))->val < INT(MC_ARG(1))->val);
}

void
cm_int_tostring(void)
{
  if (MC_ARGC != 1)  method_argc_err();
  if (inst_of(MC_ARG(0)) != consts.cl_int)  method_bad_arg_err(MC_ARG(0));

  char buf[32];

  snprintf(buf, sizeof(buf), "%lld", INT(MC_ARG(0))->val);
  
  str_newc(MC_RESULT, 1, strlen(buf) + 1, buf);
}

/***************************************************************************/

void
float_init(obj_t self, obj_t cl, unsigned argc, va_list ap)
{
  assert(argc > 0);

  FLOAT(self)->val = va_arg(ap, floatval_t);  --argc;

  inst_init_parent(self, cl, argc, ap);
}

void
float_new(obj_t *dst, floatval_t val)
{
  inst_alloc(dst, consts.cl_float);
  inst_init(*dst, 1, val);
}


void
cm_float_new(void)
{
  if (MC_ARGC != 2)  method_argc_err();

  obj_t cl = inst_of(MC_ARG(1));

  if (cl == consts.cl_float) {
    obj_assign(MC_RESULT, MC_ARG(1));
    
    return;
  }

  floatval_t val = 0;
  
  if (cl == consts.cl_int) {
    val = (floatval_t) INT(MC_ARG(1))->val;
  } else if (cl == consts.cl_str) {
    sscanf(STR(MC_ARG(1))->data, "%Lg", &val);
  } else  method_bad_arg_err(MC_ARG(1));

  float_new(MC_RESULT, val);
}

void
cm_float_tostring(void)
{
  if (MC_ARGC != 1)  method_argc_err();
  if (inst_of(MC_ARG(0)) != consts.cl_float)  method_bad_arg_err(MC_ARG(0));

  char buf[64];

  snprintf(buf, sizeof(buf), "%Lg", FLOAT(MC_ARG(0))->val);

  str_newc(MC_RESULT, 1, strlen(buf) + 1, buf);
}

/***************************************************************************/

void
str_init(obj_t self, obj_t cl, unsigned argc, va_list ap)
{
  assert(argc > 0);

  obj_t arg = va_arg(ap, obj_t);  --argc;

  WORK_FRAME_DECL(work, 1);

  work_frame_push(work);

  inst_method_call(&WORK(work, 0), consts.str_tostring, 1, &arg);

  if (STR(self)->data)  ool_mem_free(STR(self)->data, STR(self)->size);

  STR(self)->size = STR(WORK(work, 0))->size;
  STR(self)->data = ool_mem_alloc(STR(self)->size);
  memcpy(STR(self)->data, STR(WORK(work, 0))->data, STR(self)->size);
  
  work_frame_pop();

  inst_init_parent(self, cl, argc, ap);
}

void
str_newc(obj_t *result, unsigned argc, ...)
{
  WORK_FRAME_DECL(work, 1);

  work_frame_push(work);

  va_list  ap;

  va_start(ap, argc);

  unsigned n, len;
  char     *s, *q;

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

  work_frame_pop();
}

void
str_newv(obj_t *result, unsigned argc, obj_t *argv)
{

  WORK_FRAME_DECL(work, 1);

  work_frame_push(work);

  unsigned n, len;
  obj_t    *p;
  char     *s, *q;

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

  work_frame_pop();
}

void
str_free(obj_t obj)
{
  ool_mem_free(STR(obj)->data, STR(obj)->size);
}

unsigned
str_hash(obj_t s)
{
  assert(inst_of(s) == consts.cl_str);

  unsigned result;
  char     *p, c;

  for (result = 0, p = STR(s)->data; (c = *p) != 0; ++p) {
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

  for ( ; (q = *p) != 0; p = &CDR(q)) {
    if (str_eq(CAR(CAR(q)), key))  return (p);
  }

  return (0);
}

unsigned
round_up_to_power_of_2(unsigned n)
{
  if (n <= 2)  return (n);

  for (--n;;) {
    unsigned nn = n & (n - 1);

    if (nn == 0)  return (n << 1);
    n = nn;
  }
}

enum {
  STRDICT_SIZE_DFLT = 32
};

void
strdict_new(obj_t *dst, unsigned size)
{
  inst_alloc(dst, consts.cl_dict);

  if (size == 0) {
    size = STRDICT_SIZE_DFLT;
  } else {
    size = round_up_to_power_of_2(size);
  }

  inst_init(*dst, 2, strdict_find, size);
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

  WORK_FRAME_DECL(work, 2);

  work_frame_push(work);

  obj_assign(&WORK(work, 0), consts.cl_env);
  obj_assign(&WORK(work, 1), MC_ARG(0));

  inst_method_call(MC_RESULT, consts.str_atc, 2, &WORK(work, 0));

  work_frame_pop();
}

/***************************************************************************/

void
dptr_new(obj_t *result, obj_t cl, obj_t car, obj_t cdr)
{
  WORK_FRAME_DECL(work, 1);

  work_frame_push(work);

  inst_alloc(&WORK(work, 0), cl);
  obj_assign(&CAR(WORK(work, 0)), car);
  obj_assign(&CDR(WORK(work, 0)), cdr);

  obj_assign(result, WORK(work, 0));
  
  work_frame_pop();
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
cm_pair_eval(void)
{
  WORK_FRAME_DECL(work, 2);

  work_frame_push(work);

  inst_method_call(&WORK(work, 0), consts.str_eval, 1, &CAR(MC_ARG(0)));
  inst_method_call(&WORK(work, 1), consts.str_eval, 1, &CDR(MC_ARG(0)));
  pair_new(MC_RESULT, WORK(work, 0), WORK(work, 1));

  work_frame_pop();
}

void
cm_pair_tostring(void)
{
  obj_t *a;

  WORK_FRAME_DECL(work, 1);

  work_frame_push(work);

  array_new(&WORK(work, 0), 5);
  a = ARRAY(WORK(work, 0))->data;

  str_newc(&a[0], 1, 2, "(");
  inst_method_call(&a[1], consts.str_tostring, 1, &CAR(MC_ARG(0)));
  str_newc(&a[2], 1, 3, ", ");
  inst_method_call(&a[3], consts.str_tostring, 1, &CDR(MC_ARG(0)));
  str_newc(&a[4], 1, 2, ")");

  str_newv(MC_RESULT, 5, a);

  work_frame_pop();
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
cm_list_new(void)
{
  
}

void
cm_list_eval(void)
{
  obj_t *p, q;

  WORK_FRAME_DECL(work, 2);

  work_frame_push(work);

  for (p = &WORK(work, 0), q = MC_ARG(0); q; q = CDR(q)) {
    inst_method_call(&WORK(work, 1), consts.str_eval, 1, &CAR(q));
    list_new(p, WORK(work, 1), 0);
    p = &CDR(*p);
  }

  obj_assign(MC_RESULT, WORK(work, 0));

  work_frame_pop();
}

void
cm_list_tostring(void)
{
  unsigned n, nn, i;
  obj_t    p, *a, *q;

  n = list_len(MC_ARG(0));
  nn = 1 + (n > 1 ? 2 * n - 1 : n) + 1;
  
  {
    WORK_FRAME_DECL(work, 1);

    work_frame_push(work);

    array_new(&WORK(work, 0), 1 + nn);
    a = ARRAY(WORK(work, 0))->data;

    q = a;
    str_newc(q, 1, 2, " ");  ++q;

    str_newc(q, 1, 2, "(");  ++q;
    for (i = 0, p = MC_ARG(0); p; p = CDR(p), ++i) {
      if (i > 0) {
	obj_assign(q, a[0]);  ++q;
      }
      
      inst_method_call(q, consts.str_tostring, 1, &CAR(p));  ++q;
    }
    str_newc(q, 1, 2, ")");
    
    str_newv(MC_RESULT, nn, a + 1);
    
    work_frame_pop();
  }
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

void
array_new(obj_t *dst, unsigned size)
{
  inst_alloc(dst, consts.cl_array);
  inst_init(*dst, 1, size);
}

void
array_walk(obj_t obj, void (*func)(obj_t))
{
  obj_t    *p;
  unsigned n;

  for (p = ARRAY(obj)->data, n = ARRAY(obj)->size; n > 0; --n, ++p) {
    (*func)(*p);
  }
}

void
array_free(obj_t obj)
{
  ool_mem_free(ARRAY(obj)->data, ARRAY(obj)->size * sizeof(ARRAY(obj)->data[0]));
}

/***************************************************************************/

void
set_init(obj_t self, obj_t cl, unsigned argc, va_list ap)
{
  inst_init_parent(self, cl, argc, ap);
}

/***************************************************************************/

void
dict_init(obj_t self, obj_t cl, unsigned argc, va_list ap)
{
  assert(argc > 0);

  DICT(self)->base->find = va_arg(ap, obj_t *(*)(obj_t, obj_t, obj_t **));  --argc;
  
  inst_init_parent(self, cl, argc, ap);
}

enum {
  DICT_SIZE_DFLT = 32
};

obj_t *
dict_find(obj_t dict, obj_t key, obj_t **bucket)
{
  obj_t *result = 0, *p, q;

  WORK_FRAME_DECL(work, 1);

  work_frame_push(work);

  inst_method_call(&WORK(work, 0), consts.str_hash, 1, &key);
  p = &DICT(dict)->base->base->data[INT(WORK(work, 0))->val & (DICT(dict)->base->base->size - 1)];

  if (bucket)  *bucket = p;

  for ( ; (q = *p) != 0; p = &CDR(q)) {
    inst_method_call(&WORK(work, 0), consts.str_equalc, 1, &key);
    if (BOOL(WORK(work, 0))->val) {
      result = p;
      break;
    }
  }

  work_frame_pop();

  return (result);
}

void
dict_new(obj_t *dst, unsigned size)
{
  inst_alloc(dst, consts.cl_dict);

  if (size == 0) {
    size = DICT_SIZE_DFLT;
  } else {
    size = round_up_to_power_of_2(size);
  }

  inst_init(*dst, 2, dict_find, size);
}

obj_t
dict_at(obj_t dict, obj_t key)
{
  obj_t *p = (*DICT(dict)->base->find)(dict, key, 0);

  return (p ? CAR(*p) : 0);
}

void
dict_at_put(obj_t dict, obj_t key, obj_t val)
{
  obj_t *b;
  obj_t *p = (*DICT(dict)->base->find)(dict, key, &b);

  if (p == 0) {
    WORK_FRAME_DECL(work, 2);

    work_frame_push(work);

    pair_new(&WORK(work, 0), key, val);
    list_new(&WORK(work, 1), WORK(work, 0), *b);

    obj_assign(b, WORK(work, 1));

    ++DICT(dict)->base->cnt;

    work_frame_pop();

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
  obj_t *p = (*DICT(dict)->base->find)(dict, key, &b);

  if (p == 0)  return;

  obj_assign(p, CDR(*p));

  --DICT(dict)->base->cnt;
}

void
cm_dict_at(void)
{
  obj_assign(MC_RESULT, dict_at(MC_ARG(0), MC_ARG(1)));
}

void
cm_dict_atput(void)
{
  dict_at_put(MC_ARG(0), MC_ARG(1), MC_ARG(2));

  obj_assign(MC_RESULT, MC_ARG(2));
}

/***************************************************************************/

void
method_call_init(obj_t self, obj_t cl, unsigned argc, va_list ap)
{
  obj_assign(&METHOD_CALL(self)->sel,  va_arg(ap, obj_t));  --argc;
  obj_assign(&METHOD_CALL(self)->args, va_arg(ap, obj_t));  --argc;

  inst_init_parent(self, cl, argc, ap);
}


void
method_call_walk(obj_t obj, void (*func)(obj_t))
{
  (*func)(METHOD_CALL(obj)->sel);
  (*func)(METHOD_CALL(obj)->args);
}

void
method_call_new(obj_t *dst, obj_t sel, obj_t args)
{
  WORK_FRAME_DECL(work, 1);

  work_frame_push(work);
  
  inst_alloc(&WORK(work, 0), consts.cl_method_call);
  inst_init(WORK(work, 0), 2, sel, args);

  obj_assign(dst, WORK(work, 0));

  work_frame_pop();
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

  if ((quotef = (STR(sel)->size >= 2 && STR(sel)->data[0] == '&'))) {
    macrof = STR(sel)->size >= 3 && STR(sel)->data[1] == '&';
  }
  
  n = list_len(METHOD_CALL(MC_ARG(0))->args);

  {
    WORK_FRAME_DECL(work, n);

    work_frame_push(work);

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
    
    work_frame_pop();
  }
}

void
cm_mc_tostring(void)
{
  unsigned n, nn, k, i;
  obj_t    p, *a, *q;
  char     *r, *rr;

  n = list_len(METHOD_CALL(MC_ARG(0))->args);
  nn = 1 + (n > 1 ? 4 * n - 3 : 4 * n - 1) + 1;

  {
    WORK_FRAME_DECL(work, 1);
    
    work_frame_push(work);
   
    array_new(&WORK(work, 0), 1 + nn);
    a = ARRAY(WORK(work, 0))->data;
 
    q = a;
    str_newc(q, 1, 2, " ");  ++q;
    
    r = STR(METHOD_CALL(MC_ARG(0))->sel)->data;
    str_newc(q, 1, 2, "[");  ++q;
    for (i = 0, p = METHOD_CALL(MC_ARG(0))->args; i < 2 || p != 0; ++i) {
      if (i > 0) {
	obj_assign(q, a[0]);  ++q;
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
    
    str_newv(MC_RESULT, nn, &a[1]);
    
    work_frame_pop();  
  }
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

void
block_walk(obj_t obj, void (*func)(obj_t))
{
  (*func)(BLOCK(obj)->args);
  (*func)(BLOCK(obj)->body);
}

void
block_new(obj_t *dst, obj_t args, obj_t body)
{
  WORK_FRAME_DECL(work, 1);

  work_frame_push(work);
  
  inst_alloc(&WORK(work, 0), consts.cl_block);
  inst_init(WORK(work, 0), 2, args, body);

  obj_assign(dst, WORK(work, 0));

  work_frame_pop();
}

void
cm_blk_eval(void)
{
  obj_t p, q;

  WORK_FRAME_DECL(work, 2);

  if (!is_list(MC_ARG(1)))  method_bad_arg_err(MC_ARG(1));
  if (list_len(MC_ARG(1)) != BLOCK(MC_ARG(0))->argc)  method_argc_err();

  work_frame_push(work);

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
  
  work_frame_pop();
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

void
module_walk(obj_t obj, void (*func)(obj_t))
{
  (*func)(MODULE(obj)->name);
  (*func)(MODULE(obj)->parent);
}

void
module_new(obj_t *dst, obj_t name, obj_t parent)
{
  WORK_FRAME_DECL(work, 1);

  work_frame_push(work);

  inst_alloc(&WORK(work, 0), consts.cl_module);
  inst_init(WORK(work, 0), 2, name, parent);

  obj_assign(dst, WORK(work, 0));

  work_frame_pop();
}

void
cm_module_name(void)
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
    if ((p = dict_at(*(obj_t *)((char *) cl + dofs), sel)) != 0) {
      *found_cl = cl;
      return (CDR(p));
    }
  }
  
  return (0);
}

void
_method_run(obj_t m, obj_t *result, obj_t cl, obj_t sel, unsigned argc, obj_t *argv)
{
  obj_t mcl = inst_of(m);

  if (mcl == consts.cl_code_method) {
    (*CODE_METHOD(m)->func)();

    return;
  }

  if (mcl == consts.cl_block) {
    obj_t *p;

    WORK_FRAME_DECL(work, 2);

    work_frame_push(work);

    obj_assign(&WORK(work, 0), m);

    for (p = &WORK(work, 1); argc; --argc, ++argv) {
      list_new(p, *argv, 0);
      p = &CDR(*p);
    }

    inst_method_call(result, consts.str_evalc, 2, &WORK(work, 0));

    work_frame_pop();

    return;
  }

  fprintf(stderr, "Invalid method definition\n");
  
  error();
}

void
method_run(obj_t m, obj_t *result, obj_t cl, obj_t sel, unsigned argc, obj_t *argv)
{
  if (modfp->module != CLASS(cl)->module) {
    struct module_frame fr[1];

    module_frame_push(fr, CLASS(cl)->module);

    _method_run(m, result, cl, sel, argc, argv);

    module_frame_pop();

    return;
  }

  _method_run(m, result, cl, sel, argc, argv);
}

void
inst_method_call(obj_t *result, obj_t sel, unsigned argc, obj_t *argv)
{
  obj_t cl;
  obj_t m = 0;
  struct method_call_frame mcfr[1];

  if (inst_of(argv[0]) == consts.metaclass) {
    m = method_find(argv[0], offsetof(struct class, cl_methods), sel, &cl);
  }
  if (m == 0) {
    m = method_find(inst_of(argv[0]), offsetof(struct class, inst_methods), sel, &cl);
  }

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
user_walk(obj_t obj, void (*func)(obj_t))
{
  obj_t    cl = inst_of(obj), *p;
  unsigned ofs;

  for (ofs = CLASS(CLASS(cl)->parent)->inst_size, p = (obj_t *)((char *) obj + ofs);
       ofs < CLASS(cl)->inst_size;
       ofs += sizeof(obj_t), ++p
       ) {
    (*func)(*p);
  }
}

void
metaclass_init(obj_t inst, obj_t cl, unsigned argc, va_list ap)
{
  assert(argc >= 3);

  obj_t name      = va_arg(ap, obj_t);
  obj_t parent    = va_arg(ap, obj_t);
  obj_t inst_vars = va_arg(ap, obj_t);

  WORK_FRAME_DECL(work, 1);

  work_frame_push(work);

  obj_assign(&CLASS(inst)->name,   name);
  obj_assign(&CLASS(inst)->module, modfp->module);
  obj_assign(&CLASS(inst)->parent, parent);

  unsigned n = list_len(inst_vars);

  CLASS(inst)->inst_size = CLASS(parent)->inst_size + n * sizeof(obj_t);
  if (n == 0) {
    CLASS(inst)->inst_cache = CLASS(parent)->inst_cache;
  } else {
    list_init(CLASS(inst)->_inst_cache);
    CLASS(inst)->inst_cache = CLASS(inst)->_inst_cache;
  }
  
  CLASS(inst)->walk = user_walk;

  strdict_new(&CLASS(inst)->cl_vars, 16);
  strdict_new(&CLASS(inst)->cl_methods, 16);
  strdict_new(&CLASS(inst)->inst_vars, 16);
  strdict_new(&CLASS(inst)->inst_methods, 16);

  unsigned ofs;
  obj_t    p;

  for (ofs = CLASS(parent)->inst_size, p = inst_vars; p != 0; p = CDR(p), ofs += sizeof(obj_t)) {
    int_new(&WORK(work, 0), ofs);
    dict_at_put(CLASS(inst)->inst_vars, CAR(p), WORK(work, 0));
  }

  work_frame_pop();
}

void
metaclass_walk(obj_t inst, void (*func)(obj_t))
{
  (*func)(CLASS(inst)->name);
  (*func)(CLASS(inst)->module);
  (*func)(CLASS(inst)->parent);
  (*func)(CLASS(inst)->cl_vars);
  (*func)(CLASS(inst)->cl_methods);
  (*func)(CLASS(inst)->inst_vars);
  (*func)(CLASS(inst)->inst_methods);
}

void
cm_metaclass_new(void)
{
  WORK_FRAME_DECL(work, 1);

  work_frame_push(work);

  inst_alloc(&WORK(work, 0), consts.metaclass);
  inst_init(WORK(work, 0), 3, MC_ARG(1), MC_ARG(2), MC_ARG(3));

  env_defput(MC_ARG(1), WORK(work, 0));

  obj_assign(MC_RESULT, WORK(work, 0));

  work_frame_pop();
}

void
cm_metaclass_name(void)
{
  obj_assign(MC_RESULT, CLASS(MC_ARG(0))->name);
}

void
cm_metaclass_module(void)
{
  obj_assign(MC_RESULT, CLASS(MC_ARG(0))->module);
}

void
cm_metaclass_parent(void)
{
  obj_assign(MC_RESULT, CLASS(MC_ARG(0))->parent);
}

void
cm_metaclass_cl_vars(void)
{
  obj_assign(MC_RESULT, CLASS(MC_ARG(0))->cl_vars);
}

void
cm_metaclass_cl_methods(void)
{
  obj_assign(MC_RESULT, CLASS(MC_ARG(0))->cl_methods);
}

void
cm_metaclass_inst_methods(void)
{
  obj_assign(MC_RESULT, CLASS(MC_ARG(0))->inst_methods);
}

/***************************************************************************/

obj_t
env_find(obj_t s)
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
env_top(void)
{
  return (blkfp ? blkfp->dict : OBJ(MODULE(modfp->module)->base));
}

void
cm_env_at(void)
{
  obj_t p;

  if ((p = env_find(MC_ARG(1))) == 0) {
    fprintf(stderr, "Variable not bound: %s\n", STR(MC_ARG(1))->data);
    
    error();
  }

  obj_assign(MC_RESULT, CDR(p));
}

void
env_defput(obj_t nm, obj_t val)
{
  dict_at_put(env_top(), nm, val);
}

void
cm_env_defput(void)
{
  env_defput(MC_ARG(1), MC_ARG(2));

  obj_assign(MC_RESULT, MC_ARG(2));
}

void
cm_env_atput(void)
{
  obj_t p;

  if ((p = env_find(MC_ARG(1))) == 0) {
    cm_env_defput();

    return;
  }

  obj_assign(&CDR(p), MC_ARG(2));

  obj_assign(MC_RESULT, MC_ARG(2));
}

/***************************************************************************/

void
cm_system_dump(void)
{
  printf("System dump\n");
}

/***************************************************************************/

void
backtrace(void)
{
  struct method_call_frame *p;
  obj_t                    *a;
  unsigned                 n;

  WORK_FRAME_DECL(work, 1);

  work_frame_push(work);

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

  work_frame_pop();
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
  { &consts.str_atc_putc,    "at:put:" },
  { &consts.str_block,       "#Block" },
  { &consts.str_boolean,     "#Boolean" },
  { &consts.str_code_method, "#Code_Method" },
  { &consts.str_defc_putc,   "def:put:" },
  { &consts.str_dict,        "#Dictionary" },
  { &consts.str_dptr,        "#Dptr" },
  { &consts.str_dump,        "dump" },
  { &consts.str_env,         "#Environment" },
  { &consts.str_equalc,      "equal:" },
  { &consts.str_eval,        "eval" },
  { &consts.str_evalc,       "eval:" },
  { &consts.str_float,       "#Float" },
  { &consts.str_hash,        "hash" },
  { &consts.str_inst_of,     "instance-of" },
  { &consts.str_inst_methods,   "instance-methods" },
  { &consts.str_integer,     "#Integer" },
  { &consts.str_list,        "#List" },
  { &consts.str_ltc,         "lt:" },
  { &consts.str_main,        "#main" },
  { &consts.str_metaclass,   "#Metaclass" },
  { &consts.str_method_call, "#Method_Call" },
  { &consts.str_module,      "#Module" },
  { &consts.str_name,        "name" },
  { &consts.str_new,         "new" },
  { &consts.str_newc,        "new:" },
  { &consts.str_newc_parentc_instance_variablesc, "new:parent:instance-variables:" },
  { &consts.str_object,      "#Object" },
  { &consts.str_pair,        "#Pair" },
  { &consts.str_parent,      "parent" },
  { &consts.str_quote,       "&quote" },
  { &consts.str_set,         "#Set" },
  { &consts.str_setc,        "&set:" },
  { &consts.str_string,      "#String" },
  { &consts.str_system,      "#System" },
  { &consts.str_tostring,    "tostring" },
  { &consts.str_whilec,      "&while:" }
};

struct {
  obj_t    *var;
  obj_t    *name;
  obj_t    *parent;
  unsigned flags;
  unsigned inst_size;
  void     (*init)(obj_t self, obj_t cl, unsigned argc, va_list ap);
  void     (*walk)(obj_t obj, void (*func)(obj_t obj));
  void     (*free)(obj_t obj);
} init_cl_tbl[] = {
  { &consts.cl_object,      &consts.str_object,      0,                                   0,              sizeof(struct obj),      object_init,                0, object_free },
  { &consts.cl_bool,        &consts.str_boolean,     &consts.cl_object,                   0,        sizeof(struct inst_bool),        bool_init },
  { &consts.cl_int,         &consts.str_integer,     &consts.cl_object,                   0,         sizeof(struct inst_int),         int_init },
  { &consts.cl_float,       &consts.str_float,       &consts.cl_object,                   0,       sizeof(struct inst_float),       float_init },
  { &consts.cl_str,         &consts.str_string,      &consts.cl_object,                   0,         sizeof(struct inst_str),         str_init,                0,    str_free },
  { &consts.cl_dptr,        &consts.str_dptr,        &consts.cl_object,  CLASS_FLAG_NO_INST,        sizeof(struct inst_dptr),        dptr_init,        dptr_walk },
  { &consts.cl_pair,        &consts.str_pair,        &consts.cl_dptr,                     0,        sizeof(struct inst_dptr), inst_init_parent },
  { &consts.cl_list,        &consts.str_list,        &consts.cl_dptr,                     0,        sizeof(struct inst_dptr), inst_init_parent },
  { &consts.cl_array,       &consts.str_array,       &consts.cl_object,                   0,       sizeof(struct inst_array),       array_init,       array_walk,  array_free },
  { &consts.cl_set,         &consts.str_set,         &consts.cl_array,                    0,         sizeof(struct inst_set),         set_init },
  { &consts.cl_dict,        &consts.str_dict,        &consts.cl_set,                      0,        sizeof(struct inst_dict),        dict_init },
  { &consts.cl_code_method, &consts.str_code_method, &consts.cl_object,                   0, sizeof(struct inst_code_method), code_method_init },
  { &consts.cl_method_call, &consts.str_method_call, &consts.cl_object,                   0, sizeof(struct inst_method_call), method_call_init, method_call_walk },
  { &consts.cl_block,       &consts.str_block,       &consts.cl_object,                   0,       sizeof(struct inst_block),       block_init,       block_walk },
  { &consts.cl_module,      &consts.str_module,      &consts.cl_dict,                     0,      sizeof(struct inst_module),      module_init,      module_walk },
  { &consts.cl_env,         &consts.str_env,         &consts.cl_object,  CLASS_FLAG_NO_INST },
  { &consts.cl_system,      &consts.str_system,      &consts.cl_object,  CLASS_FLAG_NO_INST }
};

struct {
  obj_t    *var;
  unsigned dofs;
  obj_t    *sel;
  void     (*func)(void);
} init_method_tbl[] = {
  { &consts.metaclass, offsetof(struct class, cl_methods), &consts.str_newc_parentc_instance_variablesc,  cm_metaclass_new },

  { &consts.metaclass, offsetof(struct class, inst_methods), &consts.str_new,      cm_obj_new },
  { &consts.metaclass, offsetof(struct class, inst_methods), &consts.str_name,     cm_metaclass_name },
  { &consts.metaclass, offsetof(struct class, inst_methods), &consts.str_parent,   cm_metaclass_parent },
  { &consts.metaclass, offsetof(struct class, inst_methods), &consts.str_inst_methods, cm_metaclass_inst_methods },

  { &consts.cl_object, offsetof(struct class, inst_methods), &consts.str_inst_of,  cm_obj_inst_of },
  { &consts.cl_object, offsetof(struct class, inst_methods), &consts.str_quote,    cm_obj_quote },
  { &consts.cl_object, offsetof(struct class, inst_methods), &consts.str_eval,     cm_obj_eval },
  { &consts.cl_object, offsetof(struct class, inst_methods), &consts.str_tostring, cm_obj_tostring },
  { &consts.cl_object, offsetof(struct class, inst_methods), &consts.str_whilec,   cm_obj_while },
  { &consts.cl_object, offsetof(struct class, inst_methods), &consts.str_atc,      cm_obj_at },
  { &consts.cl_object, offsetof(struct class, inst_methods), &consts.str_atc_putc, cm_obj_atput },

  { &consts.cl_bool, offsetof(struct class, cl_methods), &consts.str_newc, cm_bool_newc },

  { &consts.cl_bool, offsetof(struct class, inst_methods), &consts.str_tostring, cm_bool_tostring },

  { &consts.cl_int, offsetof(struct class, cl_methods), &consts.str_newc,     cm_int_new },

  { &consts.cl_int, offsetof(struct class, inst_methods), &consts.str_addc,     cm_int_add },
  { &consts.cl_int, offsetof(struct class, inst_methods), &consts.str_ltc,      cm_int_lt },
  { &consts.cl_int, offsetof(struct class, inst_methods), &consts.str_tostring, cm_int_tostring },

  { &consts.cl_float, offsetof(struct class, cl_methods), &consts.str_newc,     cm_float_new },

  { &consts.cl_float, offsetof(struct class, inst_methods), &consts.str_tostring,     cm_float_tostring },

  { &consts.cl_str, offsetof(struct class, inst_methods), &consts.str_eval,     cm_str_eval },
  { &consts.cl_str, offsetof(struct class, inst_methods), &consts.str_tostring, cm_str_tostring },

  { &consts.cl_pair, offsetof(struct class, inst_methods), &consts.str_eval,     cm_pair_eval },
  { &consts.cl_pair, offsetof(struct class, inst_methods), &consts.str_tostring, cm_pair_tostring },

  { &consts.cl_list, offsetof(struct class, inst_methods), &consts.str_eval,     cm_list_eval },
  { &consts.cl_list, offsetof(struct class, inst_methods), &consts.str_tostring, cm_list_tostring },

  { &consts.cl_dict, offsetof(struct class, inst_methods), &consts.str_atc,      cm_dict_at },
  { &consts.cl_dict, offsetof(struct class, inst_methods), &consts.str_atc_putc, cm_dict_atput },

  { &consts.cl_method_call, offsetof(struct class, inst_methods), &consts.str_tostring, cm_mc_tostring },
  { &consts.cl_method_call, offsetof(struct class, inst_methods), &consts.str_eval,     cm_mc_eval },

  { &consts.cl_block, offsetof(struct class, inst_methods), &consts.str_evalc, cm_blk_eval },

  { &consts.cl_module, offsetof(struct class, inst_methods), &consts.str_name, cm_module_name },

  { &consts.cl_env, offsetof(struct class, cl_methods), &consts.str_atc,       cm_env_at },  
  { &consts.cl_env, offsetof(struct class, cl_methods), &consts.str_defc_putc, cm_env_defput },  
  { &consts.cl_env, offsetof(struct class, cl_methods), &consts.str_atc_putc,  cm_env_atput },  

  { &consts.cl_system, offsetof(struct class, cl_methods), &consts.str_dump, cm_system_dump },  
};


void
init_dict(obj_t d, unsigned size)
{
  DICT(d)->base->base->size = size;
  DICT(d)->base->base->data = ool_mem_allocz(size * sizeof(obj_t));
  DICT(d)->base->find       = strdict_find;
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

  work_frame_push(work);

  /* Create main module */

  obj_assign(&consts.module_main, (obj_t) ool_mem_allocz(sizeof(struct inst_module)));
  init_dict(consts.module_main, 64);

  /* Create metaclass */

  obj_assign(&consts.metaclass, (obj_t) ool_mem_allocz(sizeof(struct class)));
  init_cl(consts.metaclass, 32);
  obj_assign(&CLASS(consts.metaclass)->module, consts.module_main);
  CLASS(consts.metaclass)->inst_size = sizeof(struct class);
  list_init(CLASS(consts.metaclass)->_inst_cache);
  CLASS(consts.metaclass)->inst_cache = CLASS(consts.metaclass)->_inst_cache;
  CLASS(consts.metaclass)->init = metaclass_init;
  CLASS(consts.metaclass)->walk = metaclass_walk;

  /* Create classes, pass 1 - Allocate classes, some init */

  for (i = 0; i < ARRAY_SIZE(init_cl_tbl); ++i) {
    obj_t cl;

    obj_assign(init_cl_tbl[i].var, cl = (obj_t) ool_mem_allocz(sizeof(struct class)));
    init_cl(cl, 32);
    obj_assign(&cl->inst_of, consts.metaclass);
    obj_assign(&CLASS(cl)->module, consts.module_main);
    obj_assign(&CLASS(cl)->parent, init_cl_tbl[i].parent ? *init_cl_tbl[i].parent : 0);
    CLASS(cl)->flags     = init_cl_tbl[i].flags;
    CLASS(cl)->inst_size = init_cl_tbl[i].inst_size;
    list_init(CLASS(cl)->_inst_cache);
    CLASS(cl)->inst_cache = CLASS(base_class_same_inst_size(cl))->_inst_cache;
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

  work_frame_pop();
}

int
main(void)
{
  struct module_frame modfr[1];

  WORK_FRAME_DECL(work, 10);

  init();

  module_frame_push(modfr, consts.module_main);

  work_frame_push(work);

#if 1
  {
    struct stream_file str[1];
    struct parse_ctxt  pc[1];

    stream_file_init(str, stdin);

    parse_ctxt_init(pc, str->base);

    for (;;) {
      unsigned ret;

      
      ret = parse(&WORK(work, 0), pc);
      if (ret == PARSE_EOF)  break;
      if (ret == PARSE_ERR) {
	printf("Syntax error\n"); 

	continue;
      }

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

  work_frame_pop();

  module_frame_pop();
    
  return (0);
}
