#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <stdio.h>
#include <assert.h>


#define ARRAY_SIZE(a)  (sizeof(a) / sizeof((a)[0]))

#define CONTAINER_OF(p, s, f)  ((s *)((char *)(p) - offsetof(s, f)))

enum { false = 0, true = 1 };


struct list {
  struct list *prev, *next;
};

static inline void
list_init(struct list *li)
{
  li->prev = li->next = li;
}

static inline struct list *
list_first(struct list *li)
{
  return (li->next);
}

static inline struct list *
list_last(struct list *li)
{
  return (li->prev);
}

static inline struct list *
list_end(struct list *li)
{
  return (li);
}

static inline unsigned
list_empty(struct list *li)
{
  return (li->next == li);
}

static inline struct list *
list_prev(struct list *nd)
{
  return (nd->prev);
}

static inline struct list *
list_next(struct list *nd)
{
  return (nd->next);
}

void *ool_mem_alloc(unsigned size);
void *ool_mem_allocz(unsigned size);
void ool_mem_free(void *p, unsigned size);


struct obj;
typedef struct obj *obj_t;

struct obj {
  struct list list_node[1];
  unsigned    ref_cnt;
  obj_t       inst_of;
};
#define OBJ(x)  ((struct obj *)(x))
#define NIL     OBJ(0)

typedef unsigned char boolval_t;
struct inst_bool {
  struct obj base[1];
  boolval_t  val;
};
#define BOOL(x) ((struct inst_bool *)(x))

typedef long long intval_t;
struct inst_int {
  struct obj base[1];
  intval_t   val;
};
#define INT(x)  ((struct inst_int *)(x))

typedef long double floatval_t;
struct inst_float {
  struct obj base[1];
  floatval_t val;
};
#define FLOAT(x)  ((struct inst_float *)(x))

struct inst_str {
  struct obj base[1];
  unsigned   size;
  char       *data;
};
#define STR(x)  ((struct inst_str *)(x))

struct inst_dptr {
  struct obj base[1];
  obj_t      car, cdr;
};
#define CAR(x)  (((struct inst_dptr *)(x))->car)
#define CDR(x)  (((struct inst_dptr *)(x))->cdr)

struct inst_array {
  struct obj base[1];
  unsigned   size;
  obj_t      *data;
};
#define ARRAY(x)  ((struct inst_array *)(x))

struct inst_set {
  struct inst_array base[1];
  obj_t             *(*find)(obj_t dict, obj_t key, obj_t **bucket);
  unsigned          cnt;
};
#define SET(x)  ((struct inst_set *)(x))

struct inst_dict {
  struct inst_set base[1];
};
#define DICT(x)  ((struct inst_dict *)(x))

struct inst_code_method {
  struct obj base[1];
  void       (*func)(void);
};
#define CODE_METHOD(x)  ((struct inst_code_method *)(x))

struct inst_block {
  struct obj base[1];
  unsigned   argc;
  obj_t      args, body;
};
#define BLOCK(x)  ((struct inst_block *)(x))

struct inst_method_call {
  struct obj base[1];
  obj_t      sel, args;
};

#define METHOD_CALL(x)  ((struct inst_method_call *)(x))

struct inst_module {
  struct inst_dict base[1];
  obj_t            name;
  obj_t            parent;
};
#define MODULE(x)  ((struct inst_module *)(x))

struct inst_user {
  struct obj base[1];
  obj_t      instvar[1];
};

struct class {
  struct obj  base[1];
  obj_t       name;
  obj_t       module;
  obj_t       parent;
  enum {
    CLASS_FLAG_NO_INST = 1 << 0
  }           flags;
  unsigned    inst_size;
  struct list _inst_cache[1], *inst_cache;
  void        (*init)(obj_t self, obj_t cl, unsigned argc, va_list ap);
  void        (*walk)(obj_t obj, void (*func)(obj_t obj));
  void        (*free)(obj_t obj);
  obj_t       cl_vars, cl_methods;
  obj_t       inst_vars, inst_methods;
};
#define CLASS(x)  ((struct class *)(x))

void  obj_release(obj_t obj);
void  obj_assign(obj_t *dst, obj_t obj);
void  str_newc(obj_t *result, unsigned argc, ...);
void  error(void);
void  inst_method_call(obj_t *result, obj_t sel, unsigned argc, obj_t *argv);
obj_t dict_at(obj_t dict, obj_t key);
void  dict_at_put(obj_t dict, obj_t key, obj_t val);
void  bool_new(obj_t *dst, unsigned val);
void  int_new(obj_t *dst, intval_t val);
void  pair_new(obj_t *dst, obj_t first, obj_t second);
void  list_new(obj_t *dst, obj_t car, obj_t cdr);
void  array_new(obj_t *dst, unsigned size);
void  method_call_new(obj_t *dst, obj_t sel, obj_t args);
void  block_new(obj_t *dst, obj_t args, obj_t body);
void  module_new(obj_t *dst, obj_t name, obj_t parent);
void  env_defput(obj_t nm, obj_t val);

struct {
  obj_t str_addc;
  obj_t str_array;
  obj_t str_atc;
  obj_t str_atc_putc;
  obj_t str_block;
  obj_t str_boolean;
  obj_t str_cl_methods;
  obj_t str_cl_vars;
  obj_t str_code_method;
  obj_t str_defc_putc;
  obj_t str_dict;
  obj_t str_dptr;
  obj_t str_dump;
  obj_t str_env;
  obj_t str_equalc;
  obj_t str_eval;
  obj_t str_evalc;
  obj_t str_float;
  obj_t str_hash;
  obj_t str_inst_methods;
  obj_t str_inst_of;
  obj_t str_integer;
  obj_t str_list;
  obj_t str_ltc;
  obj_t str_main;
  obj_t str_metaclass;
  obj_t str_method_call;
  obj_t str_module;
  obj_t str_name;
  obj_t str_new;
  obj_t str_newc;
  obj_t str_newc_parentc_instance_variablesc;
  obj_t str_object;
  obj_t str_pair;
  obj_t str_parent;
  obj_t str_quote;
  obj_t str_set;
  obj_t str_setc;
  obj_t str_string;
  obj_t str_system;
  obj_t str_tostring;
  obj_t str_whilec;

  obj_t metaclass;
  obj_t cl_object;
  obj_t cl_bool;
  obj_t cl_int;
  obj_t cl_float;
  obj_t cl_str;
  obj_t cl_dptr;
  obj_t cl_pair;
  obj_t cl_list;
  obj_t cl_array;
  obj_t cl_set;
  obj_t cl_dict;
  obj_t cl_code_method;
  obj_t cl_block;
  obj_t cl_method_call;
  obj_t cl_module;
  obj_t cl_env;
  obj_t cl_system;

  obj_t module_main;
} consts;

/***************************************************************************/

static inline obj_t
inst_of(obj_t obj)
{
  return (obj == 0 ? consts.cl_object : obj->inst_of);
}

/***************************************************************************/

struct stream;

struct stream_funcs {
  int  (*getc)(struct stream *);
  void (*ungetc)(struct stream *, char);
};

struct stream {
  struct stream_funcs *funcs;
  unsigned            line;
};

struct stream_buf {
  struct stream base[1];

  char     *buf;
  unsigned len, ofs;
};

struct stream_file {
  struct stream base[1];
  
  char *filename;
  FILE *fp;
};

void stream_file_init(struct stream_file *str, char *filename, FILE *fp);

struct tokbuf {
  unsigned bufsize;
  unsigned len;
  char     *buf;
  char     data[32];
};

struct parse_ctxt {
  struct stream *str;
  struct tokbuf tb[1];
};

void parse_ctxt_init(struct parse_ctxt *pc, struct stream *str);
void parse_ctxt_fini(struct parse_ctxt *pc);

enum {
  PARSE_EOF, PARSE_OK, PARSE_ERR
};

unsigned parse(obj_t *dst, struct parse_ctxt *pc);


struct frame {
  struct frame *prev;
  enum {
    FRAME_TYPE_WORK = 1,
    FRAME_TYPE_METHOD_CALL,
    FRAME_TYPE_MODULE,
    FRAME_TYPE_BLOCK,
    FRAME_TYPE_RESTART,
    FRAME_TYPE_INPUT
  } type;
};

struct frame *fp;

static inline void
frame_push(struct frame *fr, unsigned type)
{
  fr->type = type;
  fr->prev = fp;				\
  fp = fr;
}

static inline void
frame_pop(void)
{
  fp = fp->prev;
}

struct work_frame {
  struct frame      base[1];
  struct work_frame *prev;
  unsigned          size;
  obj_t             *data;
};

struct work_frame *wfp;

#define WORK_FRAME_DATA(nm)  __ ## nm ## _data

#define WORK_FRAME_DECL(nm , n)						\
  obj_t WORK_FRAME_DATA(nm)[n];						\
  struct work_frame nm[1] = { { .size = (n), .data = WORK_FRAME_DATA(nm) } }

static inline void
work_frame_push(struct work_frame *fr)
{
  memset(fr->data, 0, fr->size * sizeof(fr->data[0]));
  fr->prev = wfp;
  wfp = fr;
  frame_push(fr->base, FRAME_TYPE_WORK);
}

static inline void
work_frame_pop(void)
{
  frame_pop();
  
  for (obj_t *p = wfp->data, unsigned n = wfp->size; n > 0; --n, ++p) {
    obj_release(*p);
  }
  wfp = wfp->prev;
}

#define WORK_FRAME_BEGIN(_n)			\
  {						\
    WORK_FRAME_DECL(__work, (_n));		\
    work_frame_push(__work);

#define WORK_FRAME_END				\
    work_frame_pop();				\
  }

#define WORK(i)  (WORK_FRAME_DATA(__work)[i])

struct method_call_frame {
  struct frame             base[1];
  struct method_call_frame *prev;
  obj_t                    *result;
  obj_t                    cl;
  obj_t                    sel;
  unsigned                 argc;
  obj_t                    *argv;
};

struct method_call_frame *mcfp;

static inline void
method_call_frame_push(struct method_call_frame *fr, obj_t *rslt, obj_t cl, obj_t sel, unsigned argc, obj_t *argv)
{
  fr->result = rslt;					    
  fr->cl     = cl;					    
  fr->sel    = sel;					    
  fr->argc   = argc;					    
  fr->argv   = argv;					    
  fr->prev   = mcfp;					    
  mcfp = fr;						    
  frame_push(fr->base, FRAME_TYPE_METHOD_CALL);		
}

static inline void
method_call_frame_pop(void)
{
  frame_pop();
  mcfp = mcfp->prev;
}

#define METHOD_CALL_FRAME_BEGIN(_rslt, _cl, _sel, _argc, _argv)		\
  {									\
    struct method_call_frame __mcfr[1];					\
    method_call_frame_push(__mcfr, (_rslt), (_cl), (_sel), (_argc), (_argv));

#define METHOD_CALL_FRAME_END			\
    method_call_frame_pop();			\
  }

#define MC_RESULT  (mcfp->result)
#define MC_ARGC    (mcfp->argc)
#define MC_ARG(x)  (mcfp->argv[x])

struct module_frame {
  struct frame        base[1];
  struct module_frame *prev;
  obj_t               module;
};

struct module_frame *modfp;

static inline void
module_frame_push(struct module_frame *fr, obj_t module)
{
  fr->module = module;
  fr->prev   = modfp;
  modfp = fr;		
  frame_push(fr->base, FRAME_TYPE_MODULE);
}

static inline void
module_frame_pop(void)
{
  frame_pop();
  modfp = modfp->prev;
}

#define MODULE_FRAME_BEGIN(_mod)		\
  {						\
    struct module_frame __modfr[1];		\
    module_frame_push(__modfr, (_mod));

#define MODULE_FRAME_END			\
    module_frame_pop();				\
  }

#define MODULE_CUR  (modfp->module)

struct jmp_frame {
  struct frame base[1];
  jmp_buf      jmpbuf;
  int          code;
};

#define JMP_FRAME_SETJMP(_fr) \
  ((_fr)->code = setjmp((_fr)->jmp_buf))

void jmp_frame_jmp(struct jmp_frame *fr, int code);

struct restart_frame {
  struct jmp_frame     base[1];
  struct restart_frame *prev;
};

struct restart_frame *rstfp;

static inline void
restart_frame_push(struct restart_frame *fr)
{
  fr->prev = rstfp;
  rstfp = fr;
  frame_push(fr->base->base, FRAME_TYPE_RESTART);
}

static inline void
restart_frame_pop(void)
{
  frame_pop();
  rstfp = rstfp->prev;
}

#define RESTART_FRAME_BEGIN			\
  {						\
    struct restart_frame __rstfr[1];		\
    restart_frame_push(__rstfr);		\
    JMP_FRAME_SETJMP(_rstfr->base);

#define RESTART_FRAME_END					\
    restart_frame_pop();					\
  }

#define RESTART_FRAME_JMP(_code)  (jmp_frame_jmp(rstfp->base, (_code)))
#define RESTART_FRAME_CODE        (rstfp->base->code)

struct block_frame {
  struct jmp_frame   base[1];
  struct block_frame *prev;
  obj_t              dict;
};

struct block_frame *blkfp;

static inline void
block_frame_push(struct block_frame *fr, obj_t dict)
{
  fr->dict = dict;
  fr->prev = blkfp;
  blkfp = fr;
  frame_push(fr->base->base, FRAME_TYPE_BLOCK);
}

static inline void
block_frame_pop(void)
{
  frame_pop();
  blkfp = blkfp->prev;				\
}

#define BLOCK_FRAME_BEGIN(_dict)		\
  {						\
    struct block_frame __blkfr[1];		\
    block_frame_push(__blkfr, (_dict));		\
    JMP_FRAME_SETJMP(__blkfr->base);

#define BLOCK_FRAME_END				\
    block_frame_pop();				\
  }

#define BLOCK_FRAME_JMP(_code)  (jmp_frame_jmp(blkfp->base, (_code)))
#define BLOCK_FRAME_CODE        (blkfp->base->code)

struct input_frame {
  struct jmp_frame   base[1];
  struct input_frame *prev;
  struct parse_ctxt  *pc;
};

struct input_frame *inpfp;

static inline void
input_frame_push(struct input_frame *fr, struct parse_ctxt *pc)
{
  fr->pc   = pc;
  fr->prev = inpfp;
  inpfp = fr;
  frame_push(fr->base->base, FRAME_TYPE_INPUT);
}

static inline void
input_frame_pop(void)
{
  frame_pop();
  inpfp = inpfp->prev;
}

#define INPUT_FRAME_BEGIN(_pc)			\
  {						\
    struct input_frame __inpfr[1];		\
    input_frame_push(_pc);

#define INPUT_FRAME_END \
    input_frame_pop();	\
  }

void method_argc_err(void);
void method_bad_arg_err(obj_t arg);


