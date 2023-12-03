#include <values.h>
#include "glue.h"
#include <stdio.h>
#include <ncurses.h>

/* THE FOLLOWING SHOULD EVENTUALLY BE MOVED INTO gc_stack.h */
/* BEGINFRAME / LIVEPOINTERSn / ENDFRAME
  Usage:

value myfunc(struct thread_info *tinfo, ...other args...) {
  ... some variable declarations ...
  BEGINFRAME(tinfo,n)
  ... some more variable declarations ...

  ...
  r=LIVEPOINTERSj(tinfo,funcallx,a0,a1,...,aj-1);    [where j<n]
  ...
  LIVEPOINTERSk(tinfo,(funcally,NULL),a0,a1,...,ak-1);    [where k<n]
  
  
  ENDFRAME
}

  The "tinfo" argument to BEGINFRAME is the tinfo pointer of the
  enclosing function.  The number n is the maximum frame size, that is,
  the max number of pointervalues to save across any call within the
  BEGINFRAME/ENDFRAME block.  There may be zero or more calls to
  LIVEPOINTERS[0,1,2,3,etc] within the block.  In each such call,
  the "funcall" is some expression that calls a function, returning
  a result of type "value", and the arguments ai are pointer values
  to save across the call.  The result of calling the function will
  be returned as the result of LIVEPOINTERS; in the pattern shown,
  it would be put into "r".
     To call a void-returning function f(x), then use  (f(x),(value)NULL)
  as the funcall argument, and in that case you may leave out
  the r=  in the pattern shown.
     It's important that the implementation of ENDFRAME has no
  executable code, because it may be bypassed by a function return.
*/
  
#define BEGINFRAME(tinfo,n) {{{{{ value __ROOT__[n];   \
   struct stack_frame __FRAME__ = { NULL/*bogus*/, __ROOT__, tinfo->fp }; \
   value __RTEMP__;

#define ENDFRAME }}}}}

#define LIVEPOINTERS0(tinfo, exp) (exp)

#define LIVEPOINTERS1(tinfo, exp, a0) \
  (tinfo->fp= &__FRAME__, __FRAME__.next=__ROOT__+1, \
  __ROOT__[0]=(a0), __RTEMP__=(exp), (a0)=__ROOT__[0], \
  tinfo->fp=__FRAME__.prev, __RTEMP__)

#define LIVEPOINTERS2(tinfo, exp, a0, a1)	\
  (tinfo->fp= &__FRAME__, __FRAME__.next=__ROOT__+2, \
  __ROOT__[0]=(a0), __ROOT__[1]=(a1),		\
  __RTEMP__=(exp),                              \
  (a0)=__ROOT__[0], (a1)=__ROOT__[1],             \
  tinfo->fp=__FRAME__.prev, __RTEMP__)

#define LIVEPOINTERS3(tinfo, exp, a0, a1, a2)   \
  (tinfo->fp= &__FRAME__, __FRAME__.next=__ROOT__+3,                       \
  __ROOT__[0]=(a0), __ROOT__[1]=(a1), __ROOT__[2]=(a2),  \
  __RTEMP__=(exp),                                       \
  (a0)=__ROOT__[0], (a1)=__ROOT__[1], (a2)=__ROOT__[2],    \
  tinfo->fp=__FRAME__.prev, __RTEMP__)

#define LIVEPOINTERS4(tinfo, exp, a0, a1, a2, a3)	\
  (tinfo->fp= &__FRAME__,  __FRAME__.next=__ROOT__+4,  \
  __ROOT__[0]=(a0), __ROOT__[1]=(a1), __ROOT__[2]=(a2), __ROOT__[3]=(a3),  \
  __RTEMP__=(exp),                                       \
  (a0)=__ROOT__[0], (a1)=__ROOT__[1], (a2)=__ROOT__[2], (a3)=__ROOT__[3],    \
  tinfo->fp=__FRAME__.prev, __RTEMP__)
/* END OF STUFF TO BE MOVED INTO gc_stack.h */

typedef enum { XI, XO, XH } tag_positive;
// not very space efficient but it should be easy to prove
value int_of_positive(value p) {
  switch (get_Coq_Numbers_BinNums_positive_tag(p)) {
    case XI:
      return ((2 * (int_of_positive(get_args(p)[0]) >> 1) + 1) << 1) + 1;
    case XO:
      return ((2 * (int_of_positive(get_args(p)[0]) >> 1)) << 1) + 1;
    case XH:
      return (1 << 1) + 1;
  }
}

typedef enum { N0, NPOS } tag_N;
value int_of_n(value z) {
  switch (get_Coq_Numbers_BinNums_N_tag(z)) {
    case N0:
      return 0;
    case NPOS:
      return int_of_positive(get_args(z)[0]);
  }
}

value n_of_int(struct thread_info *tinfo, value t) {
  if (t == 1) {
    return make_Coq_Numbers_BinNums_N_N0();
  }
  value temp = 0;
  // loop over bits from left (most significant) to right (least significant)
  // ignore the last bit, hence i > 0, not i >= 0
  for (unsigned int i = sizeof(value) * 8 - 1; i > 0; i--) {
    _Bool bit = (t & (1 << i)) >> i;
    if (bit) {
      if (temp) {
        temp = alloc_make_Coq_Numbers_BinNums_positive_xI(tinfo, temp);
      } else {
        temp = make_Coq_Numbers_BinNums_positive_xH();
      }
    } else if (temp) {
      temp = alloc_make_Coq_Numbers_BinNums_positive_xO(tinfo, temp);
    }
    // ignore the 0 bits before the first significant 1
  }
  return alloc_make_Coq_Numbers_BinNums_N_Npos(tinfo, temp);
}

unsigned char ascii_to_char(value x) {
  unsigned char c = 0;
  for(unsigned int i = 0; i < 8; i++) {
    unsigned int tag = 
      get_Coq_Init_Datatypes_bool_tag(*((value *) *((value *) x) + i));
    c += !tag << i;
  }
  return c;
}

typedef enum { EMPTYSTRING, STRING } coq_string;

size_t string_value_length(value s) {
  value temp = s;
  size_t i = 0;
  while(get_Coq_Strings_String_string_tag(temp) == STRING) {
    temp = *((value *) temp + 1ULL);
    i++;
  }
  return i;
}

char *value_to_string(value s) {
  value temp = s;
  char * result;
  size_t result_length = string_value_length(s) + 1;
  result = (char*) malloc(result_length * sizeof(char));
  memset(result, 0, result_length);

  for(int i = 0; get_Coq_Strings_String_string_tag(temp) == STRING; i++) {
    sprintf(result + i, "%c", ascii_to_char(temp));
    temp = *((value *) temp + 1ULL);
  }

  return result;
}

typedef enum { PURE, BIND, NEWWINDOW, CLOSEWINDOW, 
               MOVECURSOR, GETCURSOR, GETSIZE, PRINT, REFRESH, CLEAR, GETCHAR } M;

value runM(struct thread_info *tinfo, value action) {
  BEGINFRAME(tinfo, 2)
  switch (get_prog_C_MI_tag(action)) {
    case PURE:
      return get_args(action)[1];
    case BIND: 
      {
        value arg0 = get_args(action)[2];
        value arg1 = get_args(action)[3];
        value temp = LIVEPOINTERS2(tinfo, runM(tinfo, arg0), arg0, arg1);
        temp = LIVEPOINTERS2(tinfo, call(tinfo, arg1, temp), arg1, temp);
        return runM(tinfo, temp);
      }
    case NEWWINDOW:
      {
        value w = (value) initscr();
        noecho();
        /* curs_set(0); */
        return w;
      }
    case CLOSEWINDOW:
      {
        value w = get_args(action)[0];
        delwin(w);
        endwin();
        _nc_freeall();
        return make_Coq_Init_Datatypes_unit_tt();
      }
    case MOVECURSOR:
      {
        value w = get_args(action)[0];
        value arg0 = get_args(action)[1];
        value arg1 = get_args(action)[2];
        wmove(w, Unsigned_long_val(arg0), Unsigned_long_val(arg1));
        return make_Coq_Init_Datatypes_unit_tt();
      }
    case GETCURSOR:
      {
        value w = get_args(action)[0];
        value y = Val_long(getcury(w));
        value x = Val_long(getcurx(w));
        return alloc_make_Coq_Init_Datatypes_prod_pair(tinfo, y, x);
      }
    case GETSIZE:
      {
        value w = get_args(action)[0];
        value y = Val_long(getmaxy(w));
        value x = Val_long(getmaxx(w));
        return alloc_make_Coq_Init_Datatypes_prod_pair(tinfo, y, x);
      }
    case PRINT:
      {
        value w = get_args(action)[0];
        char *s = value_to_string(get_args(action)[1]);
        waddstr(w, s);
        free(s);
        return make_Coq_Init_Datatypes_unit_tt();
      }
    case REFRESH:
      {
        value w = get_args(action)[0];
        wrefresh(w);
        return make_Coq_Init_Datatypes_unit_tt();
      }
    case CLEAR:
      {
        value w = get_args(action)[0];
        wclear(w);
        return make_Coq_Init_Datatypes_unit_tt();
      }
    case GETCHAR:
      {
        value w = get_args(action)[0];
        return Val_long(wgetch(w));
      }
    default:
      return 0;
  }
  ENDFRAME
}
