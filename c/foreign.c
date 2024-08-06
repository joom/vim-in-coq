#include <stdio.h>
#include <stdlib.h>
#include <curses.h>
#include <string.h>
#include <sys/stat.h>
#include <values.h>
#include "glue.h"

/* THE FOLLOWING SHOULD EVENTUALLY BE MOVED INTO gc_stack.h */
/* BEGINFRAME / GCSAVEn / ENDFRAME
  Usage:

value myfunc(struct thread_info *tinfo, ...other args...) {
  ... some variable declarations ...
  BEGINFRAME(tinfo,n)
  ... some more variable declarations ...

  ...
  r=GCSAVEj(tinfo,funcallx,a0,a1,...,aj-1);    [where j<n]
  ...
  GCSAVEk(tinfo,(funcally,NULL),a0,a1,...,ak-1);    [where k<n]


  ENDFRAME
}

  The "tinfo" argument to BEGINFRAME is the tinfo pointer of the
  enclosing function.  The number n is the maximum frame size, that is,
  the max number of pointervalues to save across any call within the
  BEGINFRAME/ENDFRAME block.  There may be zero or more calls to
  GCSAVE[0,1,2,3,etc] within the block.  In each such call,
  the "funcall" is some expression that calls a function, returning
  a result of type "value", and the arguments ai are pointer values
  to save across the call.  The result of calling the function will
  be returned as the result of GCSAVE; in the pattern shown,
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

#define GCSAVE0(tinfo, exp) (exp)

#define GCSAVE1(tinfo, exp, a0) \
  (tinfo->fp= &__FRAME__, __FRAME__.next=__ROOT__+1, \
  __ROOT__[0]=(a0), __RTEMP__=(exp), (a0)=__ROOT__[0], \
  tinfo->fp=__FRAME__.prev, __RTEMP__)

#define GCSAVE2(tinfo, exp, a0, a1)	\
  (tinfo->fp= &__FRAME__, __FRAME__.next=__ROOT__+2, \
  __ROOT__[0]=(a0), __ROOT__[1]=(a1),		\
  __RTEMP__=(exp),                              \
  (a0)=__ROOT__[0], (a1)=__ROOT__[1],             \
  tinfo->fp=__FRAME__.prev, __RTEMP__)

#define GCSAVE3(tinfo, exp, a0, a1, a2)   \
  (tinfo->fp= &__FRAME__, __FRAME__.next=__ROOT__+3,                       \
  __ROOT__[0]=(a0), __ROOT__[1]=(a1), __ROOT__[2]=(a2),  \
  __RTEMP__=(exp),                                       \
  (a0)=__ROOT__[0], (a1)=__ROOT__[1], (a2)=__ROOT__[2],    \
  tinfo->fp=__FRAME__.prev, __RTEMP__)

#define GCSAVE4(tinfo, exp, a0, a1, a2, a3)	\
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

unsigned char c_char_of_coq_ascii(value x) {
  unsigned char c = 0;
  for (unsigned int i = 0; i < 8; i++) {
    unsigned int tag =
      get_Coq_Init_Datatypes_bool_tag(get_args(get_args(x)[0])[i]);
    c += !tag << i;
  }
  return c;
}

typedef enum { NIL, CONS } coq_list;

size_t coq_list_length(value s) {
  value temp = s;
  size_t i = 0;
  while (get_Coq_Init_Datatypes_list_tag(temp) == CONS) {
    temp = get_args(temp)[1];
    i++;
  }
  return i;
}

char *c_string_of_coq_ascii_list(value s) {
  value temp = s;
  char * result;
  size_t result_length = coq_list_length(s) + 1;
  result = (char*) malloc(result_length * sizeof(char));
  memset(result, 0, result_length);

  for (int i = 0; get_Coq_Init_Datatypes_list_tag(temp) == CONS; i++) {
    sprintf(result + i, "%c", c_char_of_coq_ascii(temp));
    temp = get_args(temp)[1];
  }

  return result;
}

value coq_bool_of_c_bool(_Bool b) {
  if (b)
    return make_Coq_Init_Datatypes_bool_true();
  else
    return make_Coq_Init_Datatypes_bool_false();
}

value coq_ascii_of_c_char(struct thread_info *tinfo, unsigned char c) {
  value v[8];
  for (unsigned int i = 0; i < 8; i++) {
    v[i] = coq_bool_of_c_bool(c & (1 << i));
  }
  return alloc_make_Coq_Strings_Ascii_ascii_Ascii(tinfo, v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7]);
}

value coq_ascii_list_of_c_string(struct thread_info *tinfo, unsigned char *s) {
  value temp = make_Coq_Init_Datatypes_list_nil();
  for (unsigned int i = strlen(s); 0 < i; i--) {
    value c = coq_ascii_of_c_char(tinfo, s[i-1]);
    temp = alloc_make_Coq_Init_Datatypes_list_cons(tinfo, c, temp);
  }
  return temp;
}

value read_file_into_coq_ascii_list(struct thread_info *tinfo, value file_name) {
  value err = NULL;
  char *c_file_name = c_string_of_coq_ascii_list(file_name);
  struct stat st;
  FILE *fp = fopen(c_file_name, "r");
  free(c_file_name);
  if (fp == NULL) {
    return alloc_make_Coq_Init_Datatypes_sum_inl(tinfo,
        alloc_make_Vim_Errors_error_CouldntReadFile(tinfo, file_name));
  }
  int fn;
  if ((fn = fileno(fp)) == -1) {
    fclose(fp);
    return alloc_make_Coq_Init_Datatypes_sum_inl(tinfo,
        alloc_make_Vim_Errors_error_CouldntReadFile(tinfo, file_name));
  }
  if (fstat(fn, &st)) {
    fclose(fp);
    return alloc_make_Coq_Init_Datatypes_sum_inl(tinfo,
        alloc_make_Vim_Errors_error_CouldntReadFile(tinfo, file_name));
  }
  if (fseek(fp, -1, SEEK_END)) { // start from the end
    return alloc_make_Coq_Init_Datatypes_sum_inl(tinfo,
        alloc_make_Vim_Errors_error_CouldntReadFile(tinfo, file_name));
  }
  value temp = make_Coq_Init_Datatypes_list_nil();
  // could do better error handling for the loop
  for (int p = st.st_size; p > 0; p--) {
    char c = fgetc(fp);
    fseek(fp, -2, SEEK_CUR); // read backwards
    temp = alloc_make_Coq_Init_Datatypes_list_cons(tinfo, coq_ascii_of_c_char(tinfo, c), temp);
  }
  fclose(fp);
  return alloc_make_Coq_Init_Datatypes_sum_inr(tinfo, temp);
}

value write_file_from_coq_ascii_list(struct thread_info *tinfo, value file_name, value content) {
  char *c_file_name = c_string_of_coq_ascii_list(file_name);
  FILE *fp = fopen(c_file_name, "w");
  free(c_file_name);
  if (fp == NULL) {
    return alloc_make_Coq_Init_Datatypes_option_Some(tinfo,
        alloc_make_Vim_Errors_error_CouldntWriteToFile(tinfo, file_name));
  }
  char *s = c_string_of_coq_ascii_list(content);
  if (fputs(s, fp) == EOF) {
    fclose(fp);
    free(s);
    return alloc_make_Coq_Init_Datatypes_option_Some(tinfo,
        alloc_make_Vim_Errors_error_CouldntWriteToFile(tinfo, file_name));
  }
  // also possible to write it character by character using fputc
  fclose(fp);
  free(s);
  return make_Coq_Init_Datatypes_option_None();
}

short style_count = 1;

short c_color_of_coq_color(value c) {
  if (c == make_Vim_Foreign_color_black()) return COLOR_BLACK;
  if (c == make_Vim_Foreign_color_blue()) return COLOR_BLUE;
  if (c == make_Vim_Foreign_color_green()) return COLOR_GREEN;
  if (c == make_Vim_Foreign_color_cyan()) return COLOR_CYAN;
  if (c == make_Vim_Foreign_color_red()) return COLOR_RED;
  if (c == make_Vim_Foreign_color_magenta()) return COLOR_MAGENTA;
  if (c == make_Vim_Foreign_color_yellow()) return COLOR_YELLOW;
  if (c == make_Vim_Foreign_color_white()) return COLOR_WHITE;
  if (c == make_Vim_Foreign_color_bright_black()) return 8 | COLOR_BLACK;
  if (c == make_Vim_Foreign_color_bright_blue()) return 8 | COLOR_BLUE;
  if (c == make_Vim_Foreign_color_bright_green()) return 8 | COLOR_GREEN;
  if (c == make_Vim_Foreign_color_bright_cyan()) return 8 | COLOR_CYAN;
  if (c == make_Vim_Foreign_color_bright_red()) return 8 | COLOR_RED;
  if (c == make_Vim_Foreign_color_bright_magenta()) return 8 | COLOR_MAGENTA;
  if (c == make_Vim_Foreign_color_bright_yellow()) return 8 | COLOR_YELLOW;
  if (c == make_Vim_Foreign_color_bright_white()) return 8 | COLOR_WHITE;
}

typedef enum { PURE, BIND, EXIT, NEWWINDOW, CLOSEWINDOW,
               MOVECURSOR, GETCURSOR, GETSIZE, PRINT, 
               MAKE_STYLE, SET_WINDOW_DEFAULT_STYLE, START_STYLE, END_STYLE,
               REFRESH, CLEAR, GETCHAR,
               READ_FILE, WRITE_TO_FILE } M;

value runM(struct thread_info *tinfo, value action) {
  BEGINFRAME(tinfo, 2)
  // call the function with a unit to run the thunk from the coinductive
  action = GCSAVE1(tinfo, call(tinfo, action, make_Coq_Init_Datatypes_unit_tt()), action);
  switch (get_Vim_Foreign_C_MI_tag(action)) {
    case PURE:
      return get_args(action)[1];
    case BIND: {
      value arg0 = get_args(action)[2];
      value arg1 = get_args(action)[3];
      value temp = GCSAVE2(tinfo, runM(tinfo, arg0), arg0, arg1);
      temp = GCSAVE2(tinfo, call(tinfo, arg1, temp), arg1, temp);
      return runM(tinfo, temp);
    }
    case EXIT: {
      value arg0 = get_args(action)[0];
      if (arg0 == make_Vim_Foreign_exit_status_success()) {
        exit(EXIT_SUCCESS);
      } else {
        exit(EXIT_FAILURE);
      }
      return make_Coq_Init_Datatypes_unit_tt();
    }
    case NEWWINDOW: {
      value w = (value) initscr();
      noecho();
      /* curs_set(0); */
      start_color();
      return w;
    }
    case CLOSEWINDOW: {
      value w = get_args(action)[0];
      delwin(w);
      endwin();
      return make_Coq_Init_Datatypes_unit_tt();
    }
    case MOVECURSOR: {
      value w = get_args(action)[0];
      value arg0 = get_args(action)[1];
      value arg1 = get_args(action)[2];
      wmove(w, Unsigned_long_val(arg0), Unsigned_long_val(arg1));
      return make_Coq_Init_Datatypes_unit_tt();
    }
    case GETCURSOR: {
      value w = get_args(action)[0];
      value y = Val_long(getcury(w));
      value x = Val_long(getcurx(w));
      return alloc_make_Coq_Init_Datatypes_prod_pair(tinfo, y, x);
    }
    case GETSIZE: {
      value w = get_args(action)[0];
      value y = Val_long(getmaxy(w));
      value x = Val_long(getmaxx(w));
      return alloc_make_Coq_Init_Datatypes_prod_pair(tinfo, y, x);
    }
    case PRINT: {
      value w = get_args(action)[0];
      char *s = c_string_of_coq_ascii_list(get_args(action)[1]);
      waddstr(w, s);
      free(s);
      return make_Coq_Init_Datatypes_unit_tt();
    }
    case MAKE_STYLE: {
      value fg = c_color_of_coq_color(get_args(action)[0]);
      value bg = c_color_of_coq_color(get_args(action)[1]);
      init_pair(style_count, fg, bg);
      return style_count++;
    }
    case SET_WINDOW_DEFAULT_STYLE: {
      value w = get_args(action)[0];
      value style = get_args(action)[1];
      wbkgd(w, COLOR_PAIR(style));
      return make_Coq_Init_Datatypes_unit_tt();
    }
    case START_STYLE: {
      value style = get_args(action)[0];
      attron(COLOR_PAIR(style));
      return make_Coq_Init_Datatypes_unit_tt();
    }
    case END_STYLE: {
      value style = get_args(action)[0];
      attroff(COLOR_PAIR(style));
      return make_Coq_Init_Datatypes_unit_tt();
    }
    case REFRESH: {
      value w = get_args(action)[0];
      wrefresh(w);
      return make_Coq_Init_Datatypes_unit_tt();
    }
    case CLEAR: {
      value w = get_args(action)[0];
      wclear(w);
      return make_Coq_Init_Datatypes_unit_tt();
    }
    case GETCHAR: {
      value w = get_args(action)[0];
      return Val_long(wgetch(w));
    }
    case READ_FILE: {
      value file_name = get_args(action)[0];
      return read_file_into_coq_ascii_list(tinfo, file_name);
    }
    case WRITE_TO_FILE: {
      value file_name = get_args(action)[0];
      value content = get_args(action)[1];
      return write_file_from_coq_ascii_list(tinfo, file_name, content);
    }
    default: return 0;
  }
  ENDFRAME
}

value coq_argv_of_c_argv(struct thread_info *tinfo, int argc, char *argv[]) {
  value temp = make_Coq_Init_Datatypes_list_nil();
  for (int i = argc - 1; i >= 1; i--) {
    temp = alloc_make_Coq_Init_Datatypes_list_cons(tinfo, coq_ascii_list_of_c_string(tinfo, argv[i]), temp);
  }
  return temp;
}
