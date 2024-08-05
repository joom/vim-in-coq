#include <stdio.h>
#include <stdlib.h>
#include <gc_stack.c>
#include <prim_int63.c>
#include "main.h"
#include "foreign.h"
#include "glue.h"

int main(int argc, char *argv[]) {
  struct thread_info* tinfo = make_tinfo();
  value coq_argv = coq_argv_of_c_argv(tinfo, argc, argv);
  value prog = body(tinfo);
  prog = call(tinfo, prog, coq_argv);
  runM(tinfo, prog);
  return 0;
}
