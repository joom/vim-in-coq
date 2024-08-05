#include <stdio.h>
#include <stdlib.h>
#include <gc_stack.c>
#include <prim_int63.c>
#include "glue.h"
#include "foreign.h"

extern value body(struct thread_info *);

int main(int argc, char *argv[]) {
  struct thread_info* tinfo = make_tinfo();
  value result = body(tinfo);
  runM(tinfo, result);
  return 0;
}
