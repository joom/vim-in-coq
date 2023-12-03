#include <stdio.h>
#include <stdlib.h>
#include <gc_stack.c>
#include <prim_int63.c>
#include "glue.h"

extern value body(struct thread_info *);

int main(int argc, char *argv[]) {

  // make infinite fuel!
  value fuel[2] = { 1024, 1 };
  value infiniteFuel = (value) (fuel + 1);
  fuel[1] = infiniteFuel;

  struct thread_info* tinfo = make_tinfo();
  value result = body(tinfo);
  result = call(tinfo, result, infiniteFuel);
  runM(tinfo, result);
  return 0;
}
