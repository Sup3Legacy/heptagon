/* --- Generated the 19/8/2012 at 9:24 --- */
/* --- heptagon compiler, version 0.4 (compiled sat. aug. 18 23:21:33 CET 2012) --- */
/* --- Command line: /Users/lgerard/W/heptagon/compiler/heptc.byte -stdlib /Users/lgerard/W/heptagon/lib -target c -O -s main simple.ept --- */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "_main.h"

Simple__main_mem mem;
int main(int argc, char** argv) {
  int step_c;
  int step_max;
  int _res;
  step_c = 0;
  step_max = 0;
  if ((argc==2)) {
    step_max = atoi(argv[1]);
  };
  Simple__main_reset(&mem);
  while ((!(step_max)||(step_c<step_max))) {
    step_c = (step_c+1);
    Simple__main_step(&_res, &mem);
    printf("=> ");
    printf("%d ", _res);
    puts("");
    fflush(stdout);
  };
  return 0;
}

