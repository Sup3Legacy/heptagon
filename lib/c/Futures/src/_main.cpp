/* --- Generated the 17/8/2012 at 15:53 --- */
/* --- heptagon compiler, version 0.4 (compiled wed. aug. 15 18:40:15 CET 2012) --- */
/* --- Command line: /Users/lgerard/W/heptagon/compiler/heptc.byte -stdlib /Users/lgerard/W/heptagon/lib -O -s main -target c simple.ept --- */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "_main.h"

Simple__main_mem mem;
int main(int argc, char** argv) {
  int step_c;
  int step_max;
  Simple__main_out _res;
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
    printf("%d ", _res.z);
    puts("");
    fflush(stdout);
  };
  return 0;
}

