/* --- Generated the 19/8/2012 at 9:24 --- */
/* --- heptagon compiler, version 0.4 (compiled sat. aug. 18 23:21:33 CET 2012) --- */
/* --- Command line: /Users/lgerard/W/heptagon/compiler/heptc.byte -stdlib /Users/lgerard/W/heptagon/lib -target c -O -s main simple.ept --- */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "simple.h"

void Simple__f_reset(Simple__f_mem* self) {
  self->mem_z = 0;
}

void Simple__f_step(int x, int y, int* z, Simple__f_mem* self) {
  int v;
  v = (x+y);
  *z = self->mem_z;
  self->mem_z = v;;
}

void Simple__main_reset(Simple__main_mem* self) {
  Simple__f_reset(&self->f);
  self->mem_z = 0;
}

void Simple__main_step(int* z, Simple__main_mem* self) {
  
  int v;
  *z = self->mem_z;
  Simple__f_step(3, 4, &v, &self->f);
  self->mem_z = v;;
}

