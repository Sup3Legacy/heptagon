/* --- Generated the 17/8/2012 at 15:13 --- */
/* --- heptagon compiler, version 0.4 (compiled wed. aug. 15 18:40:15 CET 2012) --- */
/* --- Command line: /Users/lgerard/W/heptagon/compiler/heptc.byte -stdlib /Users/lgerard/W/heptagon/lib -target c -O simple.ept --- */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "simple_a.h"

void ASimple__f_reset(Simple__f_mem* self) {
  self->mem_z = 0;
}

void ASimple__f_step(int x, int y, Simple__f_out* _out, Simple__f_mem* self) {
  
  int v;
  v = (x+y);
  _out->z = self->mem_z;
  self->mem_z = v;;
}

void Simple__main_reset(Simple__main_mem* self) {
  Simple__f_reset(&self->f);
  self->mem_z = 0;
}

void Simple__main_step(Simple__main_out* _out, Simple__main_mem* self) {
  ASimple__f_out ASimple__f_out_st;
  
  int v;
  _out->z = self->mem_z;
  Simple__f_step(3, 4, &ASimple__f_out_st, &self->f);
  v = Simple__f_out_st.z;
  self->mem_z = v;;
}

