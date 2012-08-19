/* --- Generated the 17/8/2012 at 15:13 --- */
/* --- heptagon compiler, version 0.4 (compiled wed. aug. 15 18:40:15 CET 2012) --- */
/* --- Command line: /Users/lgerard/W/heptagon/compiler/heptc.byte -stdlib /Users/lgerard/W/heptagon/lib -target c -O simple.ept --- */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "simple_a.h"


void ASimple__main_reset(ASimple__main_mem* self) {
  ASimple__f_reset(&self->f);
  self->mem_z = self->future_0;
}


void ASimple__main_step(int* _out, ASimple__main_mem* self) {
  future<int> *v;
  *_out = self->mem_z->get();


  ASimple__f_step(3, 4, v, &self->f);
  self->mem_z = v;;
}

