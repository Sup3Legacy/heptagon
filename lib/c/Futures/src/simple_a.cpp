/* --- Generated the 17/8/2012 at 15:13 --- */
/* --- heptagon compiler, version 0.4 (compiled wed. aug. 15 18:40:15 CET 2012) --- */
/* --- Command line: /Users/lgerard/W/heptagon/compiler/heptc.byte -stdlib /Users/lgerard/W/heptagon/lib -target c -O simple.ept --- */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "simple_a.h"

void ASimple__f_reset(ASimple__f_mem* self) {
  self->o = 0;
  Simple__f_reset(&self->s); //TODO cannot reset freely
}

void ASimple__f_step(int x, int y, ASimple__f_mem* self) {
  
}

void ASimple__main_reset(ASimple__main_mem* self) {
  ASimple__f_reset(&self->f);
  self->mem_z = 0;
}

void Simple__main_collect();


void ASimple__main_step(ASimple__main_out* _out, ASimple__main_mem* self) {
  Future<int> *v;
  _out->z = self->mem_z->get();
  ASimple__f_step(3, 4, &self->f);
  v = self->f.o;
  self->mem_z = v;;
}

