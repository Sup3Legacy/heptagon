/* --- Generated the 17/8/2012 at 15:13 --- */
/* --- heptagon compiler, version 0.4 (compiled wed. aug. 15 18:40:15 CET 2012) --- */
/* --- Command line: /Users/lgerard/W/heptagon/compiler/heptc.byte -stdlib /Users/lgerard/W/heptagon/lib -target c -O simple.ept --- */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "simple_a.h"


WRAPPER_FUN_DEFS(Simple__f,int,(int x, int y),(x, y))
/*
template<int queue_size, int queue_nb>
void Simple__f_Areset(Simple__f_Amem<queue_size,queue_nb>* self) {
  self->reset();
}

template<int queue_size, int queue_nb>
void Simple__f_Astep(int x, int y, future<int>* _out,
    Simple__f_Amem<queue_size,queue_nb>* self) {
  self->step(x,y,_out);
}
*/

void ASimple__main_reset(ASimple__main_mem* self) {
  Simple__f_Areset(&self->f);
  self->__stock.reset_store(self->mem_z,0);
}


void ASimple__main_step(int* _out, ASimple__main_mem* self) {
  future<int>* v;
  self->__stock.tick();
  *_out = self->mem_z->get();
  Simple__f_Astep(3, 4, v = self->__stock.get_free(), &self->f);

  self->__stock.store_in(v,self->mem_z);
}

