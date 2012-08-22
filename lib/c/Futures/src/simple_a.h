/* --- Generated the 17/8/2012 at 15:13 --- */
/* --- heptagon compiler, version 0.4 (compiled wed. aug. 15 18:40:15 CET 2012) --- */
/* --- Command line: /Users/lgerard/W/heptagon/compiler/heptc.byte -stdlib /Users/lgerard/W/heptagon/lib -target c -O simple.ept --- */

#ifndef ASIMPLE_H
#define ASIMPLE_H

#include "lib/futures.h"
#include "lib/async_node.h"
#include "lib/async_macros.h"
#include "lib/stock.h"

#include "simple.h"

WRAPPER_MEM_DEC(Simple__f,int,(int,int))

/*
template<int queue_size, int queue_nb>
using ASimple__f_mem =
    wrap<int,Simple__f_mem,int, int>
    ::async_node<Simple__f_step, Simple__f_reset, queue_size, queue_nb>
  ;
*/

typedef struct ASimple__main_mem {
  stock<int,3> __stock; //queue_size+1+mem_nb+nb_async_statics
  future<int>* mem_z;
  Simple__f_Amem<1,1> f;
} ASimple__main_mem;



void ASimple__main_reset(ASimple__main_mem* self);

void ASimple__main_step(int* _out, ASimple__main_mem* self);

#endif // ASIMPLE_H
