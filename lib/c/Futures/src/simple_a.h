/* --- Generated the 17/8/2012 at 15:13 --- */
/* --- heptagon compiler, version 0.4 (compiled wed. aug. 15 18:40:15 CET 2012) --- */
/* --- Command line: /Users/lgerard/W/heptagon/compiler/heptc.byte -stdlib /Users/lgerard/W/heptagon/lib -target c -O simple.ept --- */

#ifndef ASIMPLE_H
#define ASIMPLE_H

#include "lib/futures.h"
#include "lib/async.h"

#include "simple.h"


typedef Wrap<int,Simple__f_mem> ASimple__f_mem;


void ASimple__f_reset(ASimple__f_mem* self);

void ASimple__f_step(int x, int y, ASimple__f_mem* self);



typedef struct ASimple__main_mem {
  future<int>* mem_z;
  ASimple__f_mem f;
} ASimple__main_mem;

typedef struct ASimple__main_out {
  int z;
} ASimple__main_out;

void ASimple__main_reset(ASimple__main_mem* self);

void ASimple__main_step(ASimple__main_out* _out, ASimple__main_mem* self);

#endif // ASIMPLE_H
