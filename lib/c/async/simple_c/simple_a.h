/* --- Generated the 17/8/2012 at 15:13 --- */
/* --- heptagon compiler, version 0.4 (compiled wed. aug. 15 18:40:15 CET 2012) --- */
/* --- Command line: /Users/lgerard/W/heptagon/compiler/heptc.byte -stdlib /Users/lgerard/W/heptagon/lib -target c -O simple.ept --- */

#ifndef ASIMPLE_H
#define ASIMPLE_H

#include "simple_types.h"
typedef struct ASimple__f_mem {
  int mem_z;
} ASimple__f_mem;

typedef struct ASimple__f_out {
  int z;
} ASimple__f_out;

void ASimple__f_reset(Simple__f_mem* self);

void ASimple__f_step(int x, int y, Simple__f_out* _out, Simple__f_mem* self);



typedef struct Simple__main_mem {
  int mem_z;
  ASimple__f_mem f;
} Simple__main_mem;

typedef struct Simple__main_out {
  int z;
} Simple__main_out;

void Simple__main_reset(Simple__main_mem* self);

void Simple__main_step(Simple__main_out* _out, Simple__main_mem* self);

#endif // SIMPLE_H
