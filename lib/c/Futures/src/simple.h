/* --- Generated the 19/8/2012 at 9:24 --- */
/* --- heptagon compiler, version 0.4 (compiled sat. aug. 18 23:21:33 CET 2012) --- */
/* --- Command line: /Users/lgerard/W/heptagon/compiler/heptc.byte -stdlib /Users/lgerard/W/heptagon/lib -target c -O -s main simple.ept --- */

#ifndef SIMPLE_H
#define SIMPLE_H

typedef struct Simple__f_mem {
  int mem_z;
} Simple__f_mem;

void Simple__f_reset(Simple__f_mem* self);

void Simple__f_step(int x, int y, int* z, Simple__f_mem* self);

typedef struct Simple__main_mem {
  int mem_z;
  Simple__f_mem f;
} Simple__main_mem;

void Simple__main_reset(Simple__main_mem* self);

void Simple__main_step(int* z, Simple__main_mem* self);

#endif // SIMPLE_H
