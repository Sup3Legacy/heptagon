/* Pervasives module for the Decades compiler */

#ifndef __DECADES_PERVASIVES_H
#define __DECADES_PERVASIVES_H

/* between(i, n) returns idx between 0 and n-1. */
static inline int between(int idx, int n)
{
  int o = (idx >= n) ? n-1 : (idx < 0 ? 0 : idx);
  return o;
}

static inline int int_of_bool(bool b)
{
  return b;
}

static inline bool bool_of_int(int i)
{
  return i;
}

static inline float float_of_int(int i)
{
  return ((float) i);
}

static inline int int_of_float(float i)
{
  return ((int) i);
}


#include <stdlib.h>
static inline int random(int i)
{
  return (rand()%i);
}









#include <sys/time.h>
typedef struct timeval timeval;
static inline long diff_timeval(timeval *starttime, timeval *finishtime)
{
  long msec;
  msec=(finishtime->tv_sec-starttime->tv_sec)*1000;
  msec+=(finishtime->tv_usec-starttime->tv_usec+500)/1000;
  return msec;
}

#endif

