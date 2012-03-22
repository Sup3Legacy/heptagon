/* Pervasives module for the Decades compiler */

#ifndef DECADES_PERVASIVES_H
#define DECADES_PERVASIVES_H

/* between(i, n) returns idx between 0 and n-1. */
static inline int between(int idx, int n)
{
#ifndef HEPT_DISABLE_BOUND_CHECKS
  int o = (idx >= n) ? n-1 : (idx < 0 ? 0 : idx);
#else
  int o = idx;
#endif
  return o;
}

/* is_between(i, a, b) returns a <= i < b */
static inline bool is_between(int idx, int a, int b)
{
#ifndef HEPT_DISABLE_BOUND_CHECKS
  return (a <= idx) && (idx < b);
#else
  return true;
#endif
}

#define int_of_bool(b) (b)

static inline bool bool_of_int(int i)
{
  return i;
}

#endif

