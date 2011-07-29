/* Pervasives module for the Decades compiler */

#ifndef DECADES_PERVASIVES_H
#define DECADES_PERVASIVES_H

/* between(i, n) returns idx between 0 and n-1.
   Because of a bug who sometimes occurs with Nvidia (even though extremely
   rare), we can't use the C version and return 0 when out of bounds. */
#define between(idx,n) ((idx < n) && (idx >= 0) ? idx : 0)

#endif

