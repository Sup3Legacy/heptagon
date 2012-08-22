//
//  utils.h
//  FutureLustre
//
//  Created by Leonard Gerard on 16/08/12.
//  Copyright (c) 2012 Leonard Gerard. All rights reserved.
//

#ifndef FutureLustre_utils_h
#define FutureLustre_utils_h


#define CACHE_LINE_SIZE 64
#define CACHE_ALIGNED __attribute__ ((aligned(CACHE_LINE_SIZE)))

#ifdef DDEBUG
#define DPRINT(...) { fprintf( stderr, __VA_ARGS__ ); fflush(stderr); }
#else
#define DPRINT(...)
#endif

#define INCR_MOD(X,M) (X+1>=M)?0:X+1
#define DECR_MOD(X,M) (X-1>=0)?X-1:M-1


#endif
