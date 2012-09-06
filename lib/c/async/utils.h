//
//  utils.h
//  FutureLustre
//
//  Created by Leonard Gerard on 16/08/12.
//

#ifndef __DECADES_UTILS_H
#define __DECADES_UTILS_H


#define CACHE_LINE_SIZE 64
#define CACHE_ALIGNED __attribute__ ((aligned(CACHE_LINE_SIZE)))

#ifdef DDEBUG
#define DPRINT(...) { fprintf( stderr, __VA_ARGS__ ); fflush(stderr); }
#else
#define DPRINT(...)
#endif

#define INCR_MOD(X,M) (X+1>=M)?0:X+1
#define DECR_MOD(X,M) (X-1>=0)?X-1:M-1



#include <cstdlib>
#include <cstring>
#include <csignal>
#include <iostream>

using namespace std;

static void setsignal(int signum, void (*sighandler)(int), int options) {
  struct sigaction s;
  memset(&s, (char)0, sizeof(s));
  s.sa_handler = sighandler;
  sigemptyset(&s.sa_mask);
  s.sa_flags = options;
  if (sigaction(signum, &s, NULL) < 0) {
    cerr << "Unable to set signal handler";
    exit(EXIT_FAILURE);
  }
}






#endif
