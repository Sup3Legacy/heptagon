//
//  main.cpp
//  FutureLustre
//
//  Created by Leonard Gerard on 16/08/12.
//  Copyright (c) 2012 Leonard Gerard. All rights reserved.
///Users/lgerard/Desktop/FutureLustre/FutureLustre.xcodeproj

#include "futures.h"
#include "spsc_bounded_p_fifo.h"

#include "utils.h"

#include <cassert> // for assert ()
#include <cstdlib> // for rand ()
#include <thread>

using namespace std;


/*
#include "stock.h"

int main(int argc, const char * argv[]) {
  stock<int,6> s;
  future<int>* mem1,mem2,mem3;
  future<int>* local1,local2;

  s.tick();

  s.get_free()->set(0);
  local1 = s.get_free();
  s.get_free()->set(1);

  mem1 = local1;
  s.store_in(mem1,local1);

}

*/

/*
float do_stuff(int k) {
  float r = 0;
  for (int i = 0; i < k; k++ ) {
    r = (((i - r + 15687) / (21+r) ) * (13-r) )/3;
  }
  return r;
}



void consume(queue<future<int> > * q, int k) {
  future<int> *f;
  int i = 0;
  while (true) {
    f = q->get();
    f->set(i);
    q->remove();
    i++;
  }
}

void terminate(int sig) {
  exit(0);
}


int main (int argc, const char * argv[]) {
  signal(SIGTERM, terminate);
  signal(SIGINT, terminate);
  int k;
  int burst;
  int marge;
  if (argc<2) k = 1000;
  else k = atoi(argv[1]);
  if (argc<3) burst = 1000;
  else burst = atoi(argv[2]);
  if (argc<4) marge = 0;
  else marge = atoi(argv[3]);

  future<int> *tf = new future<int>[burst];
  queue<future<int> > q(burst+marge);


  //threads
  thread c(consume, &q, k);
  //	pthread_setschedprio(c.native_handle(),1);

  //producer
  q.attach_productor();
  for (int i = 0; i < k; i++) {
    DPRINT("index %d",i);
    q.attach_productor();
    for (int j = 0; j < burst; j++) {
      tf[j].reset();
      q.push(& (tf[j]));
      DPRINT("pushed %d\n", i*burst+j);
    }
    q.detach_productor();
    for (int j = 0; j < burst; j++) {
      DPRINT("%d =?= %d\n", i*burst+j, tf[j].get());
      assert((i*burst+j) == tf[j].get());
    }
  }
  printf("joining\n");
  fflush(stdout);
  pthread_kill(c.native_handle(), SIGTERM);
  c.join();
  return 0;
}
*/
