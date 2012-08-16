//
//  main.cpp
//  FutureLustre
//
//  Created by Leonard Gerard on 16/08/12.
//  Copyright (c) 2012 Leonard Gerard. All rights reserved.
///Users/lgerard/Desktop/FutureLustre/FutureLustre.xcodeproj

#include "futures.cpp"
#include "spsc_bounded_fifo.cpp"

#include "utils.h"

#include <cassert> // for assert ()
#include <cstdlib> // for rand ()
#include <thread>

using namespace std;

float do_stuff(int k) {
	float r = 0;
	for (int i = 0; i < k; k++ ) {
        r = (((i - r + 15687) / (21+r) ) * (13-r) )/3;
	}
	return r;
}




/*int main() {
 for (int i = 0; i<10; i++){
 ft[i].future_float_activate();
 thread t(compute, i);
 }
 for (int i = 0; i<100000; i++)
 printf("valeur du future : %f\n",ft[i].future_float_get());
 printf("bonjour\n");
 return 0;
 }*/


/*void produce(int k) {
 for (int i = 0; i < k; i ++) {
 //		this_thread::sleep_for(chrono::nanoseconds(rand()%1));
 q.push(&i);
 }
 //	q.wait_empty();
 }*/

void consume(Queue<Future<int> > * q, int k) {
	Future<int> *f;
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
    
    Future<int> tf[burst];
    Queue<Future<int> > q(burst+marge);
	
    
    //threads
    thread c(consume, &q, k);
    //	pthread_setschedprio(c.native_handle(),1);
    
    //producer
	q.attach_productor();
    for (int i = 0; i < k; i++) {
        DPRINT("index %d",i);
        q.attach_productor();
        for (int j = 0; j < burst; j++) {
            tf[j].activate();
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
