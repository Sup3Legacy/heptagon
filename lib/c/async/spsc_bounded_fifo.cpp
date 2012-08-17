#include <atomic>
#include <condition_variable>
#include <iostream>

#include "utils.h"

using namespace std;

/*
 * Buggy for know, since the reader may check the queue, see it is empty, then the producer add a value and notify it, then the consumer go to sleep.
 * I don't know how to prevent that without requiring the writer to acquire a lock on m each time it adds a value.... then the lock free part will be very tenuous.
 * It seems not to happen ( maybe something is missing in my analyse or my tests ).
 */

template<typename T>
class Queue {

  T* *data_array;
    const int size;
	
  typedef struct productor {
    atomic_int current;
    int max; //private local to the productor
    atomic<bool> present;
    productor(int size) : current(0), max(size), present(false) {}
  } CACHE_ALIGNED productor;

    productor p;

  typedef struct consumer{
    atomic_int current;
    int max; //private local to the consumer
    int next; //private local to the consumer
      consumer(int size) : current(size), max(0), next(0) {}
  } CACHE_ALIGNED consumer;

    consumer c;

  condition_variable wake_up;
  mutex m;
public:
    Queue(int s):size(s+1),wake_up(),m(),p(size),c(size){
        data_array = new T*[size];
    }
    ~Queue() {
        delete[] data_array;
    }
  void push(T * t) {
    int current = p.current.load(memory_order_relaxed);
    int next = (current >= size) ? 0 : current + 1;
    if (next == p.max) {
      // need to synchro and wait for max to grow
      p.max = c.current.load(memory_order_acquire);
      while ( next == p.max ) {
	//TODO stall for better busy wait
	p.max = c.current.load(memory_order_acquire);
      }
    }
    // effectively push
    data_array[current] = t;
    p.current.store(next, memory_order_release);
  }
	
  void attach_productor () {
    unique_lock<mutex> lock(m);
      DPRINT("attach\n");
      // no memory order since the mutex is here to force it
    p.present.store(true,memory_order_relaxed);
    wake_up.notify_all();
  }

  void detach_productor () {
    unique_lock<mutex> lock(m);
    // no memory order since the mutex is here to force it
    p.present.store(false, memory_order_relaxed);
  }

  T * get() {
    bool prod_present;
    int current = c.current.load(memory_order_relaxed);
    int next = (current >= size) ? 0 : current + 1;
    if (next == c.max) {
      // need to synchro and wait for max to grow
      while (true) {
	prod_present = p.present.load(memory_order_acquire);
	c.max = p.current.load(memory_order_acquire);
	//since [present] is retrieved before [current],
	//if not present then [current] is the last current place,
	//the consumer may then sleep until a new prod is attached
	if (next != c.max) break; // finish busy wait
	else if (!prod_present) {
	  unique_lock<mutex> lock(m);
	  //be sure
	  prod_present = p.present.load(memory_order_acquire);
	  c.max = p.current.load(memory_order_acquire);
	  if (next != c.max) break;
	  else if (!prod_present) {
	    //we are sure no prod and max too small
	    wake_up.wait(lock);
	  }	  
	}
      }
    }
    c.next = next;
    // Do not change the current for now, until remove is called
    return data_array[next];
  }

  void remove() {
    // release the current one. relaxed on c.next since only the consumer should get and remove.
    c.current.store(c.next, memory_order_release);
  }

  void pop(T * in) {
    *in = *get();
    remove();
  }

};

