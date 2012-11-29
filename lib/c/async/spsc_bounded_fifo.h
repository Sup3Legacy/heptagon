
#ifndef DECADES_SPSC_BOUNDED_H_
#define DECADES_SPSC_BOUNDED_H_


#include <atomic>
#include <condition_variable>
#include <iostream>
#include <thread>

#include "utils.h"

using namespace std;

template<typename T, int size>
class queue {

  typedef struct productor {
    atomic<int> current; //current writing position, should not get
    int max; //private local to the productor
    int next; //private local to the productor
    atomic<bool> present;
    productor() : current(0), max(size), present(false) {}
  } CACHE_ALIGNED productor;

  typedef struct consumer{
    atomic_int current; //current reading position, should not set
    int max; //private local to the consumer
    int next; //private local to the consumer
    consumer() : current(size), max(0) {}
  } CACHE_ALIGNED consumer;

  const int _size; //internal size is external size + 1
  T *data_array;
  condition_variable wake_up;
  mutex m;
  productor p;
  consumer c;

public:
  queue():_size(size+1),wake_up(),m(),p(),c(){
    data_array = new T[_size];
  }
  //Prevent copy constructor, since it should never happen
  queue(const queue&) = delete;
  ~queue() {
    delete[] data_array;
  }

  T* to_fill() {
    int current = p.current.load(memory_order_relaxed);
    if (current == p.max) {
      // need to synchro and wait for max to grow
      p.max = c.current.load(memory_order_acquire);
      while ( current == p.max ) {
        std::this_thread::yield();
        p.max = c.current.load(memory_order_acquire);
      }
    }
    p.next = INCR_MOD(current, _size);
    return &data_array[current];
  }

  void commit() {
    p.current.store(p.next, memory_order_release);
  }

  void push(T&& t) {
    *to_fill() = t;
    commit();
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
    int next = INCR_MOD(current,_size);
    if (next == c.max) {
      // need to synchro and wait for max to grow
      while (true) {
        prod_present = p.present.load(memory_order_acquire);
        c.max = p.current.load(memory_order_acquire);
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
    return &data_array[next];
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

#endif
