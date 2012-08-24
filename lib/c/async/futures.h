
#ifndef DECADES_FUTURES_H_
#define DECADES_FUTURES_H_


#include <atomic>
#include <thread>

#include "utils.h"


template <typename T>
class future {
private :
  T o;
  std::atomic<bool> not_ready = {true};

public :

  future() : not_ready(true) {}

  /** Create a future with a given already present value.
   */
  future(T v) : o(v), not_ready(false) {}

  //Prevent copy constructor, since it should never happen
  future(const future&) = delete;


  void release() {
    not_ready.store(false, std::memory_order_release);
  }

  void reset() {
    not_ready.store(true, std::memory_order_release);
  }

  bool is_not_ready() const {
    return (not_ready.load(std::memory_order_acquire));
  }

  T get() const {
    /* active wait on the read condition of the future */
    while (is_not_ready()) {
      std::this_thread::yield();
    }
    return o;
  }

  void set(T o) {
    this->o = o;
    release();
  }

  future<T>* set2(T o) {
    set(o);
    return this;
  }

  T* to_set() {
    return &(this->o);
  }

} CACHE_ALIGNED ;


#endif
