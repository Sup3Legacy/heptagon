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
  // Create a future with a given already present value
  future(const T& v) : o(v), not_ready(false) {}
  //Prevent copy and move constructor, since it should never happen
  future(const future&) = delete;
  future(future && x) = delete;

  void reset() {
    not_ready.store(true, std::memory_order_release);
  }

  bool is_not_ready() const {
    return (not_ready.load(std::memory_order_acquire));
  }

  const T& get() const {
    // active wait on the read condition of the future
//	int i = 0;
    while (is_not_ready()) {
//      i++;
//      if(i > 300) {
//    	  i = 0;
//    	  std::this_thread::yield();
//      }
    }
    return o;
  }

  T* to_set() {
    return &(this->o);
  }

  void release() {
    not_ready.store(false, std::memory_order_release);
  }

  void set(const T& v) {
    *(to_set()) = v;
    release();
  }

  future<T> set2(const T& v) {
    set(v);
    return this;
  }

} CACHE_ALIGNED ;


#endif
