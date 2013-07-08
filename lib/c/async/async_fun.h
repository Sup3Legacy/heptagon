/*
 * async.h
 *
 *      Author: lgerard
 */

#ifndef __DECADES_ASYNCFUN_H_
#define __DECADES_ASYNCFUN_H_

#include <thread>
#include <functional>

#include "utils.h"
#include "futures.h"
#include "spsc_bounded_fifo.h"


template <typename Output, typename ... Inputs>
struct wrapfun {
  template<void(*f_step)(Inputs..., Output*),
      int queue_size, int queue_nb>
  class async {

    typedef struct work_closure {
      function<void(Output*)> ff;
      future<Output>* fo;
    } work_closure;
    // We work in place in the queue, so we need one more place
    typedef queue<work_closure,queue_size+1> work_queue;

    work_queue queues[queue_nb];
    int current_queue;

  public:

    async():current_queue(0) {
      for(int i = 0; i<queue_nb; i++) {
    	queues[i].attach_productor(); //Proactif !!
        (new std::thread (
          [](work_queue *q) {
            while (true) {
              work_closure* r = q->get();
              r->ff(r->fo->to_set());
              r->fo->release();
              q->remove();
            }
          }
          , &queues[i]))->detach();
      }
    }

    //Prevent copy constructor, since it should never happen
    async(const async&) = delete;

    /** Push in the current queue and reset the [need_reset] flag.
     */
    void step(Inputs... i, future<Output>* o) {
      o->reset();
      //create closure
      *queues[current_queue].to_fill() =
      {std::bind(f_step,i...,placeholders::_1),o};
      //push it in the current queue
      queues[current_queue].commit();
    }

    /** Round Robin choice of the queue and set the [need_reset] flag,
     * so that next time [step] is called, the flag will be true.
     */
    void reset() {
      current_queue = INCR_MOD(current_queue, queue_nb);
    }

  };

  template<void(*f_step)(Inputs..., Output*),
        int queue_size>
    class async<f_step, queue_size, 0> {
    public:
      async(){ }
      void step(Inputs... i, future<Output>* o) {
    	o->reset();
      	f_step(i..., o->to_set());
      	o->release();
      }
      void reset() {
      }
    };

};


#endif /* ASYNCFUN_H_ */
