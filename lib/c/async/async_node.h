/*
 * async.h
 *
 *      Author: lgerard
 */

#ifndef __DECADES_ASYNCNODE_H_
#define __DECADES_ASYNCNODE_H_

#include <Thread>
#include <functional>

#include "utils.h"
#include "futures.h"
#include "spsc_bounded_fifo.h"


template <typename Output, typename Mem, typename ... Inputs>
struct wrapnode {
  template<void(*f_step)(Inputs..., Output*, Mem*),
      void(*f_reset)(Mem*),
      int queue_size, int queue_nb>
  class async {

    typedef struct work_closure {
      function<void(Output*, Mem*)> ff;
      bool nreset;
      future<Output>* fo;
    } work_closure;
    typedef queue<work_closure,queue_size> work_queue;

    work_queue queues[queue_nb];
    thread **workers;
    int current_queue;
    bool need_reset;

  public:

    async():current_queue(0),need_reset(true) {
      workers = new thread*[queue_nb];
      for(int i = 0; i<queue_nb; i++) {
        workers[i] = new std::thread (
          [](work_queue *q) {
            signal(SIGINT,[](int i){pthread_exit(0);});
            signal(SIGTERM,[](int i){pthread_exit(0);});
            Mem m;
            f_reset(&m);
            while (true) {
              work_closure* r = q->get();
              if (r->nreset) f_reset(&m);
              r->ff(r->fo->to_set(), &m);
              r->fo->release();
              q->remove();
            }
          }
          , &queues[i]);
      }
    }

    //Prevent copy constructor, since it should never happen
    async(const async&) = delete;

    ~async() {
      for(int i = 0; i<queue_nb; i++)
        pthread_kill(workers[i]->native_handle(),SIGTERM);
      for(int i = 0; i<queue_nb; i++) {
        workers[i]->join();
        delete(workers[i]);
      }
      delete[](workers);
    }

    /** Push in the current queue and reset the [need_reset] flag.
     */
    void step(Inputs... i, future<Output>* o) {
      //create closure
      *queues[current_queue].to_fill() =
      {std::bind(f_step,i...,placeholders::_1,placeholders::_2),
          need_reset, o};
      //push it in the current queue
      queues[current_queue].commit();
      //reset the [reset] flag
      need_reset = false;
    }

    /** Round Robin choice of the queue and set the [need_reset] flag,
     * so that next time [step] is called, the flag will be true.
     */
    void reset() {
      queues[current_queue].detach_productor();
      current_queue = INCR_MOD(current_queue, queue_nb);
      queues[current_queue].attach_productor();
      need_reset = true;
    }

  };
};


#endif /* ASYNCNODE_H_ */