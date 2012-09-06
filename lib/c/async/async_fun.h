/*
 * async.h
 *
 *      Author: lgerard
 */

#ifndef __DECADES_ASYNCFUN_H_
#define __DECADES_ASYNCFUN_H_

#include <Thread>
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
    typedef queue<work_closure,queue_size> work_queue;

    work_queue queues[queue_nb];
    thread **workers;
    int current_queue;

  public:

    async():current_queue(0) {
      workers = new thread*[queue_nb];
      for(int i = 0; i<queue_nb; i++) {
    	queues[i].attach_productor(); //Proactif !!
        workers[i] = new std::thread (
          [](work_queue *q) {
            setsignal(SIGINT,[](int i){pthread_exit(0);});
            setsignal(SIGTERM,[](int i){pthread_exit(0);});
            while (true) {
              work_closure* r = q->get();
              r->ff(r->fo->to_set());
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
      for(int i = 0; i<queue_nb; i++) {
    	int r = pthread_kill(workers[i]->native_handle(),SIGTERM);
    	if (r==0) {
    		printf("killed %d\n",i);
    		fflush(stdout);
    	} else {
    		printf("killed failed %d\n",i);
    		fflush(stdout);
    	}
      }
      for(int i = 0; i<queue_nb; i++) {
        workers[i]->join();
        printf("joined %d\n",i);
        fflush(stdout);
        delete(workers[i]);
      }
      delete[](workers);
    }

    /** Push in the current queue and reset the [need_reset] flag.
     */
    void step(Inputs... i, future<Output>* o) {
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
};


#endif /* ASYNCFUN_H_ */
