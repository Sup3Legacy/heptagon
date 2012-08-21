/*
 * async.h
 *
 *  Created on: 17 aožt 2012
 *      Author: lgerard
 */

#ifndef ASYNC_H_
#define ASYNC_H_

#include <Tuple>
#include <Thread>

using namespace std;

#include "utils.h"
#include "spsc_bounded_fifo.h"

void worker_quit(int sig) {
  pthread_exit(0);
}

template <typename Output, typename Mem, typename ... Inputs>
struct wrapper {
  template < void(*f_step)(Inputs..., Output*, Mem*),
             void(*f_reset)(Mem*),int queue_size = 1, int queue_nb = 1>
  class async_node {
    struct work_closure {
      bool reset;
      future<Output>* out;
      tuple<Inputs...> in;
    };

    typedef queue<work_closure,queue_size> work_queue;

    work_queue *queues;
    thread **workers;
    int current_queue;
    bool need_reset;

  public:

    async_node() {
      queues = new work_queue[queue_nb];
      current_queue = 0;
      need_reset = true;
      workers = new thread*[queue_nb];
      for(int i = 0; i<queue_nb; i++)
        workers[i] = new thread (worker,&queues[i]);
    }

    //Prevent copy constructor, since it should never happen
    async_node(const async_node&) = delete;

    ~async_node() {
      delete[](queues);
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
      //queues[current_queue].push(forward_as_tuple(need_reset, o, i...));
      (*queues[current_queue].to_fill()) = {need_reset, o, tie(i...)};
      queues[current_queue].commit();
      need_reset = false;
    }

    /** Round Robin choice of the queue and set the [need_reset] flag,
     * so that next time [step] is called, the flag will be true.
     */
    void reset() {
      current_queue = INCR_MOD(current_queue, queue_nb);
      need_reset = true;
    }

  private:

    void worker(work_queue *q) {
      signal(SIGINT,worker_quit);
      signal(SIGTERM,worker_quit);
      Mem m;
      f_reset(&m);
      while (true) {
        struct work_closure *r;
        r = q->get();
        if (r->reset) f_reset(&m);
        tuple<int,int> t = {0,2};
        f_step(t, r->out->get_to_set(), &m);
        r->out->release();
        q->remove();
      }
    }

  };
};



#endif /* ASYNC_H_ */
