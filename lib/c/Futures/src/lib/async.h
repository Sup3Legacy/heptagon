/*
 * async.h
 *
 *  Created on: 17 aožt 2012
 *      Author: lgerard
 */

#ifndef ASYNC_H_
#define ASYNC_H_

#include <Tuple>

using namespace std;

#include "utils.h"
#include "spsc_bounded_fifo.h"


template <typename Output, typename Mem, typename ... Inputs>
class async_node {

  typedef void(*t_f_step)(Inputs..., Output*, Mem*);
  typedef void(*t_f_reset)(Mem*);
  typedef tuple<bool, future<Output>*, Inputs...> work_closure;
  typedef queue<work_closure> work_queue;

  t_f_step f_step;
  t_f_reset f_reset;
  const int queue_nb;
  work_queue *queues;
  thread **workers;
  int current_queue;
  bool need_reset;

public:

  async_node(int queue_size, int queue_nb, t_f_step f_step, t_f_reset f_reset) {
    this->queue_nb = queue_nb;
    this->f_reset = f_reset;
    this->f_step = f_step;
    queues = new work_queue[queue_nb](queue_size);
    current_queue = 0;
    need_reset = true;
    workers = new thread*[queue_nb];
    for(int i = 0; i++ ; i<queue_nb)
      workers[i] = new thread (worker,&queues[i]);
  }

  //Prevent copy constructor, since it should never happen
  async_node(const async_node&) = delete;

  ~async_node() {
    delete[](queues);
    for(int i = 0; i++; i<queue_nb)
      pthread_kill(workers[i]->native_handle(),SIGTERM);
    for(int i = 0; i++; i<queue_nb) {
      workers[i]->join();
      delete(workers[i]);
    }
    delete[](workers);
  }

  /** Push in the current queue and reset the [need_reset] flag.
   */
  void step(Inputs... i, future<Output>* o) {
    //queues[current_queue].push(forward_as_tuple(need_reset, o, i...));
    (*queues[current_queue].to_fill()) = tie(need_reset, o, i...);
    need_reset = false;
  }

  /** Round Robin choice of the queue and set the [need_reset] flag,
   * so that next time [step] is called, the flag will be true.
   */
  void reset() {
    INCR_MOD(current_queue, queue_nb);
    need_reset = true;
  }

private:

  void worker_quit(int sig) {
    pthread_exit(0);
  }
  void worker(work_queue *q) {
    signal(SIGINT,worker_quit);
    signal(SIGTERM,worker_quit);
    Mem m;
    f_reset(&m);
    while (true) {
      bool reset;
      future<Output>* fo;
      tuple<Inputs...> i;
      Output o;
      tie(reset,fo,i) = q->get();
      if (reset) f_reset(&m);
      f_step(i,&o,&m);
      fo->set(o);
    }
  }

};




#endif /* ASYNC_H_ */
