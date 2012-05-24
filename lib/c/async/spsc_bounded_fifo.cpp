#include <atomic>
#include <condition_variable>
#include <iostream>

#include "misc.h"

using namespace std;


/*
 * Buggy for know, since the reader may check the queue, see it is empty, then the producer add a value and notify it, then the consumer go to sleep.
 * I don't know how to prevent that without requiring the writer to acquire a lock on m each time it adds a value.... then the lock free part will be very tenuous.
 * It seems not to happen ( maybe something is missing in my analyse or my tests ).
 */

template<typename T, int size>
class Queue {
	T* data_array[size+1];
	
	struct productor {
		atomic<int> current;
		int max;
	} CACHE_ALIGNED p = {{0},size};

	struct consumer{
		atomic<int> current;
		int max;
		int next;
	} CACHE_ALIGNED c = {{size},0,0};

	condition_variable wake_up;
	mutex m;
	public:
	void push(T * t) {
		int current = p.current.load()/*(memory_order_relaxed)*/;
		int next = (current >= size) ? 0 : current + 1;
		if (next == p.max) {
			// need to synchro and wait for max to grow
			p.max = c.current.load()/*(memory_order_acquire)*/;
			while ( next == p.max ) {
				// active wait because the producer can be sure that a c.is there
				wake_up.notify_one();
				p.max = c.current.load()/*(memory_order_acquire)*/;
			}
		}
		// effectively push
		data_array[current] = t;
		p.current.store(next, memory_order_release);
		// if some thread was waiting on a producer, wake it up
		wake_up.notify_one();
	}

	T * get() {
		int current = c.current.load()/*(memory_order_relaxed)*/;
		int next = (current >= size) ? 0 : current + 1;
		if (next == c.max) {
			// need to synchro and wait for max to grow
			//c.max = p.current.load()/*(memory_order_acquire)*/;
			p.current.compare_exchange_weak(c.max,c.max); //TODO memory_order ?

			for (int i = 0; next == c.max && i < 1000; i++ ) { // busy wait
				c.max = p.current.load(memory_order_acquire);
			}
			while ( next == c.max ) {
				// passive wait, we never know if a producer is here.
				// TODO do some active wait before waiting.
				printf("C sleep waiting for %d\n",next);
				fflush(stdout);
				unique_lock<mutex> lock(m);
				wake_up.wait(lock);
				printf("C woke up\n");
				fflush(stdout);
				// synchronize and verify that we woke up on the right purpose
				p.current.compare_exchange_weak(c.max,c.max); //TODO memory_order ?
			}
		}
		// relaxed on c.next since only the consumer should get and remove
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

