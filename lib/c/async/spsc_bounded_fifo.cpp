#include <cassert>
#include <thread>
#include <atomic>
#include <condition_variable>
#include <iostream>
#define CACHE_LINE_SIZE 64
#define CACHE_ALIGNED __attribute__ ((aligned(CACHE_LINE_SIZE)))

using namespace std;

template<typename T>
struct added_data {
	T data;
} CACHE_ALIGNED;

template<typename T, int size>
class Queue {
	T data_array[size];
	
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
	void push(T* t) {
		int current = p.current.load(memory_order_relaxed);
		int next = (current >= size) ? 0 : current + 1;
		if (next == p.max) {
			// need to synchro and wait for max to grow
			p.max = c.current.load(memory_order_acquire);
			while ( next == p.max ) {
				// active wait because the producer can be sure that a c.is there
				//lock_guard<mutex> lock(m);
				//wake_up.wait(lock);
				p.max = c.current.load(memory_order_acquire);
			}
		}
		// effectively push
		data_array[current] = *t;
		p.current.store(next, memory_order_release);
		// if some thread was waiting on a producer, wake it up
		wake_up.notify_all();
	}

	T * get() {
		int current = c.current.load(memory_order_relaxed);
		int next = (current >= size) ? 0 : current + 1;
		if (next == c.max) {
			// need to synchro and wait for max to grow
			c.max = p.current.load(memory_order_acquire);
			while ( next == c.max ) {
				// passive wait, we never know if a producer is here.
				// TODO do some active wait before waiting.
				unique_lock<mutex> lock(m);
				wake_up.wait(lock);
				// synchronize and verify that we wake up on the right purpose
				c.max = p.current.load(memory_order_acquire);
			}
		}
		c.next = next;
		// Do not change the current for now, until remove is called
		return &data_array[next];
	}

	void remove() {
		// release the current one.
		c.current.store(c.next, memory_order_release);
	}

	void pop(T * in) {
		*in = *get();
		remove();
	}
			

};


Queue<int,5> q;

void produce() {
	for (int i = 0; i < 1000; i ++) {
		q.push(&i);
	}
}

void consume() {
	int r;
	for (int i = 0; i < 999; i ++) {
		q.pop(&r);
		assert(r == i);
		printf("C%d (consumed %d)\n", i, r);
	}
}


int main () {
	thread p(produce);
	thread c(consume);
	p.join();
	c.join();
	return 0;
}
