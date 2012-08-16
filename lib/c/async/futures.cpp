#include <atomic>
#include <thread>

#include "utils.h"

using namespace std;

template <typename T>
class Future {
	private :
	T o;
	atomic<bool> not_ready;

	public :
	T get() const {
		/* active wait on the read condition of the future */
		while (not_ready.load(memory_order_acquire)) {std::this_thread::yield();}
		return o;
	}
	
	void set(T o) {
		this->o = o;
		not_ready.store(false, memory_order_release);
	}
	
	void activate() {
		not_ready.store(true, memory_order_release);
	}
	
} CACHE_ALIGNED ;

