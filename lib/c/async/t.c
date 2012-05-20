#include <atomic>
#include <thread>
using namespace std;
extern "C" {

#include <stdio.h>

typedef struct future_float {
	private :
	volatile float o;
	atomic_bool not_ready;

	public :
	float future_float_get() {
		/* active wait on the read condition of the future */
		while (not_ready.load(memory_order_acquire)) {}
		return o;
	}
	
	void future_float_set(float o) {
		o = o;
		not_ready.store(false, memory_order_release);
	}
	
	void future_float_activate() {
		not_ready.store(true, memory_order_release);
	}
	
} future_float;


future_float ft[100000];

void compute(int i) {
	ft[i].future_float_set((float) i);
}

int main() {
	for (int i = 0; i<10; i++){
		ft[i].future_float_activate();
		thread t(compute, i);
	}
	for (int i = 0; i<100000; i++)
		printf("valeur du future : %f\n",ft[i].future_float_get());
	printf("bonjour\n");
	return 0;
}

}
