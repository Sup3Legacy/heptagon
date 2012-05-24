
#include "futures.cpp"
#include "spsc_bounded_fifo.cpp"


#include <cassert> // for assert ()
#include <cstdlib> // for rand ()
#include <thread>


float do_stuff(int k) {
	float r = 0;
	for (int i = 0; i < k; k++ ) {
		 r = (((i - r + 15687) / (21+r) ) * (13-r) )/3;
	}
	return r;
}




/*int main() {
	for (int i = 0; i<10; i++){
		ft[i].future_float_activate();
		thread t(compute, i);
	}
	for (int i = 0; i<100000; i++)
		printf("valeur du future : %f\n",ft[i].future_float_get());
	printf("bonjour\n");
	return 0;
}*/


/*void produce(int k) {
	for (int i = 0; i < k; i ++) {
//		this_thread::sleep_for(chrono::nanoseconds(rand()%1));
		q.push(&i);
	}
//	q.wait_empty();
}*/

void consume(Queue<Future<int>,10> * q, int k) {
	Future<int> *f;
	int i = 0;
	while (1) { //for (int i = 0; i < 6*k-1; i ++) {
		f = q->get();
//		this_thread::sleep_for(chrono::nanoseconds(rand()%1));
//		printf("C%d (consumed %d)", i, *r);
		f->set(i);
		q->remove();
		i++;
	}
}


int main (int argv, char ** argc) {
	int k;
	if (argv<2) k = 100000;
	else k = atoi(argc[1]);
	

	Future<int> tf[1000];
	Queue<Future<int>,10> q;
	

	//threads
	thread c(consume, &q, k);
	pthread_setschedprio(c.native_handle(),1);

	//producer
	for (int i = 0; i < k; i++) {
		for (int j = 0; j < 5; j++) {
			tf[j].activate();
			q.push(& (tf[j]));
			printf("pushed %d", i*5+j);
		}
		for (int j = 0; j < 5; j++) {
			printf ("%d =?= %d\n", i*5+j, tf[j].get());
			assert((i*5+j) == tf[j].get());
		}
	}

	return 0;
}
