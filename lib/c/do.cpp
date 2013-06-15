
#include "do.h"
#include "stdlib.h"



//Always return 0
void Do__stuffi_step(long long coeff, int *r) {
	long long x = 13;
	coeff = (coeff<=0)?0:coeff;
	for (long long j = coeff; j>=0; j--) {
		for (int i = 0; i < 18; ++i)
			__asm__ __volatile__ ("addq %1, %0" : "+r"(x) : "r"(j) : "memory");
	}
	*r = (int)x;
	return;
};

void Do__stuff_step(long long coeff) {
	int x;
	Do__stuffi_step(coeff, &x);
	return;
}
