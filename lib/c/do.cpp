
#include "do.h"

void Do__stuff_step(long long coeff, int *r) {
	long long x = 13;
	coeff = (coeff<=0)?0:coeff;
	for (long long i = 0; i<4; i++) {
		for (long long j = coeff; j>0; j--) {
			x = (x+j) % (x+j/x) + 13;
		}
	}
	*r = x;
	return;
}
