
#include "do.h"

void Do__stuff_step(int coeff) {
	int x = 13;
	for (int i = 0; i<coeff; i++) {
		for (int j = 0; j<10000; j++) {
			x = (x+j) % (x+j/x) + 13;
		}
	}
	return;
}

void Do__stuffi_step(int coeff, int *r) {
	Do__stuff_step(coeff);
	*r = coeff;
}
