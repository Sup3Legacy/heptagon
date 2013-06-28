
#include "unopt.h"

static volatile int v_i = 0;

//Always return 0
void Unopt__i_step(int *o) {
	*o = v_i;
};

//Always return 0^n
void Unopt__ti240_step(array<int, 240> *o) {
	(*o)[0] = 0;
};
//Always return 0^n
void Unopt__ti24_step(array<int,24> *o) {
	(*o)[0] = 0;
};
//Always return 0^n
void Unopt__ti530_step(array<int, 530> *o) {
	(*o)[0] = 0;
};
//Always return 0^n
void Unopt__ti85_step(array<int, 85> *o) {
	(*o)[0] = 0;
};
//Always return 0^n
void Unopt__ti90_step(array<int, 90> *o) {
	(*o)[0] = 0;
};
//Always return 0^n
void Unopt__ti65_step(array<int, 65> *o) {
	(*o)[0] = 0;
};

//Always return 0^n
void Unopt__ti2400_step(array<int,2400> *o) {
	(*o)[0] = 0;
};
//Always return 0^n

void Unopt__ti24000_step(array<int,24000> *o) {
	(*o)[0] = 0;
};
