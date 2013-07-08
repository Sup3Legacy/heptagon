#include "do.h"
#include "pervasives.h"
#include <cstdio>
using namespace std;

//Sur mon mac cela fait 65,2  secondes pour 10^11

int main() {
	int x;
	timeval t_begin;
	timeval t_end;
	gettimeofday(&t_begin, NULL);
	Do__stuffi_step(100000000000,&x);
	gettimeofday(&t_end, NULL);
	printf("time : %ld\n", diff_timeval(&t_begin, &t_end));
	fflush(stdout);
	return x;
}
