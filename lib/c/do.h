
#ifndef __DECADES_DO_H
#define __DECADES_DO_H


void Do__stuffi_step(long long coeff, int* r);
void Do__stuff_step(long long coeff);
int Do__neverend_step(int x, int* r);

inline void Do__stuffi_step(long long coeff, int* r) {
        long long x = 13;
//      coeff = (coeff<=0)?0:coeff;
        for (long long j = coeff; j>=0; j--) {
                __asm__ __volatile__ ("addq %1, %0" : "+r"(x) : "r"(j) : "memory");
        }
        *r = (int)x;
        return;
};

inline void Do__stuff_step(long long coeff) {
        int x;
        Do__stuffi_step(coeff, &x);
        return;
};

inline int Do__neverend_step(int x, int* r) {
	Do__stuffi_step(9999999999999999, r);
};
#endif
