
#ifndef __DECADES_FUTURESIMPURS_H
#define __DECADES_FUTURESIMPURS_H

#include "async.h"
inline void Futuresimpurs__is_ready_i_step(future<int>* f, int * b) {
	*b = f->is_ready();
}

inline void Futuresimpurs__is_ready_b_step(future<int>* f, int * b) {
	*b = f->is_ready();
}
#endif
