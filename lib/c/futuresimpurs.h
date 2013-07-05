
#ifndef __DECADES_FUTURESIMPURS_H
#define __DECADES_FUTURESIMPURS_H

#include "async.h"
template<class T>
inline void Futuresimpurs__is_ready_step(future<T>* f, int * b) {
	*b = f->is_ready();
}

#endif
