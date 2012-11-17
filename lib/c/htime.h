
#ifndef __DECADES_HTIME_H
#define __DECADES_HTIME_H

extern "C" {
#include <sys/time.h>
}

void Htime__get_um_time_step(long* t);
void Htime__get_m_time_step(long* t);
#endif
