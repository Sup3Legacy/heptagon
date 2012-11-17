
#include "htime.h"

struct Beg_of_time {
  struct timeval start_time;
  Beg_of_time() {
    gettimeofday(&start_time, NULL);
  }
};
  
Beg_of_time __time__decade_beg;
  
void Htime__get_um_time_step(long* o) {
  struct timeval t;
  gettimeofday(&t, NULL);
  *o = (long) (t.tv_sec - __time__decade_beg.start_time.tv_sec) * 1000000
    + (t.tv_usec - __time__decade_beg.start_time.tv_usec);
  return;
}

void Htime__get_m_time_step(long* o) {
  struct timeval t;
  gettimeofday(&t, NULL);
  *o = (long) (t.tv_sec - __time__decade_beg.start_time.tv_sec) * 1000
    + (t.tv_usec - __time__decade_beg.start_time.tv_usec)/1000;
  return;
}
  
