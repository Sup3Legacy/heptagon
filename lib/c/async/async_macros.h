/*
 * async_macros.h
 *
 *  Created on: 21 ao�t 2012
 *      Author: lgerard
 */

#ifndef __DECADES_ASYNC_MACROS_H_
#define __DECADES_ASYNC_MACROS_H_

//Stock is the stock name, Mem the memory name, Value is the value to be stored
//#define STORE_STATIC_FUTURE(Stock,Mem,Value) {\
//  self->Mem = self->Stock.get_free_and_store().set(Value);\
//}

//Stock is the stock name, Value is the value to be stored
//#define STATIC_FUTURE(Stock,Value) self->Stock.get_free().set(Value)

#define STRIP(...) __VA_ARGS__


#define WRAPPER_NODE_MEM_DEC(WRAPPED,OUT,IN)\
  template<int queue_size = 1 , int queue_nb = 1>\
using WRAPPED##_Amem =\
    wrapnode<STRIP OUT,WRAPPED##_mem STRIP IN>\
    ::async<WRAPPED##_step, WRAPPED##_reset, queue_size, queue_nb>;

#define WRAPPER_NODE_DEFS(WRAPPED,OUT,IN,ARGS)\
template<int queue_size, int queue_nb>\
void WRAPPED##_Areset(WRAPPED##_Amem<queue_size,queue_nb>* self) {\
  self->reset();\
}\
template<int queue_size = 1, int queue_nb = 1>\
void WRAPPED##_Astep(STRIP IN future<STRIP OUT>* _out,\
    WRAPPED##_Amem<queue_size,queue_nb>* self) {\
  self->step(STRIP ARGS _out);\
}


#define WRAPPER_FUN_MEM_DEC(WRAPPED,OUT,IN)\
  template<int queue_size = 1 , int queue_nb = 1>\
using WRAPPED##_Amem =\
    wrapfun<STRIP OUT STRIP IN>\
    ::async<WRAPPED##_step, queue_size, queue_nb>;

#define WRAPPER_FUN_DEFS(WRAPPED,OUT,IN,ARGS)\
template<int queue_size = 1, int queue_nb = 1>\
void WRAPPED##_Astep(STRIP IN future<STRIP OUT>* _out,\
    WRAPPED##_Amem<queue_size,queue_nb>* self) {\
  self->step(STRIP ARGS _out);\
}



#endif /* ASYNC_MACROS_H_ */
