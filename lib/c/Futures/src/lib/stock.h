/*
 * stock.h
 *
 *  Created on: 19 aožt 2012
 *      Author: lgerard
 */

#ifndef STOCK_H_
#define STOCK_H_

#include "utils.h"

enum class Flag { unset, fresh };

template <typename T>
struct node {
  future<T> v;

  node * prev;
  node * next;
  Flag flag;
};

template <typename T, int size>
class stock {
  typedef node<T>* n;
  node<T> all[size];
  n whites;
  n grays;
  n blacks;

  void inline move_to_tail(n x, n &new_queue) {
    if (new_queue) {
      //remove x from its list
      x->prev->next = x->next;
      x->next->prev = x->prev;
      //add it to the newlist
      x->prev = new_queue->prev;
      x->next = new_queue;
      new_queue->prev = x;
    }
    else {
      x->prev = x;
      x->next = x;
      new_queue = x;
    }
  }

  void inline move_all(n &q1, n &q2) {
    if (!q1) return;
    if (q2) {
      n end = q1->prev;
      q2->prev->next = q1;
      q1->prev = q2->prev;
      end->next = q2;
      q2->prev = end;
    }
    else {
      q2 = q1;
    }
    q1 = 0;
  }

  void inline move_to_head(n x, n &new_queue) {
    move_to_tail(x,new_queue);
    //rehead new_queue to point to x
    new_queue = x;
  }

public :
  stock() {
    for (int i = 0; i++; i<size) {
      all[i].prev = &all[DECR_MOD(i,size)];
      all[i].next = &all[INCR_MOD(i,size)];
      all[i].flag = Flag::unset;
    }
    whites = &all[0];
    grays = 0;
    blacks = 0;
  }
  stock(const stock& ) = delete;

  T* get_free() {
    n current = whites;


  }

  /**
   * [oldx] should already be black (previously stored),
   *   it'll be set as ready (white) if it is not a fresh store.
   * [newx] will be set as stored and marked as a fresh store.
   *
   * The freshness is reset by the tick function.
   */
  void store_swap(n oldx, n newx) {
    move_to_tail(newx, blacks);
    newx->flag = Flag::fresh;
    if (oldx->flag == Flag::fresh) { /*It should stay black*/ }
    else { move_to_tail(oldx, whites); }
  }

  /**
   * Remove the freshness of black nodes
   * and move gray to white.
   */
  void tick() {
    //move gray to white
    move_all(grays,whites);
    //remove flags of the blacks
    n current = blacks;
    do current->flag = Flag::unset;
    while((current = current->next) != blacks);
  }


};



#endif /* STOCK_H_ */
