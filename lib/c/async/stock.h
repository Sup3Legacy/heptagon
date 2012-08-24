/*
 * stock.h
 *
 *  Created on: 19 aožt 2012
 *      Author: lgerard
 */

#ifndef __DECADES_STOCK_H_
#define __DECADES_STOCK_H_

/** Define STOCK_EMPTYWHITES if the stock is not big enough
 * to never have empty white list.
 */
//#define STOCK_EMPTYWHITES

#include "utils.h"
#include <assert.h>

#include "futures.h"


template <typename T, int size>
class stock {
  /** Internal handling with doubly linked lists */
  typedef future<T>* ext_n;
  struct node {
    future<T> v;

    node * prev;
    node * next;
    int ref_count;
  };
  typedef node* n;

  /**
   * There is a mapping between [all] and the queues.
   * - [whites] stores the nodes which are not alive in the program.
   * - [grays] stores the nodes which are alive in the stack of the program.
   * - [blacks] stores the nodes which are alive in the memory of the program.
   * White and gray nodes are tagged as [unset].
   * Black nodes are tagged as:
   *   - [old] if they were stored before the last [tick()]
   *   - [fresh] if they were stored during the current tick.
   */
  node all[size];
  n whites;
  n grays;
  n blacks;

  inline void move(n &from, n x, n &dest) {
    //remove x from its list
    if (x == x->next)
      from = 0;
    else {
      x->prev->next = x->next;
      x->next->prev = x->prev;
      if (x == from)
        // x is the head of the queue, move the head correctly
        from = x->next;
    }
    //add it to the newlist
    if (dest) {
      x->prev = dest->prev;
      x->next = dest;
      x->prev->next = x;
      x->next->prev = x;
    }
    else {
      x->prev = x;
      x->next = x;
      dest = x;
    }
  }

  inline void move_from_whites(n x, n &dest) {
#ifdef STOCK_EMPTYWHITES
    move(whites, x, dest);
#else
    //remove x from the white list
    x->prev->next = x->next;
    x->next->prev = x->prev;
    if (x == whites)
      // x is the head of the queue, move the head correctly
      whites = x->next;
    assert(whites); //whites should stay non-empty
    //add x to the dest
    if (dest) {
      x->prev = dest->prev;
      x->next = dest;
      x->prev->next = x;
      x->next->prev = x;
    }
    else {
      x->prev = x;
      x->next = x;
      dest = x;
    }
#endif
  }

  inline void move_all(n &q1, n &q2) {
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

  inline void move_all_to_whites(n &q1) {
#ifdef STOCK_EMPTYWHITES
    move_all(q1,whites);
#else
    assert(whites); //The white queue should never be empty
    if (!q1) return;
    n end = q1->prev;
    whites->prev->next = q1;
    q1->prev = whites->prev;
    end->next = whites;
    whites->prev = end;
    q1 = 0;
#endif
  }

  inline n find_free() {
    assert(whites); //The white queue should never be empty
    n current = whites;
    int i = 0;
    while(current->v.is_not_ready()) {
      current = current->next;
      i++;
      if (i==size) {
        std::this_thread::yield();
      }
    }
    return current;
  }


public :
  stock() {
    for (int i = 0; i<size; i++) {
      all[i].prev = &all[DECR_MOD(i,size)];
      all[i].next = &all[INCR_MOD(i,size)];
      all[i].ref_count = 0;
      all[i].v.release(); //set all futures as ready
    }
    whites = &all[0];
    grays = 0;
    blacks = 0;
  }
  stock(const stock& ) = delete;


  ext_n get_free() {
    n x = find_free();
    move_from_whites(x,grays);
    x->v.reset();
    return (reinterpret_cast<ext_n>(reinterpret_cast<future<T>*>(x)));
  }


  /**
   * Sets the store [ext_x] to [o].
   * If the given black is null, it is initialized.
   */
  void reset_store(ext_n &ext_x, T o) {
    if (!ext_x) {
      ext_x = get_free_and_store();
    }
    ext_x->set(o);
  }
  inline ext_n get_free_and_store() {
    n x = find_free();
    move_from_whites(x,blacks);
    x->ref_count = 1;
    x->v.reset();
    return (reinterpret_cast<ext_n>(x));
  }

  /**
   * [oldx] should already be black (previously stored),
   *   it'll be set as ready (white) if it is not a fresh store.
   * [newx] will be set as stored and marked as a fresh store.
   *   it must be alive: either black or gray.
   * The freshness is reset by the tick function.
   */
  void store_in(ext_n ext_newx, ext_n &ext_oldx) {
    if (ext_newx == ext_oldx)
    {} //no_op
    else {
      store(ext_newx);
      unstore(ext_oldx); //unstore after store to deal with store_in(x,x)
      ext_oldx = ext_newx;
    }
  }
  inline void store(ext_n ext_newx) {
    n newx = reinterpret_cast<n>(ext_newx);
    if (newx->ref_count == 0) {// It is gray
      move(grays, newx, blacks);
      newx->ref_count = 1;
    }
    else // It is black
      newx->ref_count++;
  }
  inline void unstore(ext_n ext_oldx) {
    n oldx = reinterpret_cast<n>(ext_oldx);
    oldx->ref_count--;
    if (oldx->ref_count == 0)
      move(blacks, oldx, grays);
  }

  /**
   * Remove the freshness of black nodes
   * and move grays to white.
   */
  void tick() {
    //move gray to white
    move_all_to_whites(grays);
  }
};



#endif /* STOCK_H_ */
