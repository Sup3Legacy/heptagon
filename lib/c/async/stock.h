#ifndef __DECADES_STOCK_H_
#define __DECADES_STOCK_H_

/** Define STOCK_EMPTYWHITES if the stock is not big enough
 * to never have empty white list.
 */
//#define STOCK_EMPTYWHITES

#include <assert.h> //TODO assert c++ ?
#include "utils.h"
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
   * There is a mapping between [all] and the lists.
   * - [whites] stores the nodes which are not alive in the program.
   * - [blacks] stores the nodes which are alive in the memory of the program.
   * - [grays] stores all other nodes.
   * Black nodes use the ref_count to count black references.
   */
  node all[size];
  n whites, grays, blacks;

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
    assert(whites); //The white queue should not be empty here
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
    grays = nullptr;
    blacks = nullptr;
  }
  stock(const stock& ) = delete;


  ext_n get_free() {
    n x = find_free();
    move_from_whites(x,grays);
    return (reinterpret_cast<ext_n>(x));
  }


  /**
   * Sets the store [ext_x] to [o].
   * If the given black is null, it is initialized.
   * Only here for convenience
   */
  void reset_store(ext_n &ext_x, const T& o) {
    if (!ext_x) {
      ext_x = get_free_and_store();
    }
    (*ext_x->to_set()) = o;
    ext_x->release();
  }

  /**
   * Only here for speed,
   * from white to black without passing in gray
   */
  inline ext_n get_free_and_store() {
    n x = find_free();
    move_from_whites(x,blacks);
    x->ref_count = 1;
    return (reinterpret_cast<ext_n>(x));
  }

  /**
   * [oldx] is unstored.
   * [newx] is stored.
   * Only here for convenience (and speed)
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

  //Move gray to white.
  void tick() {
    move_all_to_whites(grays);
  }
};

#endif /* STOCK_H_ */
