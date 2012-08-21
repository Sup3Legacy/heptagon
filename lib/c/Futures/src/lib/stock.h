/*
 * stock.h
 *
 *  Created on: 19 aožt 2012
 *      Author: lgerard
 */

#ifndef STOCK_H_
#define STOCK_H_

#include "utils.h"
#include "assert.h"

/*TODO Si l'on est certain que white ne sera jamais vide,
       il y a des tests que l'on peu enlever. */
template <typename T, int size>
class stock {
  /** Internal handling with doubly linked lists */
  typedef future<T>* ext_n;
  enum class Flag { unset, old, fresh };
  struct node {
    future<T> v;

    node * prev;
    node * next;
    Flag flag;
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

  void inline move_to_tail(n &from, n x, n &dest) {
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

  void inline move_to_black(n &from, n x) {
    move_to_tail(from,x,blacks);
    x->flag = Flag::fresh;
  }

  void inline move_black_to_white(n x) {
    move_to_tail(blacks,x,whites);
    x->flag = Flag::unset;
  }

  void inline move_gray_to_white(n x) {
    move_to_tail(grays,x,whites);
  }

  void inline move_white_to_gray(n x) {
    move_to_tail(whites,x,grays);
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


public :
  stock() {
    for (int i = 0; i<size; i++) {
      all[i].prev = &all[DECR_MOD(i,size)];
      all[i].next = &all[INCR_MOD(i,size)];
      all[i].flag = Flag::unset;
    }
    whites = &all[0];
    grays = 0;
    blacks = 0;
  }
  stock(const stock& ) = delete;

  future<T>* get_free() {
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
    move_white_to_gray(current);
    return (reinterpret_cast<ext_n>(current));
  }

  /**
   * [oldx] should already be black (previously stored),
   *   it'll be set as ready (white) if it is not a fresh store.
   * [newx] will be set as stored and marked as a fresh store.
   *   it must be alive: either black or gray.
   * The freshness is reset by the tick function.
   */
  void store_in(ext_n ext_newx, ext_n ext_oldx) {
    n newx = reinterpret_cast<n>(ext_newx);
    n oldx = reinterpret_cast<n>(ext_oldx);
    if (newx->flag == Flag::unset) // It is gray
      move_to_black(grays, newx);
    else
      {} // It is already black
    if (oldx->flag == Flag::fresh)
      {} //It should stay black
    else
      move_black_to_white(oldx);
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
    do current->flag = Flag::old;
    while((current = current->next) != blacks);
  }

  void print_all() {
    printf("white : ");
    print_list(whites);
    printf(" black : ");
    print_list(blacks);
    printf(" gray : ");
    print_list(grays);
    printf("\n");
    fflush(stdout);
  }
  void print_list(n q) {
    if (q) {
      n c = q;
      printf("[ %d", c->v.get());
      c = c->next;
      while(c != q) {
        printf(", %d", c->v.get());
        c = c->next;
      }
      printf(" ]");
      fflush(stdout);
    }
    else printf("[]");
  }
  void test() {
    print_all();
    move_all(whites,grays);
    print_all();
    move_all(grays,whites);
    print_all();
    move_to_tail(whites,whites->next,blacks);
    print_all();
    move_to_tail(whites,whites->prev,grays);
    print_all();
    move_to_tail(whites,whites,blacks);
    print_all();
    move_all(grays,blacks);
    print_all();
    move_all(blacks,whites);
    print_all();
  }



};



#endif /* STOCK_H_ */
