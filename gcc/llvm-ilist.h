/* Definition of generic linked list structure
   Copyright (C) 2003 Free Software Foundation, Inc.
   Contributed by: Chris Lattner

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free
Software Foundation; either version 2, or (at your option) any later
version.

GCC is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING.  If not, write to the Free
Software Foundation, 59 Temple Place - Suite 330, Boston, MA
02111-1307, USA.  */

/* This file defines a generic 'intrusive' doubly linked list
   structure.  It assumes that the element nodes each contain a Next
   and Prev element which can be used by the linked list.

   The linked list itself consists of a First and Last pointer (with a
   prefix), and the linked list is formed with a dummy node at the end
   which is distinguished by the fact that it has a "Next" field of null.
*/

#ifndef GCC_LLVM_ILIST_H
#define GCC_LLVM_ILIST_H

#include "libiberty.h"
#include <stdlib.h>

/* llvm_ilist - Define a new instance of an intrusive list */
#define llvm_ilist(TYPE, NAME) \
  TYPE *NAME##First, *NAME##Last

/* llvm_ilist_node - Define the intrusive part which goes into the
   nodes of the list */
#define llvm_ilist_node(TYPE, NAME) \
 TYPE *Prev, *Next

/* llvm_ilist_construct - Initialize a new linked list */
#define llvm_ilist_construct(TYPE, LIST) do {\
  LIST##First = LIST##Last = (TYPE*)xcalloc(sizeof(TYPE), 1); \
} while (0)



#define llvm_ilist_begin(LIST) LIST##First
#define llvm_ilist_end(LIST) LIST##Last

/* llvm_ilist_empty - Return true if the list is empty */
#define llvm_ilist_empty(TYPE, LIST) \
  (LIST##First == LIST##Last)

/* llvm_ilist_inlist - Given an object which lives in an ilist, return true if
   it lives in a list, falst if it has not yet been inserted. */
#define llvm_ilist_inlist(OBJECT) \
  ((OBJECT)->Next != 0)


/* llvm_ilist_foreach - Iterate over the list, executing the specified
   method on each element of the list.  The function must only take a
   pointer to a node */
#define llvm_ilist_foreach(TYPE, LIST, FN) do {\
  TYPE *XXCur = LIST##First;            \
  while (XXCur->Next) {                 \
    TYPE *XXNext = XXCur->Next;         \
    FN(XXCur);                          \
    XXCur = XXNext;                     \
  }                                     \
} while (0)


/* llvm_ilist_clear - Delete all elements in the list */
#define llvm_ilist_clear(TYPE, LIST) do {        \
  llvm_ilist_foreach(TYPE, LIST, TYPE##_delete); \
  LIST##First = LIST##Last;                      \
} while (0)

/* llvm_ilist_destruct - Destroy the entire list */
#define llvm_ilist_destruct(TYPE, LIST) do {                     \
  llvm_ilist_clear(TYPE, LIST);                                  \
  free(LIST##First);   /* The last node is not constructed */    \
} while (0)


/* llvm_ilist_back - Return the last element in the list */
#define llvm_ilist_back(TYPE, LIST)                \
  (assert(!llvm_ilist_empty(TYPE, LIST) &&"Cannot access back of empty list!"),\
   LIST##Last->Prev)

/* llvm_ilist_insert - Insert the specified value into the linked list before
   the specified insertion point. */
#define llvm_ilist_insert(TYPE, LIST, INSERTPOINT, NODE) do {              \
  TYPE *XXInsertPoint = INSERTPOINT, *XXNode = NODE;                       \
  assert(XXInsertPoint && !llvm_ilist_inlist(XXNode) && "Bad insertion!"); \
  XXNode->Next = XXInsertPoint; XXNode->Prev = XXInsertPoint->Prev;        \
  *(XXNode->Prev ? &XXNode->Prev->Next : &LIST##First) = XXNode;           \
  XXInsertPoint->Prev = XXNode;                                            \
} while (0)

/* llvm_ilist_push_back - Add a preallocated node to the end of the list */
#define llvm_ilist_push_back(TYPE, LIST, NODE) \
  llvm_ilist_insert(TYPE, LIST, llvm_ilist_end(LIST), NODE)

/* llvm_ilist_pop_back - Remove the last node from the end of the list, but do
   not deallocate it. */
#define llvm_ilist_pop_back(TYPE, LIST) do {                                \
  TYPE *XXNode = llvm_ilist_back(TYPE, LIST);   /* The end of the list */   \
  *(XXNode->Prev ? &XXNode->Prev->Next : &LIST##First) = LIST##Last;        \
  LIST##Last->Prev = XXNode->Prev;              /* Remove from end()   */   \
  XXNode->Next = XXNode->Prev = 0;              /* Remove node from list */ \
} while (0)

/* llvm_ilist_push_front - Add a preallocated node to the front of the list */
#define llvm_ilist_push_front(TYPE, LIST, NODE) do {              \
  TYPE *XXNode = NODE;                                            \
  assert(!llvm_inlist(XXNode) && "node already in list!");        \
  XXNode->Next = LIST##First; XXNode->Prev = 0;                   \
  LIST##First->Prev = XXNode;                                     \
  LIST##First = XXNode;                                           \
} while (0)

/* llvm_ilist_foreach1 - Iterate over the list, executing the
   specified method on each element of the list.  The function must
   take a pointer to a node and one additional argument */
#define llvm_ilist_foreach1(TYPE, LIST, FN, ARG) do {\
  TYPE *XXCur = LIST##First, *XXEnd = LIST##Last; \
  while (XXCur != XXEnd) {              \
    TYPE *XXNext = XXCur->Next;         \
    FN(XXCur, ARG);                     \
    XXCur = XXNext;                     \
  }                                     \
} while (0)


/* llvm_ilist_foreach1 - Iterate over the list, executing the
   specified method on each element of the list.  The function must
   take a pointer to a node and two additional arguments */
#define llvm_ilist_foreach2(TYPE, LIST, FN, ARG1, ARG2) do {\
  TYPE *XXCur = LIST##First, *XXEnd = LIST##Last; \
  while (XXCur != XXEnd) {              \
    TYPE *XXNext = XXCur->Next;         \
    FN(XXCur, ARG1, ARG2);              \
    XXCur = XXNext;                     \
  }                                     \
} while (0)

/* llvm_ilist_foreach3 - Iterate over the list, executing the
   specified method on each element of the list.  The function must
   take a pointer to a node and three additional arguments */
#define llvm_ilist_foreach3(TYPE, LIST, FN, ARG1, ARG2, ARG3) do {\
  TYPE *XXCur = LIST##First, *XXEnd = LIST##Last; \
  while (XXCur != XXEnd) {              \
    TYPE *XXNext = XXCur->Next;         \
    FN(XXCur, ARG1, ARG2, ARG3);        \
    XXCur = XXNext;                     \
  }                                     \
} while (0)

#define llvm_ilist_front(TYPE, LIST)                \
  (assert(LIST##First != LIST##Last && "ilist::front: list is empty!"), \
   LIST##First)

/* Remove the nodes specified by the range [FIRST, LAST) from OLDLIST (the list
   they are currently in) and reinsert them before the object specified by POS
   in list NEWLIST.  Note that OLDLIST AND NEWLIST may be entirely different
   lists.  This is a constant time operation.
*/
#define llvm_ilist_splice(TYPE, NEWLIST, POS, OLDLIST, FIRST, LAST) do { \
  TYPE *XXPos = POS, *XXFirst = FIRST, *XXLast = LAST;                   \
  if (XXFirst != XXLast && /* Not splicing empty list fragment? */       \
      XXPos != XXFirst) {  /* Not splicing to the same place? */         \
    TYPE *XXLastPrev = XXLast->Prev;                                     \
    /* Unsplice the [First,Last) fragment from original pos */           \
    *(XXFirst->Prev ? &XXFirst->Prev->Next : &OLDLIST##First) = XXLast;  \
    XXLast->Prev = XXFirst->Prev;                                        \
    /* Update the ends of [First,LastPrev] */                            \
    XXFirst->Prev = XXPos->Prev; XXLastPrev->Next = XXPos;               \
    /* Splice the [First,LastPrev] fragment into the new position */     \
    *(XXPos->Prev ? &XXPos->Prev->Next : &NEWLIST##First) = XXFirst;     \
    XXPos->Prev = XXLastPrev;                                            \
  } \
} while (0)

/* llvm_ilist_prev - Return the previous node in the linked list, or null if off
   the end */
#define llvm_ilist_prev(NODE) \
  (assert((NODE) && "Cannot return prev(begin())!"),  \
   (NODE)->Prev)

/* llvm_ilist_next - Return the next node in the linked list, or null if off the
   end */
#define llvm_ilist_next(NODE) \
  (assert((NODE)->Next && "Cannot return next(end())!"),  \
   (NODE)->Next->Next ? (NODE)->Next : 0)


#endif

