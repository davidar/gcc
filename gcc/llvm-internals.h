/* Functions used internal to the LLVM emission phase
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

/* This file defines functions which are use by the LLVM code
   generation phases, but are private to it.
*/

#ifndef GCC_LLVM_INTERNALS_H
#define GCC_LLVM_INTERNALS_H

#include "llvm-out.h"

extern FILE *llvm_out_file;

struct llvm_function;
struct llvm_value;
struct llvm_type;
union tree_node;

/* Initialize the function, adding arguments to the function as
   appropriate.  Set up parameters and prepare for return, for the
   function.  */
struct llvm_function *llvm_expand_function_start(union tree_node *, int);

/* Expand a call to __main at the beginning of a possible main function.  */
void llvm_expand_main_function(struct llvm_function*);


/* Generate LLVM for the statement T, its substatements, and any other
   statements at its nesting level.  */
void llvm_expand_stmt(struct llvm_function*, union tree_node *);
struct llvm_value *llvm_expand_expr(struct llvm_function *, union tree_node*,
                                    struct llvm_value *);

/* llvm_expand_lvalue_expr: generate code for computing the address of EXP.  An
 * llvm_value* for the computed L-value is returned.  This is only legal to call
 * on lvalue expression trees.  If Fn is null, this means we are trying to
 * generate a constant lvalue expression to initialize a global variable.
 *
 * If the expression is not a bitfield, then the *BITSTART and *BITSIZE members
 * are set to 0, if the pointers are not null.
 *
 * If the address does specify a bitfield, then the lvalue gets as close to the
 * bitfield as possible, and fills in the *BITSTART & *BITSIZE fields with the
 * number of bits from the start of the returned pointer the bitfield is, and
 * the size of the bitfield, both in bits.  If the pointers are null, that is an
 * error.
 */
struct llvm_value *llvm_expand_lvalue_expr(struct llvm_function *Fn,
                                           union tree_node *exp,
                                           unsigned *BitStart,
                                           unsigned *BitSize);


void llvm_expand_function_end(struct llvm_function *Fn, union tree_node *subr,
                              int end_bindings);

/* Emit the current LLVM function to the specified file */
void llvm_function_print(struct llvm_function*, FILE*);

void llvm_function_delete(struct llvm_function*);

/* llvm_InitializeTypeSystem - Initialize the type system before any
   requests are made */
void llvm_InitializeTypeSystem(void);
void llvm_InitializeConstants(void);
void llvm_InitializeProgram(void);

/* Reset the identifier rename table now that we are out of function scope */
void ResetIdentifierTableForEndOfFunction(void);

void MarkNameAsUsed(const char *);

struct llvm_value *llvm_get_empty_class_pointer(struct llvm_function *Fn,
                                                union tree_node *type);

/* Exception handling expansion interfaces: These correspond with those in
   except.h */
void llvm_emit_code_for_throw(struct llvm_function *Fn);
void llvm_expand_eh_region_start(struct llvm_function *Fn);
void llvm_expand_eh_region_end_cleanup(struct llvm_function *Fn,
                                       union tree_node *handler);
void llvm_expand_eh_region_end_must_not_throw(struct llvm_function *Fn,
                                              union tree_node *action);
void llvm_expand_catch_block(struct llvm_function *Fn, union tree_node *Hndlrs);
void llvm_expand_eh_spec(struct llvm_function *Fn, union tree_node *TypeList);

void llvm_emit_call_to_llvmunwind(struct llvm_function *Fn);

#endif /* GCC_LLVM_INTERNALS_H */
