/* Definitions for LLVM Generation and Emission
   Copyright (C) 2003 Free Software Foundation, Inc.

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

/* This file defines functions which are exported by the LLVM code
   generation interfaces and are called by the generic compiler
   interfaces.
*/

#ifndef GCC_LLVM_OUT_H
#define GCC_LLVM_OUT_H

#include <stdio.h>

#define EMIT_LLVM 1
union tree_node;

/* EMIT_CODE_INCREMENTALLY - For debugging it is nice to emit structures as
   they are computed... */
#define EMIT_CODE_INCREMENTALLY 0

void llvm_init_codegen(void);

/* Open assembly code output file.  Do this even if -fsyntax-only is
   on, because then the driver will have provided the name of a
   temporary file or bit bucket for us.  NAME is the file specified on
   the command line, possibly NULL.  */
void llvm_init_asm_output(const char *Filename);

/* llvm_assemble_external - This function is called once for each external
 *  function and variable as they are used.
 */
void llvm_assemble_external(union tree_node *decl);

/* llvm_c_expand_body - Expand the specified function into LLVM code
   and emit it. */
void llvm_c_expand_body(union tree_node *);

void llvm_assemble_variable(union tree_node *);

void llvm_mark_variable_volatile(union tree_node*);

void llvm_emit_global_ctor_dtor(int isConstructor, union tree_node *fndecl,
                                int Priority);

void llvm_emit_final_program(const char *version);
void llvm_program_print(FILE *);

#if EMIT_LLVM
/* FIXME: We should eventually implement this for crtstuff.c! This is used for
   exception handling stuff... */
#undef CRT_CALL_STATIC_FUNCTION
#define CRT_CALL_STATIC_FUNCTION(SECTION_OP, FUNC)
#undef CRT_GET_RFIB_DATA
/* END of huge FIXME. */


/* Disable emission of aliases for C++ thunks! */
#undef ASM_OUTPUT_DEF
#undef ASM_OUTPUT_WEAK_ALIAS


#define LLVM_TODO() \
  do { \
    fprintf(stderr, "ERROR: Function %s:%d not implemented in LLVM yet!\n", \
            __FUNCTION__, __LINE__); \
    abort(); } while (0)

#define LLVM_TODO_TREE(TREE) \
  do { \
    fprintf(stderr, \
            "ERROR: In function %s:%d, tree not handled by LLVM yet!\n", \
            __FUNCTION__, __LINE__); \
    debug_tree(TREE); abort(); } while (0)

#define LLVM_SHOULD_NOT_CALL() \
 do {  \
  fprintf(stderr, \
	  "ERROR: function %s should not be called when compiling to LLVM!\n",\
	  __FUNCTION__); \
  abort(); } while (0)
#else
#define LLVM_TODO()
#define LLVM_TODO_TREE(TREE)
#define LLVM_SHOULD_NOT_CALL()
#endif


#endif /* GCC_LLVM_OUT_H */
