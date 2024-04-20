/* The main tree to LLVM conversion implementation
   Copyright (C) 2003 Free Software Foundation, Inc.
   Contributed by Chris Lattner

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

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tm.h"
#include "intl.h"
#include "tree.h"
#include "tree-inline.h"
#include "flags.h"
#include "c-tree.h"
#include "toplev.h"
#include "ggc.h"
#include "tm_p.h"
#include "target.h"
#include "c-common.h"
#include "real.h"
#include "langhooks.h"
#include "output.h"
#include "except.h"
#include "diagnostic.h"
#include "llvm-internals.h"
#include "llvm-representation.h"
#include <assert.h>
#include <ctype.h>

static llvm_value *llvm_expand_assignment(llvm_function *Fn, tree to,tree from,
                                          llvm_value **Val);
static void llvm_expand_constructor(llvm_function *Fn, tree exp,
                                    llvm_value *Dest, int isVolatile);
static void llvm_expand_goto_internal(llvm_function *Fn, tree body,
                                      llvm_basicblock *label,
                                      int CleanupsCanThrow,
                                      int isExceptionEdge);
static llvm_constant *llvm_expand_constant_expr(tree exp, llvm_type *ReqType);
static llvm_constant *llvm_decode_string_constant(tree exp, unsigned Len,
                                                  llvm_type *ElTy);
static llvm_function *CreateIntrinsicFunction(const char *Name, tree FnType);
static llvm_function *CreateIntrinsicFnWithType(const char *Nam, llvm_type *Ty);

/*===----------------------------------------------------------------------===**
              ... Helper functions for Instruction Emission ...
 *===----------------------------------------------------------------------===*/

/* append_inst - Given an instruction, make it available at the end of the
 * specified function.  This function is a little bit smarter than it first
 * appears, however:
 *
 * If the specified instruction operates solely on constant operands (and no
 * side-effects), promote the instruction to be a ConstantExpr instruction,
 * which is evaluated at compile time, not runtime.  This is not strictly an
 * optimization: global values may have cast or getelementptr instruction in
 * their initializers, and they don't have a function to emit code into, thus,
 * this is a required transformation for these cases (when Fn is null).
 */
static llvm_value *append_inst(llvm_function *Fn, llvm_instruction *I) {
  llvm_basicblock *BB;

  /* If the instruction allows the ConstantExpr optimization... */
  if (I->Opcode == O_Cast || I->Opcode == O_GetElementPtr ||
      I->Opcode == O_Add || I->Opcode == O_Sub ||
      /* And, Or, and Shl are used for bitfield struct inits */
      I->Opcode == O_And || I->Opcode == O_Or || I->Opcode == O_Shl) {
    int AllOperandsConstant = 1;  /* Scan for non-constant operands */
    unsigned i;

    if (I->Opcode == O_Shl || I->Opcode == O_Shr) {
      assert(llvm_type_is_integral(I->Operands[0]->Ty) &&
             I->Operands[0]->Ty != BoolTy);
    }

    for (i = 0; i != I->NumOperands; ++i)
      if (!llvm_value_is_constant(I->Operands[i])) {
        AllOperandsConstant = 0;
        break;
      }
    if (AllOperandsConstant)  /* Safe opcode, safe operands. */
      return G2V(llvm_constant_expr_new(I));   /* Return a new constant_expr. */
  }

  BB = llvm_ilist_back(llvm_basicblock, Fn->BasicBlocks);
  llvm_ilist_push_back(llvm_instruction, BB->Instructions, I);
  return D2V(I);
}

/* insert_alloca_into_entry_block - Used to insert fixed sized alloca
   instructions into a function */
static void insert_alloca_into_entry_block(llvm_function *Fn,
                                           llvm_instruction *I) {
  llvm_basicblock *BB = llvm_ilist_front(llvm_basicblock, Fn->BasicBlocks);
  llvm_instruction *InsertPoint = llvm_ilist_begin(BB->Instructions);
  llvm_instruction *End = llvm_ilist_end(BB->Instructions);

  assert(I->Opcode == O_Alloca &&
         "Cannot insert non-alloca insts with this function");

  /* FIXME: This can cause N^2 behavior if inserting tons of allocas.  It would
   * be much better to add a "last alloca inserted" member to the ExpandInfo
   * structure for the current function.
   */

  /* Find the first non-alloca instruction */
  while (InsertPoint != End && InsertPoint->Opcode == O_Alloca)
    InsertPoint = InsertPoint->Next;
  
  /* Insert the new alloca instruction before the first non-alloca
   * instruction.
   */
  llvm_ilist_insert(llvm_instruction, BB->Instructions, InsertPoint, I);
}

static inline llvm_instruction *make_temporary_alloca(llvm_function *Fn,
                                                      llvm_type *ArgTy) {
  llvm_instruction *I =
    create_alloca_inst("mem_tmp", ArgTy, llvm_constant_uint_1);
  insert_alloca_into_entry_block(Fn, I);
  return I;
}

static inline llvm_value *cast_if_type_not_equal(llvm_function *Fn,
                                                 llvm_value *V, llvm_type *Ty) {
  llvm_instruction *Cast;
  if (V->Ty == Ty) return V;  /* No cast required? */

  assert(llvm_type_is_scalar(Ty) && "Cannot cast to non-first-class type!");
  assert(Ty != VoidTy && "Cannot cast value to void!");

  /* If we are casting bool to something, then back to bool, eliminate the two
   * casts.
   */
  if (V->VTy == Instruction && Ty->ID == BoolTyID) {
    llvm_instruction *I = (llvm_instruction *)V;
    if (I->Opcode == O_Cast && I->Operands[0]->Ty->ID == BoolTyID)
      return I->Operands[0];
  }

  /* If we are casting a pointer to a struct S1 to be a pointer to some other
   * pointer to type T2, and the first nested element of S1 is T2, insert a
   * getelementptr instruction instead of a cast instruction!
   */
  if (V->Ty->ID == PointerTyID && Ty->ID == PointerTyID &&
      llvm_type_is_composite(GET_POINTER_TYPE_ELEMENT(V->Ty))) {
    unsigned Depth = 0;
    llvm_type *STy = GET_POINTER_TYPE_ELEMENT(V->Ty);
    llvm_type *DTy = GET_POINTER_TYPE_ELEMENT(Ty);

    for (; STy != DTy && llvm_type_is_composite(STy); ++Depth)
      STy = STy->Elements[0];

    /* If we find a match, form a getelementptr instruction! */
    if (STy == DTy) {
      llvm_instruction *GEP = llvm_instruction_new(Ty, "tmp", O_GetElementPtr,
                                                   2+Depth);
      GEP->Operands[0] = V;
      GEP->Operands[1] = llvm_constant_long_0;
      STy = GET_POINTER_TYPE_ELEMENT(V->Ty);

      for (Depth = 2; STy != DTy; STy = STy->Elements[0])
        if (STy->ID == StructTyID)
          GEP->Operands[Depth++] = llvm_constant_ubyte_0;
        else
          GEP->Operands[Depth++] = llvm_constant_long_0;
      return append_inst(Fn, GEP);
    }
  }

  /* Constant fold some simple, but common, constants */
  if (V->VTy == Constant) {
    if (V2C(V)->Repr[0] == '0' && V2C(V)->Repr[1] == 0) {
      return llvm_constant_get_null(Ty);   /* At least handle the 0 case now */
    } else if (Ty == LongTy) {              /* Common array idx cases */
      if (V->Ty == UIntTy || V->Ty == IntTy)
        return llvm_constant_new(Ty, V2C(V)->Repr);
    }
  }

  Cast = llvm_instruction_new(Ty, "tmp", O_Cast, 1);
  Cast->Operands[0] = V;
  return append_inst(Fn, Cast);
}

/* llvm_zero_initialize - Emit code to zero initialize the memory pointed to by
   Dest, generating code using the type of Dest.
 */
static void llvm_zero_initialize(llvm_function *Fn, llvm_value *Dest) {
  llvm_type *ElTy = GET_POINTER_TYPE_ELEMENT(Dest->Ty);
  if (llvm_type_is_scalar(ElTy)) {
    append_inst(Fn, create_store_inst(llvm_constant_get_null(ElTy), Dest, 0));
  } else if (ElTy->ID == StructTyID) {
    unsigned i;
    for (i = 0; i != ElTy->NumElements; ++i) {
      llvm_instruction *OffsetInst = create_gep3(Dest, llvm_constant_long_0,
                                       llvm_constant_new_integral(UByteTy, i));
      llvm_zero_initialize(Fn, append_inst(Fn, OffsetInst));
    }
    
  } else if (ElTy->ID == ArrayTyID) {
    unsigned i;
    for (i = 0; i != GET_ARRAY_TYPE_SIZE(ElTy); ++i) {
      llvm_instruction *OffsetInst = 
        create_gep3(Dest, llvm_constant_long_0,
                    llvm_constant_new_integral(LongTy, i));
      llvm_zero_initialize(Fn, append_inst(Fn, OffsetInst));
    }
    
  } else {
    assert(0 && "Cannot zero initialize this type!");
    abort();
  }
}

static llvm_value *llvm_get_scalar_vararg(llvm_function *Fn,
                                          llvm_value *VAListPtr,
                                          llvm_type *ArgTy) {
  llvm_value *VAList = append_inst(Fn, create_load_inst("valist", VAListPtr,0));
  llvm_value *Result;
  llvm_instruction *VA = llvm_instruction_new(ArgTy, "tmp", O_VAArg, 1);

  assert(llvm_type_is_scalar(ArgTy) && "Not a scalar type?");

  VA->Operands[0] = VAList;
  Result = append_inst(Fn, VA);
  
  /* Update the valist */
  VA = llvm_instruction_new(VAList->Ty, "vanextlist", O_VANext, 1);
  VA->Operands[0] = VAList;
  VA->x.VANext.ArgTy = ArgTy;
  VAList = append_inst(Fn, VA);
  
  append_inst(Fn, create_store_inst(VAList, VAListPtr, 0));
  return Result;
}

/* llvm_get_composite_vararg - Emit a series of va_arg instructions that are
 * used to initialize the specified lvalue.
 */
static void llvm_get_composite_vararg(llvm_function *Fn, llvm_value *VAList,
                                      llvm_value *Dest) {
  llvm_type *ElTy = GET_POINTER_TYPE_ELEMENT(Dest->Ty);
  if (llvm_type_is_scalar(ElTy)) {
    llvm_type *PromotedElTy = llvm_type_get_promoted_type(ElTy);
    llvm_value *Val = llvm_get_scalar_vararg(Fn, VAList, PromotedElTy);
    Val = cast_if_type_not_equal(Fn, Val, ElTy);
    append_inst(Fn, create_store_inst(Val, Dest, 0));
  } else if (ElTy->ID == StructTyID) {
    unsigned i;
    for (i = 0; i != ElTy->NumElements; ++i) {
      llvm_instruction *OffsetInst =
        create_gep3(Dest, llvm_constant_long_0,
                    llvm_constant_new_integral(UByteTy, i));
      llvm_get_composite_vararg(Fn, VAList, append_inst(Fn, OffsetInst));
    }
    
  } else if (ElTy->ID == ArrayTyID) {
    unsigned i;
    for (i = 0; i != GET_ARRAY_TYPE_SIZE(ElTy); ++i) {
      llvm_instruction *OffsetInst = 
        create_gep3(Dest, llvm_constant_long_0,
                    llvm_constant_new_integral(LongTy, i));
      llvm_get_composite_vararg(Fn, VAList, append_inst(Fn, OffsetInst));
    }
    
  } else {
    assert(0 && "Cannot va_arg this type!");
    abort();
  }
}

/* FunctionEndUnreachable - Return true if we are sure that the current position
   in the emitting basic block is unreachable.  If this is true, there is no
   reason to append instructions.
*/
static int EndOfFunctionUnreachable(llvm_function *Fn) {
  llvm_basicblock *BB = llvm_ilist_back(llvm_basicblock, Fn->BasicBlocks);
  if (llvm_ilist_empty(llvm_instruction, BB->Instructions)) {
    return false;  /* No instructions yet, may be unreachable! */
  } else {
    llvm_instruction *Inst =llvm_ilist_back(llvm_instruction, BB->Instructions);
    return llvm_instruction_is_terminator(Inst);
  }
}

static void llvm_emit_label(llvm_function *Fn, llvm_basicblock *BB) {
  /* Emit a branch from the current block to the new block */
  if (!EndOfFunctionUnreachable(Fn))
    append_inst(Fn, create_uncond_branch(BB));
  
  /* add the new basic block to the function */
  llvm_ilist_push_back(llvm_basicblock, Fn->BasicBlocks, BB);
}

/* llvm_copy_aggregate - Given two pointers to structures, copy *SrcPtr into
 * *DestPtr, element by element.
 *
 * FIXME: for objects of non-trivial complexity, we could instead call a
 * "assignment" function to perform the copy.  This could save a lot of code
 * space.  We would have to mark the generated function as linkonce.
 */
static void llvm_copy_aggregate(llvm_function *Fn, llvm_value *DestPtr,
                                llvm_value *SrcPtr, int isSourceVolatile,
                                int isDestVolatile) {
  llvm_type *ObjTy;
  unsigned i;
  assert(DestPtr && SrcPtr && "Cannot copy from null ptr!");
  assert(DestPtr->Ty == SrcPtr->Ty && "Cannot copy incompatible structs!");
  if (DestPtr == SrcPtr) return;  /* X = X;   -->  Noop */

  /* Get the type of the object being copied... */
  ObjTy = GET_POINTER_TYPE_ELEMENT(DestPtr->Ty);

  /* Copy scalar values by emitting a load then store. */
  if (llvm_type_is_scalar(ObjTy)) {
    llvm_value *Val =
      append_inst(Fn, create_load_inst("tmp", SrcPtr, isSourceVolatile));
    append_inst(Fn, create_store_inst(Val, DestPtr, isDestVolatile));
    return;
  }

  /* Copy aggregate values recursively... */
  switch (ObjTy->ID) {
  case StructTyID:
    for (i = 0; i < ObjTy->NumElements; ++i) {
      llvm_value *FieldNo = llvm_constant_new_integral(UByteTy, i);
      llvm_value *DestElPtr = append_inst(Fn, create_gep3(DestPtr,
                                                llvm_constant_long_0, FieldNo));
      llvm_value *SrcElPtr = append_inst(Fn, create_gep3(SrcPtr,
                                                llvm_constant_long_0, FieldNo));
      
      llvm_copy_aggregate(Fn, DestElPtr, SrcElPtr,
                          isSourceVolatile, isDestVolatile);
    }
    break;

  case ArrayTyID: {
    for (i = 0; i < GET_ARRAY_TYPE_SIZE(ObjTy); ++i) {
      llvm_value *FieldNo = llvm_constant_new_integral(LongTy, i);
      llvm_value *DestElPtr = append_inst(Fn, create_gep3(DestPtr,
                                                llvm_constant_long_0, FieldNo));
      llvm_value *SrcElPtr = append_inst(Fn, create_gep3(SrcPtr,
                                                llvm_constant_long_0, FieldNo));
      llvm_copy_aggregate(Fn, DestElPtr, SrcElPtr,
                          isSourceVolatile, isDestVolatile);
    }
    break;
  }
  default:
    fprintf(stderr, "Cannot copy this value:\n");
    llvm_value_dump_operand(SrcPtr);
    abort();
  }
}


/*===----------------------------------------------------------------------===**
                    ... Scope Nesting Implementation ...
 *===----------------------------------------------------------------------===*/

/* Stack of control and binding constructs we are currently inside.

   These constructs begin when you call `llvm_expand_start_WHATEVER' and end
   when you call `llvm_expand_end_WHATEVER'.  This stack records info about how
   the construct began that tells the end-function what to do.  It also may
   provide information about the construct to alter the behavior of other
   constructs within the body.  For example, they affect the behavior of C
   `break' and `continue'.

   Each construct gets one `struct llvm_nesting' object.  All of these objects
   are chained through the `all' field.  `nesting_stack' points to the first
   object (innermost construct).

   Each type of construct has its own individual stack.  For example, loops have
   `loop_stack'.  Each object points to the next object of the same type through
   the `next' field.

   Some constructs are visible to `break' exit-statements and others are not.
   Which constructs are visible depends on the language.  Therefore, the data
   structure allows each construct to be visible or not, according to the args
   given when the construct is started.  The construct is visible if the
   `exit_block' field is non-null.

   FIXME FIXME FIXME FIXME FIXME FIXME FIXME FIXME FIXME FIXME FIXME FIXME 

     This is not a garbage collected structure.  As such, the garbage collector
     won't use it to calculate roots for reachable objects.  This would be ok,
     except that some objects (like the cleanups list) are dynamically allocated
     tree nodes that may cause garbage collection to happen.

     The fix is to either not use a TREE LIST to represent these cleanups, or to
     tell the GC about the roots.

   FIXME FIXME FIXME FIXME FIXME FIXME FIXME FIXME FIXME FIXME FIXME FIXME 
*/

typedef struct llvm_nesting {
  struct llvm_nesting *all;        /* Next innermost scope of any type */
  struct llvm_nesting *next;       /* Next innermost scope of current type */
  llvm_basicblock *exit_block;     /* Exit block for break statements */
  int BreakFound;                  /* Has exit_block been used?? */

  enum nesting_desc {
    COND_NESTING,
    LOOP_NESTING,
    BLOCK_NESTING,
    EXCEPT_NESTING,
    CASE_NESTING
  } desc;

  union {
    /* For conds (if-then and if-then-else statements).  */
    struct nesting_cond {
      /* Block for the end of this alternative.  This may be the end of the if
         or the next else/elseif.  */
      llvm_basicblock *next_block;

      /* Block for the end of the if statement.  This is lazily set so that just
         plain if expressions (with no else) don't get an extra block. */
      llvm_basicblock *exit_block;
    } cond;

    /* for, while, and do loops.  */
    struct nesting_loop {
      /* Label at the top of the loop; place to loop back to.  */
      llvm_basicblock *start_label;
      /* Label at the end of the whole construct.  */
      llvm_basicblock *end_label;
      /* Label for `continue' statement to jump to; this is in front of the
         stepper of the loop.  */
      llvm_basicblock *continue_label;

      /* keep track of whether a continue has been seen to avoid emitting
         extraneous labels */
      int ContinueFound;
    } loop;
    
    /* For variable binding contours.  */
    struct nesting_block {
      /* The basic block that this nesting level starts in */
      llvm_basicblock *StartBlock;

      /* List of cleanups to be run on exit from this contour.  This is a list
	 of expressions to be evaluated.  The TREE_PURPOSE of each link is the
	 ..._DECL node which the cleanup pertains to.  */
      tree cleanups;
    } block;

    /* For exception handling levels (try blocks and friends) */
    struct except_block {
      /* The basic block that is activated if an exception is thrown */
      llvm_basicblock *CatchBlock;

      /* The basic block that is used to continue excecution AFTER the try
         block */
      llvm_basicblock *OutBlock;

      /* This is set to true if the body of the exception block contains an
         exception throwing event, which requires the catch portion to be
         emitted */
      int Used;
    } except;

    /* For switch (C) or case (Pascal) statements. */
    struct case_block {
      /* The switch instruction itself. */
      llvm_instruction *SwitchInst;

      /* Name of this kind of statement, for warnings.  */
      const char *printname;
    } switchblock;
  } x;
} llvm_nesting;


/* In some cases it is impossible to generate code for a forward goto until the
   label definition is seen.  This happens when it may be necessary for the goto
   to emit cleanups: we don't know which cleanups to run because we don't know
   at what level the destination label is w.r.t the source goto.
   llvm_expand_goto_internal puts an entry on this fixup list for each
   appropriate goto, and every time a binding contour that adds cleanups is
   exited, we check the appropriate fixups.  If the target label has now been
   defined, we can insert the proper code.
*/

typedef struct llvm_goto_fixup {
  /* Points to following fixup.  */
  struct llvm_goto_fixup *next;

  /* Points to the jump instruction itself.  If more code must be inserted, it
     goes before this instruction.  */
  llvm_basicblock  *BranchBlock;
  llvm_instruction *BranchInst;

  /* The LLVM basic block that this is jumping to.  */
  llvm_basicblock *target_bb;

  /* Information about what happens if a cleanup expression throws an exception.
     See llvm_expand_goto_internal for information about this flag. */
  int CleanupsCanThrow;

  /* Information about whether this goto is part of an exception propagation.
   * If so, cleanups which are only supposed to be run on exception exits are
   * expanded.
   */
  int isExceptionEdge;

  /* List of cleanup expressions to be run by this goto in the current block.
   * This list ONLY includes cleanups in the current block: when the current
   * block is exited (assuming the destination label hasn't been seen), all of
   * these cleanups will be inserted before the branch instruction, and this
   * cleanup_list will be updated to include all of the cleanups seen so far in
   * the containing block.
   *
   * When a label is finally emitted, the fixup entry is deleted and cleanups
   * are no longer expanded for it.
   */
  tree cleanup_list;
  llvm_nesting *containing_block;
} llvm_goto_fixup;


/* llvm_tree_list - A non-garbage collected list of tree pointers */
typedef struct llvm_tree_list {
  struct llvm_tree_list *Next;
  tree Value;
} llvm_tree_list;

static void llvm_tree_list_free(llvm_tree_list *L) {
  if (L == 0) return;
  llvm_tree_list_free(L->Next);
  free(L);
}

static void llvm_tree_list_push_front(llvm_tree_list **L, tree V) {
  llvm_tree_list *NewLink = (llvm_tree_list*)xcalloc(sizeof(llvm_tree_list), 1);
  NewLink->Value = V;
  NewLink->Next = *L;
  *L = NewLink;
}


typedef struct llvm_expand_info {
  llvm_basicblock *CleanupBlock;        /* Block that executes param cleanups */
  llvm_basicblock *ReturnBlock;         /* Block which returns from function */
  llvm_basicblock *RethrowBlock;        /* Block which rethrows current except*/
  llvm_basicblock *TerminateBlock;      /* Block which calls terminate */

  llvm_nesting *InnermostScope;         /* The innermost of any scope */
  llvm_nesting *InnermostCondScope;     /* The innermost if scope */
  llvm_nesting *InnermostLoopScope;     /* The innermost loop scope */
  llvm_nesting *InnermostBlockScope;    /* The innermost BLOCK scope */
  llvm_nesting *InnermostCaseScope;     /* The innermost switch statement */
  llvm_nesting *InnermostExceptScope;   /* The innermost exception scope */

  llvm_goto_fixup *GotoFixupList;       /* Gotos needing cleanup fixups */
  llvm_value *last_expr_value;          /* used to implement EXPR_STMTS */
  llvm_value *last_expr_value_location; /* used to implement EXPR_STMTS */

  /* ThrownExceptionsCallTerminate - If this flag is set to true, any exceptions
   * throws expanded (or invoke destinations used) should branch to the
   * TerminateBlock instead of throwing the exception.
   */
  int ThrownExceptionsCallTerminate;

  /* CurrentBlockScope - If this is set, it overrides the top of the block scope
   * stack as the value to use for the current cleanups to execute.  See the
   * comment in the body of llvm_expand_goto_internal for an explanation of why
   * this is needed.
   */
  llvm_nesting *CurrentBlockScope;

} llvm_expand_info;

/* add_scope_stack - Allocate and add a scope to the top of the scope list, with
   the specified nesting_nesc type... */
static llvm_nesting *add_scope_stack(llvm_function *Fn,
                                     llvm_nesting **CurScopeList,
                                     enum nesting_desc ND) {
  llvm_nesting *NewScope = xcalloc(sizeof(llvm_nesting), 1);
  NewScope->desc = ND;
  NewScope->next = *CurScopeList;
  NewScope->all = Fn->ExpandInfo->InnermostScope;
  *CurScopeList = NewScope;
  Fn->ExpandInfo->InnermostScope = NewScope;
  return NewScope;
}

/* pop_scope_stack - Pop the current scope off of the stack and return it. */
static llvm_nesting *pop_scope_stack(llvm_function *Fn,
                                     llvm_nesting **CurScopeList) {
  llvm_nesting *CurScope = *CurScopeList;
  assert(Fn->ExpandInfo->InnermostScope == CurScope &&
	 "popping scopes in wrong order?");
  *CurScopeList = CurScope->next;
  Fn->ExpandInfo->InnermostScope = CurScope->all;
  return CurScope;
}

/* pop_and_free_scope_stack - Pop the current scope off of the stack and free
   it. */
static void pop_and_free_scope_stack(llvm_function *Fn,
                                     llvm_nesting **CurScopeList) {
  free(pop_scope_stack(Fn, CurScopeList));
}

/* Expand a list of cleanups LIST.  Elements may be expressions or may be nested
 * lists.  When expanding the list, we actually mutate the tree list pointer so
 * that if an expanded cleanup needs a cleanup itself, it will not reexpand a
 * cleanup for itself...
 */
static void llvm_expand_cleanups(llvm_function *Fn, tree *list,
                                 int isExceptionEdge) {
  tree OrigList = *list;
  while (*list) {
    tree CurCleanup = *list;
    *list = TREE_CHAIN(*list);    /* Destructively update cleanup list */

    if (TREE_CODE(TREE_VALUE(CurCleanup)) == TREE_LIST) {
      llvm_expand_cleanups(Fn, &TREE_VALUE(CurCleanup), isExceptionEdge);
    } else if (!CLEANUP_EH_ONLY(CurCleanup) || isExceptionEdge) {
      /* Cleanups may be run multiple times.  For example, when exiting a
       * binding contour, we expand the cleanups associated with that contour.
       * When a goto within that binding contour has a target outside that
       * contour, it will expand all cleanups from its scope to the target.
       * Though the cleanups are expanded multiple times, the control paths are
       * non-overlapping so the cleanups will not be executed twice.
       */
      llvm_expand_expr(Fn, TREE_VALUE(CurCleanup), 0);
    }
  }

  /* Restore input list to what it was when llvm_expand_cleanups was invoked */
  *list = OrigList;
}

/* When exiting a binding contour, process all pending gotos requiring fixups.
 * THISBLOCK is the structure that describes the block being exited.
 *
 * Gotos that jump out of this contour must execute any cleanups for this block
 * before actually jumping.
 */
static void llvm_fixup_gotos(llvm_function *Fn, llvm_nesting *thisblock) {
  /* F is the fixup we are considering; PREV is the previous one.  */
  llvm_goto_fixup *f, *prev = 0;
  llvm_nesting *NextBlockWithCleanups;
  
  /* Compute the next block that thisblock is contained in which has cleanups,
   * or null if there is none.
   */
  NextBlockWithCleanups = thisblock ? thisblock->next : 0;
  while (NextBlockWithCleanups && NextBlockWithCleanups->x.block.cleanups == 0)
    NextBlockWithCleanups = NextBlockWithCleanups->next;

  f = Fn->ExpandInfo->GotoFixupList;
  while (f) {
    if (!f->CleanupsCanThrow)
      Fn->ExpandInfo->ThrownExceptionsCallTerminate++;

    if (llvm_ilist_inlist(f->target_bb)) {       /* Block has been inserted? */
      /* We don't need to run any cleanups for the block that the label exists
       * in because we aren't exiting it!  Instead just remove the goto fixup.
       */
      llvm_goto_fixup *Next = f->next;

      /* Unlink this node in the fixup chain */
      *(prev ? &prev->next : &Fn->ExpandInfo->GotoFixupList) = Next;
      if (!f->CleanupsCanThrow)
        Fn->ExpandInfo->ThrownExceptionsCallTerminate--;
      free(f);
      f = Next;
      continue;  /* make sure not to skip a node in the list */
    } else if (f->containing_block == thisblock) {
      /* We will expand the cleanups into the end of the function and then
       * splice the block contents before the actual branch insn.  Remember
       * where the current end of the function is.
       */
      llvm_basicblock *LastBlock = llvm_ilist_back(llvm_basicblock,
                                                   Fn->BasicBlocks);
      llvm_instruction *LastInst = llvm_ilist_end(LastBlock->Instructions);
      llvm_instruction *End;

      LastInst = llvm_ilist_prev(LastInst);  /* work with empty BBs */

      /* Expand all of the cleanups that are appropriate when exiting this
         block */
      if (f->cleanup_list)
        llvm_expand_cleanups(Fn, &f->cleanup_list, f->isExceptionEdge);

      /* Now that we have expanded the appropriate code, move it from the end of
         the function to immediately before the goto in question. */
      if (LastInst)
        LastInst = llvm_ilist_next(LastInst);  /* Move the first inst to move */
      else if (!llvm_ilist_empty(llvm_instruction, LastBlock->Instructions))
        LastInst = llvm_ilist_begin(LastBlock->Instructions);
      if (LastInst) {
        /* If the cleanups expanded to SOMETHING, move the instructions from the
         * basic block where we expanded them, INTO the basic block that
         * contains the goto we are fixing up.
         */
        End = llvm_ilist_end(LastBlock->Instructions);
        llvm_ilist_splice(llvm_instruction, f->BranchBlock->Instructions,
                          f->BranchInst, LastBlock->Instructions, LastInst,End);
      }

      /* If the cleanups inserted new basic blocks into the function, we also
       * want to move the new basic blocks to be immediately after the goto
       * block.  Since we would have moved a terminator instruction right before
       * our goto, we also need to move the goto to the last of the new blocks.
       */
      if (LastBlock != llvm_ilist_back(llvm_basicblock, Fn->BasicBlocks)) {
        /* We inserted some new basic block(s).  Move our goto to the end of the
         * last block.
         */
        llvm_basicblock *NewLastBlock =
          llvm_ilist_back(llvm_basicblock, Fn->BasicBlocks);
        llvm_instruction *NewEnd = llvm_ilist_end(NewLastBlock->Instructions);
        End = llvm_ilist_end(f->BranchBlock->Instructions);
        llvm_ilist_splice(llvm_instruction, NewLastBlock->Instructions, NewEnd,
                          f->BranchBlock->Instructions, f->BranchInst, End);

        /* Now that the goto has been moved, move the inserted blocks as well */
        llvm_ilist_splice(llvm_basicblock, Fn->BasicBlocks,
                          llvm_ilist_next(f->BranchBlock), Fn->BasicBlocks,
                          llvm_ilist_next(LastBlock),
                          llvm_ilist_end(Fn->BasicBlocks));

        /* Update branch block now */
        f->BranchBlock = NewLastBlock;
      }

      /* Now that we have handled this binding level for the goto, update it to
         indicate the next binding level and cleanup list it needs to be
         concerned with */
      f->containing_block = NextBlockWithCleanups;
      f->cleanup_list     = NextBlockWithCleanups ?
                                   NextBlockWithCleanups->x.block.cleanups : 0;
    }
    if (!f->CleanupsCanThrow)
      Fn->ExpandInfo->ThrownExceptionsCallTerminate--;

    prev = f;
    f = f->next;
  }
}

/* Generate the LLVM code for entering a binding contour.  The variables are
 * declared one by one, by calls to `llvm_expand_decl'.
 */
static void llvm_expand_start_bindings(llvm_function *Fn) {
  /* Make an entry on block_stack for the block we are entering.  */
  llvm_nesting *thisblock = 
    add_scope_stack(Fn, &Fn->ExpandInfo->InnermostBlockScope, BLOCK_NESTING);

  thisblock->x.block.StartBlock = 
                   llvm_ilist_back(llvm_basicblock, Fn->BasicBlocks);
}

/* Generate LLVM code to terminate a binding contour.
 *
 * VARS is the chain of VAR_DECL nodes for the variables bound in this contour.
 * There may actually be other nodes in this chain, but any nodes other than
 * VAR_DECLS are ignored.
 */
static void llvm_expand_end_bindings(llvm_function *Fn, tree vars) {
  llvm_nesting *thisblock = Fn->ExpandInfo->InnermostBlockScope;

  /* If any of the variables in this scope were not used, warn the
     user.  */
  warn_about_unused_variables (vars);

#if 0   /* FIXME: implement nonlocal gotos */
  if (function_call_count != 0 && nonlocal_labels ...)
    expand_nl_goto_receivers (thisblock);
#endif

  /* Perform any cleanups associated with the block.  */
  if (thisblock->x.block.cleanups != 0) {
    if (!EndOfFunctionUnreachable(Fn)) {
      /* Don't let cleanups affect ({...}) constructs.  */
      llvm_value *old_last_expr_value = Fn->ExpandInfo->last_expr_value;

      /* Do the cleanups.  */
      llvm_expand_cleanups(Fn, &thisblock->x.block.cleanups, 0);

      /* Restore last expr value */
      Fn->ExpandInfo->last_expr_value = old_last_expr_value;
    }

    /* Any gotos out of this block must also do these things.  Also report any
       gotos with fixups that came to labels in this level.  */
    llvm_fixup_gotos(Fn, thisblock);
  }

  /* Pop the current scope off of the stack... */
  pop_and_free_scope_stack(Fn, &Fn->ExpandInfo->InnermostBlockScope);
}

/*===----------------------------------------------------------------------===**
              ... Exception Handling Expansion Implementation ...
 *===----------------------------------------------------------------------===*/

static tree llvm_last_cleanup_this_contour(llvm_function *Fn) {
  llvm_nesting *thisblock = Fn->ExpandInfo->InnermostBlockScope;
  return thisblock ? thisblock->x.block.cleanups : 0;
}

static llvm_basicblock *get_rethrow_block(llvm_function *Fn) {
  /* If cleanups exist, we want to create a "rethrow" block for the current
     function.  Because this block always contains the same thing for all
     throws, we only create one per function, lazily. */
  if (!Fn->ExpandInfo->RethrowBlock)
    Fn->ExpandInfo->RethrowBlock = llvm_basicblock_new("rethrow");
  
  return Fn->ExpandInfo->RethrowBlock;
}

static llvm_basicblock *get_terminate_block(llvm_function *Fn) {
  if (!Fn->ExpandInfo->TerminateBlock)
    Fn->ExpandInfo->TerminateBlock = llvm_basicblock_new("terminate");
  return Fn->ExpandInfo->TerminateBlock;
}

/* get_innermost_throw_cleanup_block - Given an LLVM function, this function
   identifies which basic block should be activated if an exception is thrown
   from the current point in the function.  This handles three main cases:

    If there is a containing exception region, the except block is returned, and
    it is marked as used.  If there is no containing exception region, but there
    are cleanup blocks, a new "rethrow" block is created.  If neither of these
    conditions is true, a null pointer is returned.
 */
static llvm_basicblock *get_innermost_throw_cleanup_block(llvm_function *Fn,
                                                          int ForceRethrow) {
  llvm_nesting *nest = Fn->ExpandInfo->InnermostExceptScope;

  if (nest) {
    nest->x.except.Used = 1;
    return nest->x.except.CatchBlock;
  } else if (ForceRethrow) {
    return get_rethrow_block(Fn);
  } else {
    /* No enclosing exception block, check to see if there are any cleanups that
       need to be run from this point. */
    nest = Fn->ExpandInfo->InnermostBlockScope;

    if (Fn->ExpandInfo->CurrentBlockScope)  /* Already partially unwound? */
      nest = Fn->ExpandInfo->CurrentBlockScope;

    for (; nest; nest = nest->next)
      if (nest->x.block.cleanups)
        break;

    if (!nest) return 0;   /* no cleanups, nothing to do! */

    /* Yes there are cleanups to perform.  Return the rethrow block so that an
     * appropriate llvm_expand_goto_internal call will cause the cleanups to be
     * expanded into the goto to the rethrow block.
     */
    return get_rethrow_block(Fn);
  }
}

static llvm_basicblock *get_innermost_catch_block(llvm_function *Fn) {
  return get_innermost_throw_cleanup_block(Fn, 1);
}

static llvm_basicblock *get_invoke_except_dest(llvm_function *Fn) {
  return get_innermost_throw_cleanup_block(Fn, 0);
}


void llvm_emit_code_for_throw(llvm_function *Fn) {
  llvm_basicblock *Dest = get_innermost_catch_block(Fn);
  llvm_expand_goto_internal(Fn, 0, Dest, 0, 1);

  /* Start a new block so that if statements are emitted after the throw, that
   * they will have the correct "current block".
   */
  llvm_emit_label(Fn, llvm_basicblock_new("dead_block_after_throw"));
}


/* llvm_expand_eh_region_start - Start an exception handling region.  All
   instructions emitted after this point are considered to be part of the region
   until an expand_eh_region_end variant is invoked.  */
void llvm_expand_eh_region_start(llvm_function *Fn) {
  llvm_nesting *thisexcept =
    add_scope_stack(Fn, &Fn->ExpandInfo->InnermostExceptScope, EXCEPT_NESTING);
  thisexcept->x.except.CatchBlock = llvm_basicblock_new("try_catch");
  thisexcept->x.except.OutBlock = llvm_basicblock_new("try_exit");
#if 0   /* Used for testing */
  thisexcept->x.except.Used = 1;
#endif
}


/* llvm_expand_eh_region_end_cleanup - End an exception handling region for a
   cleanup (something that must be executed IFF an exception is thrown).
   HANDLER is an expression to expand for the cleanup.  */
void llvm_expand_eh_region_end_cleanup(llvm_function *Fn, tree handler) {
  llvm_nesting thisexcept = *Fn->ExpandInfo->InnermostExceptScope;

  /* Pop the current scope off of the stack... now so that if an exception is
     thrown by a handler that it will be propagated UP, not to the current
     region. */
  pop_and_free_scope_stack(Fn, &Fn->ExpandInfo->InnermostExceptScope);

  if (thisexcept.x.except.Used) {    /* Only emit cleanup if necessary */
    /* Give the language a chance to specify an action to be taken if an
       exception is thrown that would propagate out of the HANDLER.  */
    tree protect_cleanup_actions
      = (lang_protect_cleanup_actions ? (*lang_protect_cleanup_actions)() : 0);

    /* Close off the exception block with a branch to the OutBlock */
    append_inst(Fn, create_uncond_branch(thisexcept.x.except.OutBlock));

    /* Start the catch block... */
    llvm_emit_label(Fn, thisexcept.x.except.CatchBlock);
    
    if (protect_cleanup_actions)
      llvm_expand_eh_region_start(Fn);
    
    /* Expand the cleanup */
    llvm_expand_expr(Fn, handler, 0);
    
    if (protect_cleanup_actions)
      llvm_expand_eh_region_end_must_not_throw(Fn, protect_cleanup_actions);

    /* Propagate control flow to a containing exception region or rethrow as
       necessary */
    llvm_expand_goto_internal(Fn, 0, get_innermost_catch_block(Fn), 0, 1);

    llvm_emit_label(Fn, thisexcept.x.except.OutBlock);
  } else {
    llvm_basicblock_delete(thisexcept.x.except.CatchBlock);
    llvm_basicblock_delete(thisexcept.x.except.OutBlock);
  }
}


/* llvm_expand_eh_region_end_must_not_throw - End an exception handling region
   for a section of code that is not allowed to throw an exception.  Action is 
   an expression to invoke if an uncaught exception propagates this far.

   This is conceptually identical to expand_eh_region_end_allowed with
   an empty allowed list (if you passed "std::terminate" instead of
   "__cxa_call_unexpected"), but they are represented differently in
   the C++ LSDA.
*/
void llvm_expand_eh_region_end_must_not_throw(llvm_function *Fn, tree action) {
  llvm_nesting thisexcept = *Fn->ExpandInfo->InnermostExceptScope;
  
  /* Pop the current exception region off of the stack so that if ACTION throws
     an exception, it is caught by the higher up region */
  pop_and_free_scope_stack(Fn, &Fn->ExpandInfo->InnermostExceptScope);

  if (thisexcept.x.except.Used) {    /* Only emit cleanup if necessary */
    /* Close off the try block with a branch to the OutBlock */
    append_inst(Fn, create_uncond_branch(thisexcept.x.except.OutBlock));
 
    /* Start the catch block... */
    llvm_emit_label(Fn, thisexcept.x.except.CatchBlock);
    llvm_expand_expr(Fn, action, 0);

    llvm_emit_label(Fn, thisexcept.x.except.OutBlock);
  } else {
    llvm_basicblock_delete(thisexcept.x.except.CatchBlock);
    llvm_basicblock_delete(thisexcept.x.except.OutBlock);
  }
}

/* llvm_expand_catch_block - End an exception handling region for a try block,
 * and emit code for all of the exception handlers specified in Handlers.
 * Handlers is a TREE_CHAIN list of HANDLER nodes.
 */
void llvm_expand_catch_block(llvm_function *Fn, tree Handlers) {
  llvm_nesting thisexcept = *Fn->ExpandInfo->InnermostExceptScope;
  
  /* Pop the current exception region off of the stack so that if ACTION throws
     an exception, it is caught by the higher up region.  Any exceptions thrown
     from within the catch block should NOT be caught by this catch block!
   */
  pop_and_free_scope_stack(Fn, &Fn->ExpandInfo->InnermostExceptScope);

  if (!thisexcept.x.except.Used) {    /* Only emit cleanup if necessary */
    llvm_basicblock_delete(thisexcept.x.except.CatchBlock);
    llvm_basicblock_delete(thisexcept.x.except.OutBlock);
    return;
  }

  /* Close off the try block with a branch to the OutBlock */
  append_inst(Fn, create_uncond_branch(thisexcept.x.except.OutBlock));
  llvm_emit_label(Fn, thisexcept.x.except.CatchBlock);

  /* Emit code for the handlers now... */
  for (; Handlers; Handlers = TREE_CHAIN(Handlers)) {
    llvm_basicblock *NextBlock = llvm_basicblock_new("catch");
    llvm_basicblock *CondBlock, *EvalBlock = 0;

    /* Get the block that we are going to expand the condition into.
     */
    CondBlock = llvm_ilist_back(llvm_basicblock, Fn->BasicBlocks);

    /* If this is not a catch (...) block, we need a block to determine
     * whether this is the correct type of block or not.
     */
    if (TREE_TYPE(Handlers)) {
      const char *BlockName = 0;
      if (TREE_CODE (TREE_TYPE(Handlers)) != TREE_LIST) {/* catch one type? */
        tree OneType = TREE_TYPE(Handlers);
        if (TYPE_NAME(OneType)) {
          const char *Tmp;
          if (TREE_CODE(TYPE_NAME(OneType)) == IDENTIFIER_NODE)
            Tmp = IDENTIFIER_POINTER(TYPE_NAME(OneType));
          else 
            Tmp = IDENTIFIER_POINTER(DECL_NAME(TYPE_NAME(OneType)));
            
          BlockName = xmalloc(strlen(Tmp)+strlen("caught.")+1);
          strcat(strcpy((char*)BlockName, "caught."), Tmp);
        }          
      }

      EvalBlock = llvm_basicblock_new(BlockName ? BlockName : "caught");
      llvm_ilist_push_back(llvm_basicblock, Fn->BasicBlocks, EvalBlock);
      if (BlockName) free((char*)BlockName);
    }

    /* Expand the handler. */
    llvm_expand_stmt(Fn, TREE_OPERAND(Handlers, 1));

    /*llvm_expand_start_catch(Fn, TREE_TYPE(Handlers), NextBlock);*/
    if (TREE_TYPE(Handlers)) { /* If this is not a catch (...) block... */
      /* For filtering catch blocks, we know that the block will start with a
       * call to __llvm_cxxeh_begin_catch_if_isa (it was set up
       * this way in cp/except.c).  The problem is that there was no way in
       * that function to insert a branch to "Next Block" if the caught
       * exception was not of the right type.  For this reason, we must look
       * for this call, then insert the conditional branch.
       */
      llvm_instruction *I = llvm_ilist_front(llvm_instruction,
                                             EvalBlock->Instructions);
      llvm_instruction *Set;
      assert(I->Opcode == O_Call && I->Operands[0]->VTy == Function &&
             !strcmp(I->Operands[0]->Name, 
                     "__llvm_cxxeh_begin_catch_if_isa") && 
             "Not a call to __llvm_cxxeh_begin_catch_if_isa!");

      /* Move the ...isa call into the EvalBlock */
      llvm_ilist_splice(llvm_instruction, CondBlock->Instructions,
                        llvm_ilist_end(CondBlock->Instructions),
                        EvalBlock->Instructions, I, llvm_ilist_next(I));

      /* Now that we have the instruction, insert a seteq <ptr>, null */
      Set = create_binary_inst("tmp", O_SetEQ, D2V(I),
                               llvm_constant_VoidPtr_null);
      llvm_ilist_push_back(llvm_instruction, CondBlock->Instructions, Set);

      /* Now output the conditional branch instruction, which goes to
       * CurrentBlock if the pointer returned is not null, otherwise to
       * NextBlock.
       */
      llvm_ilist_push_back(llvm_instruction, CondBlock->Instructions,
                           create_cond_branch(D2V(Set), NextBlock,
                                              EvalBlock));
    }

    /* End a catch clause.  Control will resume after the try/catch block.  */
    append_inst(Fn, create_uncond_branch(thisexcept.x.except.OutBlock));

    /* Start the next catch block... */
    llvm_emit_label(Fn, NextBlock);
  }

  /* If none of the handlers caught the exception, rethrow it by either
     branching to an catch block we are nested in, or by rethrowing the
     exception */
  llvm_expand_goto_internal(Fn, 0, get_innermost_catch_block(Fn), 0, 1);
    
  /* Continue emitting code after the try block */
  llvm_emit_label(Fn, thisexcept.x.except.OutBlock);
}

/* llvm_expand_eh_spec - Having emitted the body of the function, we check to
 * see if we need to emit a "catch (...)" type block to handle any function
 * exception specifiers.  TypeList is a list of the types that this function is
 * allowed to throw.
 */
void llvm_expand_eh_spec(llvm_function *Fn, tree TypeList) {
  llvm_nesting thisexcept = *Fn->ExpandInfo->InnermostExceptScope;
  llvm_instruction *I;
  unsigned ArgNo;

  /* Pop the current exception region off of the stack */
  pop_and_free_scope_stack(Fn, &Fn->ExpandInfo->InnermostExceptScope);

  if (!thisexcept.x.except.Used) {    /* Only emit code if necessary */
    llvm_basicblock_delete(thisexcept.x.except.CatchBlock);
    llvm_basicblock_delete(thisexcept.x.except.OutBlock);
    return;
  }
 
  /* Close off the try block with a branch to the OutBlock */
  append_inst(Fn, create_uncond_branch(thisexcept.x.except.OutBlock));

  /* Start the catch block by removing the exception region from the stack.  Any
   * exceptions thrown from within the catch block should NOT be caught by this
   * catch block!
   */
  llvm_emit_label(Fn, thisexcept.x.except.CatchBlock);

  /* Now that we have caught any thrown exceptions, emit a call to
   * __llvm_cxxeh_check_eh_spec to verify that the exception object is allowed.
   * If it is, the function will return, and we should 'unwind' with the
   * exception.
   */
  I = llvm_instruction_new(VoidTy, "", O_Call, list_length(TypeList)+2);
  {
    static llvm_function *check_eh = 0;
    if (check_eh == 0) {
      llvm_type *FnTy = llvm_type_create_function(1, VoidTy);
      FnTy->x.Function.isVarArg = 1;
      FnTy->Elements[1] = VoidPtrTy;
      FnTy = llvm_type_get_cannonical_version(FnTy);
      check_eh = CreateIntrinsicFnWithType("__llvm_cxxeh_check_eh_spec", FnTy);
    }
    I->Operands[0] = G2V(check_eh);
  }

  for (ArgNo = 1; TypeList; TypeList = TREE_CHAIN(TypeList), ++ArgNo) {
    tree typeid = lang_eh_runtime_type(TREE_VALUE(TypeList));
    llvm_value *typeidVal = llvm_expand_expr(Fn, typeid, 0);
    if (ArgNo == 1) typeidVal = cast_if_type_not_equal(Fn, typeidVal,VoidPtrTy);
    I->Operands[ArgNo] = typeidVal;
  }
  I->Operands[ArgNo] = llvm_constant_VoidPtr_null;

  append_inst(Fn, I);

  /* If none of the handlers caught the exception, rethrow it by either
     branching to an catch block we are nested in, or by rethrowing the
     exception */
  llvm_expand_goto_internal(Fn, 0, get_innermost_catch_block(Fn), 0, 1);

  /* Continue emitting code after the try block */
  llvm_emit_label(Fn, thisexcept.x.except.OutBlock);
}


/*===----------------------------------------------------------------------===**
                    ... Control Flow Statement Expansion ...
 *===----------------------------------------------------------------------===*/

/* Some statements, like for-statements or if-statements, require a
   condition.  This condition can be a declaration.  If T is such a
   declaration it is processed, and an expression appropriate to use
   as the condition is returned.  Otherwise, T itself is returned.  */

static tree llvm_expand_cond (llvm_function *Fn, tree t) {
  if (t && TREE_CODE (t) == TREE_LIST) {
    llvm_expand_stmt (Fn, TREE_PURPOSE (t));
    return TREE_VALUE (t);
  } else 
    return t;
}

/* Generate LLVM for the start of an if-then.  COND is the expression whose
   truth should be tested.

   If EXITFLAG is nonzero, this conditional is visible to `exit_something'.  */

static void llvm_expand_start_cond (llvm_function *Fn, tree cond, int exitflag,
                                    int has_else) {
  llvm_nesting *thiscond = 
    add_scope_stack(Fn, &Fn->ExpandInfo->InnermostCondScope, COND_NESTING);
  llvm_basicblock *IfTrueBlock = llvm_basicblock_new("then");
  llvm_value *CondVal;

  /* Make an entry on cond_stack for the cond we are entering.  */
  thiscond->x.cond.next_block = llvm_basicblock_new(has_else ? "else" :"endif");

  thiscond->exit_block = exitflag ? llvm_basicblock_new("exit") : 0;
  thiscond->x.cond.exit_block = thiscond->exit_block;

  if (thiscond->x.cond.exit_block == 0) {
    if (has_else)
      thiscond->x.cond.exit_block = llvm_basicblock_new("endif");
    else
      thiscond->x.cond.exit_block = thiscond->x.cond.next_block;
  }

  /* Expand the condition in this block so that any temporaries are scoped
     correctly */
  CondVal = llvm_expand_expr(Fn, cond, 0);
  CondVal = cast_if_type_not_equal(Fn, CondVal, BoolTy);

  append_inst(Fn, create_cond_branch(CondVal, IfTrueBlock,
                                     thiscond->x.cond.next_block));
  
  /* Add the "true" block to the function */
  llvm_ilist_push_back(llvm_basicblock, Fn->BasicBlocks, IfTrueBlock);
}


/* Generate RTL between the then-clause and the else-clause
   of an if-then-else.  */

static void llvm_expand_start_else (llvm_function *Fn) {
  llvm_nesting *thiscond = Fn->ExpandInfo->InnermostCondScope;
  assert(thiscond == Fn->ExpandInfo->InnermostScope);

  /* Exit the previous block */
  append_inst(Fn, create_uncond_branch(thiscond->x.cond.exit_block));

  /* Add the else block to the function */
  llvm_ilist_push_back(llvm_basicblock, Fn->BasicBlocks,
                       thiscond->x.cond.next_block);

  /* The next block to add is the exit block */
  thiscond->x.cond.next_block = thiscond->x.cond.exit_block;
}


/* Generate RTL for the end of an if-then.
   Pop the record for it off of cond_stack.  */

static void llvm_expand_end_cond(llvm_function *Fn) {
  llvm_nesting *thiscond = Fn->ExpandInfo->InnermostCondScope;
  assert(thiscond == Fn->ExpandInfo->InnermostScope);

  /* Add the "next" block to the function and exit the current block */
  append_inst(Fn, create_uncond_branch(thiscond->x.cond.exit_block));
  llvm_ilist_push_back(llvm_basicblock, Fn->BasicBlocks,
                       thiscond->x.cond.next_block);

  /* Pop the item off of the scope stacks */
  pop_and_free_scope_stack(Fn, &Fn->ExpandInfo->InnermostCondScope);
}

/* Generate (if necessary) a fixup for a goto whose target label in tree
   structure (if any) is TREE_LABEL and whose target LLVM basicblock is BB.

   The fixup will be used later to insert insns just before the goto.  Those
   insns will invoke any object destructors which have to be invoked when we
   exit the scopes which are exited by the goto.

   See llvm_expand_goto_internal for info about the CleanupsCanThrow flag.
*/
static void llvm_expand_fixup(llvm_function *Fn, int CleanupsCanThrow,
                              int isExceptionEdge, llvm_basicblock *BB,
                              llvm_instruction *Branch,
                              llvm_basicblock *BranchBlock) {
  llvm_nesting *block;
  llvm_goto_fixup *fixup;
    
  /* Does any containing block have a stack level or cleanups?  If not, no fixup
     is needed, and that is the normal case (the only case, for standard C).  */
  for (block = Fn->ExpandInfo->InnermostBlockScope; block; block = block->next)
    if (block->x.block.cleanups != 0)
      break;

  if (block == 0) return;

  if (Fn->ExpandInfo->CurrentBlockScope)   /* Already partially unwound? */
    block = Fn->ExpandInfo->CurrentBlockScope;

  /* Ok, a fixup is needed.  Add a fixup to the list of such.  */
  fixup = (llvm_goto_fixup*)xcalloc(sizeof(llvm_goto_fixup), 1);

  fixup->BranchBlock = BranchBlock;
  fixup->BranchInst = Branch;
  fixup->target_bb = BB;
  fixup->CleanupsCanThrow = CleanupsCanThrow;
  fixup->isExceptionEdge  = isExceptionEdge;
  fixup->containing_block = block;
  fixup->cleanup_list = block->x.block.cleanups;

  /* Add the fixup to the list of fixups for this function... */
  fixup->next = Fn->ExpandInfo->GotoFixupList;
  Fn->ExpandInfo->GotoFixupList = fixup;
}

/* Generate LLVM code for a `goto' statement with target LABEL_DECL body.
 *
 * This function is used for a variety of control flow purposes.  In particular,
 * it is the main place responsible for determining which cleanups must be
 * executed as a result of leaving blocks with destructors.  This function
 * either immediately expands the cleanups into the code (if it knows which ones
 * will be necessary) or it schedules them to be inserted with a goto_fixup
 * record.
 *
 * If it is illegal for inserted cleanups to throw any exceptions,
 * CleanupsCanThrow should be set to zero.  This is an important case for
 * exception handling: when unwinding the stack due to an active exception, any
 * destructors which propagate exceptions should cause terminate to be called.
 * Thus, if a cleanup can throw an exception, it's exception destination goes to
 * a designated terminate block.
 *
 * If isException edge is true, cleanups which apply only to exceptions are
 * expanded, otherwise they are not.
 */
static void llvm_expand_goto_internal(llvm_function *Fn, tree body,
                                      llvm_basicblock *label,
                                      int CleanupsCanThrow,
                                      int isExceptionEdge) {
  /* Create the final branch we will be using */
  llvm_instruction *Branch = create_uncond_branch(label);

  /* If label has already been defined, we can tell now whether and how we must
     run cleanups.  */
  if (llvm_ilist_inlist(label)) {
    /* Scan through the current nesting levels that we are in, emitting cleanups
     * for any blocks that we are exiting.  To do this, we scan through the
     * function backwards until we find the label we are branching to.
     */
    llvm_nesting *block = Fn->ExpandInfo->InnermostBlockScope;
    llvm_basicblock *CurBB = llvm_ilist_back(llvm_basicblock, Fn->BasicBlocks);

    if (Fn->ExpandInfo->CurrentBlockScope)   /* Already partially unwound? */
      block = Fn->ExpandInfo->CurrentBlockScope;

    if (!CleanupsCanThrow)
      Fn->ExpandInfo->ThrownExceptionsCallTerminate++;

    while (block) {
      /* First step, emit any cleanups for blocks that were begun in the current
         basic block */
      for (; block && block->x.block.StartBlock == CurBB; block = block->next)
        if (block->x.block.cleanups) {
          /* Set CurrentBlockScope to the current block.  This is critical
           * because expanded cleanups may need cleanups of their own.  If this
           * did not exist, they would restart cleaning up from the TOP of the
           * nesting stack, even through we have already destroyed a portion of
           * the nesting stack.  This allows the cleanups to only destroy the
           * portions of the stack that have not yet been unwound.
           */
          llvm_nesting *OldCBS = Fn->ExpandInfo->CurrentBlockScope;
          Fn->ExpandInfo->CurrentBlockScope = block;
          /* Expand the cleanups for the block we're exiting */
          llvm_expand_cleanups(Fn, &block->x.block.cleanups, isExceptionEdge);
          Fn->ExpandInfo->CurrentBlockScope = OldCBS;
        }

      if (CurBB == label || !block)    /* Found the block we are looking for! */
        break;

      /* Scan through the function until we find the beginning of the next
         block */
      while (CurBB != block->x.block.StartBlock && CurBB != label)
        CurBB = llvm_ilist_prev(CurBB);
    }

    if (!CleanupsCanThrow)
      Fn->ExpandInfo->ThrownExceptionsCallTerminate--;

    if (body != 0 && DECL_TOO_LATE (body))
      error ("jump to `%s' invalidly jumps into binding contour",
             IDENTIFIER_POINTER (DECL_NAME (body)));
  } else {
    /* Label not yet defined: may need to put this goto on the fixup list.  */
    llvm_expand_fixup(Fn, CleanupsCanThrow, isExceptionEdge, label, Branch,
                      llvm_ilist_back(llvm_basicblock, Fn->BasicBlocks));
  }
  
  append_inst(Fn, Branch);
}


/* llvm_expand_null_return - Generate LLVM to return from the current function,
 * with no value.  (That is, we do not do anything about returning any
 * value.)
 */

static void llvm_expand_null_return(llvm_function *Fn) {
  llvm_basicblock *EndLabel = Fn->ExpandInfo->CleanupBlock ? 
                 Fn->ExpandInfo->CleanupBlock : Fn->ExpandInfo->ReturnBlock;

  /* Simply goto the exit label now. */
  llvm_expand_goto_internal(Fn, NULL_TREE, EndLabel, 1, 0);

  /* Start a new block so that if statements are emitted after the return, that
   * they will have the correct "current block".
   */
  llvm_emit_label(Fn, llvm_basicblock_new("after_ret"));
}

/* llvm_expand_return - Generate LLVM to evaluate the expression RETVAL and
   return it from the current function.  */
static void llvm_expand_return(llvm_function *Fn, tree retval) {
  /* Process the assignment to RETURN_DECL. */
  llvm_expand_expr(Fn, retval, 0);

  /* Expand the branch to the return block, running any cleanups necessary. */
  llvm_expand_null_return(Fn);
}

/* getLabelDeclBlock - This is a wrapper function that is used to lazily create
   llvm_basicblock's for labels on demand.
 */
static llvm_basicblock* getLabelDeclBlock(tree LD) {
  const char *Name;
  llvm_basicblock *BB;
  assert(TREE_CODE(LD) == LABEL_DECL);
  if (DECL_LLVM_SET_P(LD)) return (llvm_basicblock*)DECL_LLVM(LD);

  /* Create a new basic block for the label */
  Name = DECL_NAME(LD) ? IDENTIFIER_POINTER(DECL_NAME(LD)) : "label";
  BB = llvm_basicblock_new(Name);
  SET_DECL_LLVM(LD, D2V(BB));
  return BB;  
}

/* Specify the location in the LLVM code of a label LABEL, which is a LABEL_DECL
   tree node.

   This is used for the kind of label that the user can jump to with a goto
   statement, and for alternatives of a switch or case statement.  LLVM labels
   generated for loops and conditionals don't go through here; they are
   generated directly at the LLVM level, by other functions.

   Note that this has nothing to do with defining label *names*.  Languages vary
   in how they do that and what that even means.  */

static void llvm_expand_label(llvm_function *Fn, tree Label) {
  llvm_emit_label(Fn, getLabelDeclBlock(Label));
}

/* Generate RTL for the start of a loop.  EXIT_FLAG is nonzero if this
   loop should be exited by `exit_something'.  This is a loop for which
   `expand_continue' will jump to the top of the loop.

   Make an entry on loop_stack to record the labels associated with
   this loop.  */

static void llvm_expand_start_loop(llvm_function *Fn, int exit_flag) {
  /* Make an entry on loop_stack for the loop we are entering.  */
  llvm_nesting *thisloop =
    add_scope_stack(Fn, &Fn->ExpandInfo->InnermostLoopScope, LOOP_NESTING);

  thisloop->x.loop.start_label = llvm_basicblock_new("loopentry");
  thisloop->x.loop.end_label = llvm_basicblock_new("loopexit");
  thisloop->x.loop.continue_label = thisloop->x.loop.start_label;
  thisloop->exit_block = exit_flag ? thisloop->x.loop.end_label : 0;

  llvm_emit_label(Fn, thisloop->x.loop.start_label);
}

/* Like expand_start_loop but for a loop where the continuation point
   (for expand_continue_loop) will be specified explicitly.  */

static void llvm_expand_start_loop_continue_elsewhere(llvm_function *Fn,
                                                      int exit_flag) {
  llvm_expand_start_loop(Fn, exit_flag);
  Fn->ExpandInfo->InnermostLoopScope->x.loop.continue_label = 
    llvm_basicblock_new("loopcont");
}


/* Finish a loop.  Generate a jump back to the top and the loop-exit label.
   Pop the block off of loop_stack.  */
static void llvm_expand_end_loop(llvm_function *Fn) {
  llvm_nesting *thisloop = Fn->ExpandInfo->InnermostLoopScope;

  /* Create backwards branch to loop header */
  append_inst(Fn, create_uncond_branch(thisloop->x.loop.start_label));

  /* Start the after-loop code by adding the exit block to the function */
  llvm_ilist_push_back(llvm_basicblock, Fn->BasicBlocks,
                       thisloop->x.loop.end_label);

  pop_and_free_scope_stack(Fn, &Fn->ExpandInfo->InnermostLoopScope);
}




/* Begin a null, aka do { ... } while (0) "loop".  But since the contents of
   said loop can still contain a break, we must frob the loop nest.  */

static void llvm_expand_start_null_loop(llvm_function *Fn) {
  /* Make an entry on loop_stack for the loop we are entering.  */
  llvm_nesting *thisloop = 
    add_scope_stack(Fn, &Fn->ExpandInfo->InnermostLoopScope, LOOP_NESTING);

  thisloop->x.loop.start_label = 0;     /* null loop never comes back */
  thisloop->x.loop.end_label      = llvm_basicblock_new("null_do_exit");
  thisloop->x.loop.continue_label = thisloop->x.loop.end_label;
  thisloop->exit_block            = thisloop->x.loop.end_label;
}

/* Finish a null loop, aka do { } while (0).  */
static void llvm_expand_end_null_loop(llvm_function *Fn) {
  llvm_nesting *thisloop = Fn->ExpandInfo->InnermostLoopScope;

  if (thisloop->BreakFound || thisloop->x.loop.ContinueFound) {
    /* Emit a branch from the current block to the exit block */
    llvm_emit_label(Fn, thisloop->x.loop.end_label);
  } else {
    llvm_basicblock_delete(thisloop->x.loop.end_label);
  }

  pop_and_free_scope_stack(Fn, &Fn->ExpandInfo->InnermostLoopScope);
}



/* Generate a jump to the current loop's continue-point.
   This is usually the top of the loop, but may be specified
   explicitly elsewhere.  If not currently inside a loop,
   return 0 and do nothing; caller will print an error message.  */

static int llvm_expand_continue_loop(llvm_function *Fn,
                                     llvm_nesting *whichloop) {
  if (whichloop == 0)
    whichloop = Fn->ExpandInfo->InnermostLoopScope;
  if (whichloop == 0)
    return 0;

  whichloop->x.loop.ContinueFound = 1;
  llvm_expand_goto_internal(Fn, NULL_TREE, whichloop->x.loop.continue_label,
                            1, 0);
  return 1;
}

/* Specify the continuation point for a loop started with
   llvm_expand_start_loop_continue_elsewhere.  Use this at the point in the code
   to which a continue statement should jump.  */

static void llvm_expand_loop_continue_here(llvm_function *Fn) {
  llvm_nesting *CurLoop = Fn->ExpandInfo->InnermostLoopScope;
  if (CurLoop->x.loop.ContinueFound)
    llvm_emit_label(Fn, CurLoop->x.loop.continue_label);
  else
    llvm_basicblock_delete(CurLoop->x.loop.continue_label);
}

/* Generate a conditional jump to exit the current loop if COND
   evaluates to zero.  If not currently inside a loop,
   return 0 and do nothing; caller will print an error message.  */

static int llvm_expand_exit_loop_if_false(llvm_function *Fn, 
                                          llvm_nesting *whichloop, tree cond) {
  int HasCleanups = 0;
  llvm_nesting *N;
  llvm_basicblock *ContBlock;
  llvm_value *Cond;

  if (whichloop == 0)
    whichloop = Fn->ExpandInfo->InnermostLoopScope;
  if (whichloop == 0)
    return 0;

  if (integer_nonzerop(cond))        /* No exit can happen */
    return 1;               
  if (integer_zerop(cond)) {         /* Exit is guaranteed to happen */
    llvm_expand_goto_internal(Fn, NULL_TREE, whichloop->x.loop.end_label, 1, 0);
    return 1;
  }

  /* Check to see if we won't need cleanups (the only case for C) */
  for (N = Fn->ExpandInfo->InnermostScope; N != whichloop; N = N->all)
    if (N->desc == BLOCK_NESTING && N->x.block.cleanups) {
      HasCleanups = 1;
      break;
    }

  ContBlock = llvm_basicblock_new("no_exit");
  Cond = llvm_expand_expr(Fn, cond, 0);
  Cond = cast_if_type_not_equal(Fn, Cond, BoolTy);
    
  if (!HasCleanups) {
    append_inst(Fn, create_cond_branch(Cond, ContBlock,
                                       whichloop->x.loop.end_label));
  } else {
    /* In order to handle cleanups, we actually create a conditional jump around
       an unconditional branch to exit the loop.  If fixups are necessary, they
       go before the unconditional branch.  We do this because
       llvm_expand_goto_internal only operates on unconditional branches. */
    llvm_basicblock *ExitHelperBlock =llvm_basicblock_new("exit_loop_cleanups");
    append_inst(Fn, create_cond_branch(Cond, ContBlock, ExitHelperBlock));
    llvm_expand_goto_internal(Fn, NULL_TREE, whichloop->x.loop.end_label, 1, 0);
  }
  llvm_ilist_push_back(llvm_basicblock, Fn->BasicBlocks, ContBlock);
  return 1;
}


/* Generate a jump to exit the current loop, conditional, binding contour
   or case statement.  Not all such constructs are visible to this function,
   only those started with EXIT_FLAG nonzero.  Individual languages use
   the EXIT_FLAG parameter to control which kinds of constructs you can
   exit this way.

   If not currently inside anything that can be exited,
   return 0 and do nothing; caller will print an error message.  */

static int llvm_expand_exit_something(llvm_function *Fn) {
  llvm_nesting *n;
  for (n = Fn->ExpandInfo->InnermostScope; n; n = n->all)
    if (n->exit_block) {
      n->BreakFound = 1;
      llvm_expand_goto_internal(Fn, NULL_TREE, n->exit_block, 1, 0);
      return 1;
    }

  return 0;
}


/* llvm_expand_start_case - Enter a case (Pascal) or switch (C) statement.  Push
   a block onto InnermostCaseScope and InnermostScope to accumulate the
   case-labels that are seen and to record the labels generated for the
   statement.

   EXIT_FLAG is nonzero if `exit_something' should exit this case stmt.
   Otherwise, this construct is transparent for `exit_something'.

   EXPR is the index-expression to be dispatched on.
*/
static void llvm_expand_start_case(llvm_function *Fn, int exit_flag, tree expr,
                                   const char *printname) {
  /* Make an entry on loop_stack for the loop we are entering.  */
  llvm_nesting *thiscase = 
    add_scope_stack(Fn, &Fn->ExpandInfo->InnermostCaseScope, CASE_NESTING);
  llvm_instruction *SI = llvm_instruction_new(VoidTy, "", O_Switch, 2);
  llvm_value *Val = llvm_expand_expr(Fn, expr, 0);

  SI->Operands[0] = cast_if_type_not_equal(Fn, Val, UIntTy);

  append_inst(Fn, SI);
  thiscase->x.switchblock.SwitchInst = SI;
  thiscase->x.switchblock.printname = printname;
  thiscase->exit_block = exit_flag ? llvm_basicblock_new("switchexit") : 0;
}

/* Terminate a case (Pascal) or switch (C) statement
   in which INDEX is the expression to be tested.
   If ORIG_TYPE is not NULL, it is the original ORIG_INDEX
   type as given in the source before any compiler conversions.
   Generate the code to test it and jump to the right place.  */

static void llvm_expand_end_case_type(llvm_function *Fn, tree index_expr) {
  llvm_nesting *thiscase = Fn->ExpandInfo->InnermostCaseScope;
  llvm_instruction *SwitchInst;

  /* Don't crash due to previous errors.  */
  if (thiscase == NULL) return;

  SwitchInst = thiscase->x.switchblock.SwitchInst;

  /* An ERROR_MARK occurs for various reasons including invalid data type.  */
  assert(TREE_TYPE(index_expr) != error_mark_node);

#if 0
  /* If the switch expression was an enumerated type, check that exactly all
     enumeration literals are covered by the cases.  The check is made when
     -Wswitch was specified and there is no default case, or when -Wswitch-enum
     was specified.  */
  if (((warn_switch && !thiscase->data.case_stmt.default_label)
       || warn_switch_enum)
      && TREE_CODE (orig_type) == ENUMERAL_TYPE
      && TREE_CODE (index_expr) != INTEGER_CST)
    check_for_full_enumeration_handling (orig_type);
#endif
  if (warn_switch_default && !SwitchInst->Operands[1])
    warning ("switch missing default case");

  /* If we don't have a default-block, create one here. */
  if (!SwitchInst->Operands[1]) {
    /* Share the exit block if possible.  */
    if (!thiscase->exit_block)
      thiscase->exit_block = llvm_basicblock_new("exitcase");
    SwitchInst->Operands[1] = D2V(thiscase->exit_block);
  } else if (!thiscase->exit_block) {
    thiscase->exit_block = llvm_basicblock_new("exitcase");
  }

  /* Emit the exit label for the switch statement. */
  llvm_emit_label(Fn, thiscase->exit_block);

#if 0
  end_cleanup_deferral ();
#endif

  /* Pop the current scope off of the stack... */
  pop_and_free_scope_stack(Fn, &Fn->ExpandInfo->InnermostCaseScope);
}

/* Add a case label to the current switch statement.  This could be a range of
   case values to insert.  Handle them as appropriate.
 */
static void llvm_add_case_node(llvm_function *Fn, tree low, tree high,
                               tree label) {
  llvm_nesting *thiscase = Fn->ExpandInfo->InnermostCaseScope;
  llvm_instruction *SwitchInst;
  llvm_basicblock *Block = getLabelDeclBlock(label);
  int Low, High;

  assert(thiscase && "Case label not in case statement!");
  SwitchInst = thiscase->x.switchblock.SwitchInst;

  llvm_expand_label(Fn, label);

  if (!high) {
    if (low) {
      /* If there's no HIGH value, then this is not a case range; it's just a
         simple case label.  But that's just a degenerate case range.  */
      high = low;
    } else {
      /* Handle default labels specially.  */
      assert(SwitchInst->Operands[1] == 0 &&"Default label already specified!");
      SwitchInst->Operands[1] = D2V(Block);
      return;
    }
  }

  if ((TREE_INT_CST_HIGH(low) != 0 || TREE_INT_CST_HIGH(high) != 0) &&
      (TREE_INT_CST_HIGH(low) != -1 || TREE_INT_CST_HIGH(high) != -1))
    LLVM_TODO_TREE(label); /* Cannot handle case values this large! */

  Low = (int)TREE_INT_CST_LOW(low);
  High = (int)TREE_INT_CST_LOW(high);

  for (; Low <= High; ++Low) {
    llvm_switch_case *NewCase = xmalloc(sizeof(llvm_switch_case));
    NewCase->Next = SwitchInst->x.Switch.Cases;
    SwitchInst->x.Switch.Cases = NewCase;
    NewCase->Value = Low;
    NewCase->Dest = Block;
  }
}



/*===----------------------------------------------------------------------===**
                  ... Statement Expansion Implementation ...
 *===----------------------------------------------------------------------===*/

/* Generate LLVM code for T, which is an IF_STMT.  */

static void genllvm_if_stmt(llvm_function *Fn, tree t) {
  tree cond = llvm_expand_cond (Fn, IF_COND (t));

  llvm_expand_start_cond(Fn, cond, 0, ELSE_CLAUSE(t) != 0);
  if (THEN_CLAUSE (t))
    llvm_expand_stmt (Fn, THEN_CLAUSE (t));
  if (ELSE_CLAUSE (t)) {
    llvm_expand_start_else (Fn);
    llvm_expand_stmt (Fn, ELSE_CLAUSE (t));
  }
  llvm_expand_end_cond (Fn);
}


/* Generate LLVM code for T, which is a SCOPE_STMT.  This is modelled
 * after genrtl_scope_stmt
 */
static void genllvm_scope_stmt(llvm_function *F, tree t) {
  tree block = SCOPE_STMT_BLOCK (t);

  if (!SCOPE_NO_CLEANUPS_P (t)) {
    if (SCOPE_BEGIN_P (t))
      llvm_expand_start_bindings(F);
    else if (SCOPE_END_P (t))
      llvm_expand_end_bindings(F, NULL_TREE);
  }

  /* If we're at the end of a scope that contains inlined nested
     functions, we have to decide whether or not to write them out.  */
  if (block && SCOPE_END_P (t))
    {
      tree fn;

      for (fn = BLOCK_VARS (block); fn; fn = TREE_CHAIN (fn))
        {
          if (TREE_CODE (fn) == FUNCTION_DECL 
              && DECL_CONTEXT (fn) == current_function_decl
              && DECL_SAVED_INSNS (fn)
              && !TREE_ASM_WRITTEN (fn)
              && TREE_ADDRESSABLE (fn))
            {
	      LLVM_TODO_TREE(fn);
#if 0
              push_function_context ();
              output_inline_function (fn);
              pop_function_context ();
#endif
            }
        }
    }
}

static int llvm_expand_decl_cleanup_eh(llvm_function *Fn, tree decl,
                                       tree cleanup, int eh_only);

/* Generate LLVM code for a CLEANUP_STMT.  */
static void genllvm_decl_cleanup(llvm_function *Fn, tree t) {
  tree decl = CLEANUP_DECL (t);
  if (!decl || (DECL_SIZE (decl) && TREE_TYPE (decl) != error_mark_node))
    llvm_expand_decl_cleanup_eh(Fn, decl, CLEANUP_EXPR(t), CLEANUP_EH_ONLY(t));
}

/* Generate LLVM code for the a GOTO to the specified destination */
static void genllvm_goto_stmt(llvm_function *Fn, tree dest) {
  if (TREE_CODE(dest) == IDENTIFIER_NODE) abort ();

  if (TREE_CODE(dest) != LABEL_DECL) {
    fprintf(stderr, "Computed gotos not supported!!!");
    LLVM_TODO_TREE(dest);
  }

  TREE_USED(dest) = 1;
  llvm_expand_goto_internal(Fn, dest, getLabelDeclBlock(dest), 1, 0);
}

/* Generate LLVM code for a RETURN_STMT */
static void genllvm_return_stmt(llvm_function *Fn, tree expr) {
  if (!expr) {
    /* Generate LLVM to return from the current function, with no value */
    llvm_expand_null_return (Fn);

  } else {
    /* Specify the scope of temporaries created by TARGET_EXPRs.  Similar
     * to CLEANUP_POINT_EXPR, but handles cases when a series of calls to
     * expand_expr are made.  After we end the region, we know that all
     * space for all temporaries that were created by TARGET_EXPRs will be
     * destroyed and their space freed for reuse.
     */
    /* Start a new binding layer that will keep track of all cleanup
       actions to be performed.  */
    llvm_expand_start_bindings(Fn);
    
    llvm_expand_return(Fn, expr);
    
    /* End the bindings level */
    llvm_expand_end_bindings(Fn, 0);
  }
}

/* Generate LLVM code for a DO_STMT */
static void genllvm_do_stmt(llvm_function *Fn, tree t) {
  tree cond = DO_COND (t);

  /* Recognize the common special-case of do { ... } while (0) and do not emit
     the loop widgetry in this case.  COND can be NULL due to parse errors.  */
  if (!cond || integer_zerop (cond)) {
    llvm_expand_start_null_loop(Fn);
    llvm_expand_stmt(Fn, DO_BODY (t));
    llvm_expand_end_null_loop(Fn);
  } else if (integer_nonzerop (cond)) {
    llvm_expand_start_loop(Fn, 1);
    llvm_expand_stmt(Fn, DO_BODY(t));
    llvm_expand_end_loop(Fn);
  } else {
    llvm_expand_start_loop_continue_elsewhere(Fn, 1);

    llvm_expand_stmt(Fn, DO_BODY(t));

    llvm_expand_loop_continue_here(Fn);
    cond = llvm_expand_cond(Fn, cond);
    llvm_expand_exit_loop_if_false(Fn, 0, cond);
    llvm_expand_end_loop(Fn);
  }
}

/* Generate LLVM code for T, which is a WHILE_STMT.  */
static void genllvm_while_stmt(llvm_function *Fn, tree t) {
  tree cond = WHILE_COND(t);

  llvm_expand_start_loop(Fn, 1); 

  if (cond && !integer_nonzerop (cond)) {
    cond = llvm_expand_cond(Fn, cond);
    llvm_expand_exit_loop_if_false(Fn, 0, cond);
  }
  
  llvm_expand_stmt(Fn, WHILE_BODY(t));
  llvm_expand_end_loop(Fn);
}

/* Generate LLVM code for T, which is a FOR_STMT.  */
static void genllvm_for_stmt(llvm_function *Fn, tree t) {
  tree cond = FOR_COND(t);

  llvm_expand_stmt(Fn, FOR_INIT_STMT(t));

  /* Expand the initialization.  */
  if (FOR_EXPR(t))
    llvm_expand_start_loop_continue_elsewhere(Fn, 1);
  else
    llvm_expand_start_loop(Fn, 1);

  /* Expand the condition.  */
  if (cond && !integer_nonzerop(cond)) {
    cond = llvm_expand_cond(Fn, cond);
    llvm_expand_exit_loop_if_false(Fn, 0, cond);
  }

  /* Expand the body.  */
  llvm_expand_stmt(Fn, FOR_BODY (t));

  /* Expand the increment expression.  */
  if (FOR_EXPR (t)) {
    llvm_expand_loop_continue_here (Fn);

    if (stmts_are_full_exprs_p ())    /* Provide a scope for C++ temporaries */
      llvm_expand_start_bindings(Fn);

    llvm_expand_expr(Fn, FOR_EXPR(t), 0);

    if (stmts_are_full_exprs_p ())
      llvm_expand_end_bindings(Fn, 0);
  }
  llvm_expand_end_loop (Fn);
}

/* Generate LLVM code for T, which is a SWITCH_STMT.  */
static void genllvm_switch_stmt(llvm_function *Fn, tree t) {
  tree cond = llvm_expand_cond(Fn, SWITCH_COND(t));
  if (cond == error_mark_node)
    cond = boolean_false_node;

  llvm_expand_start_case(Fn, 1, cond, "switch statement");
  llvm_expand_stmt(Fn, SWITCH_BODY (t));
  llvm_expand_end_case_type(Fn, cond);
}

/* Generate LLVM code for T, which is a CASE_LABEL.  */
static void genllvm_case_label(llvm_function *Fn, tree case_label) {
  tree cleanup = llvm_last_cleanup_this_contour(Fn);
  if (cleanup) {
    static int explained = 0;
    warning ("destructor needed for `%#D'", (TREE_PURPOSE (cleanup)));
    warning ("where case label appears here");
    if (!explained) {
      warning ("(enclose actions of previous case statements requiring destructors in their own scope.)");
      explained = 1;
    }
  }
  
  llvm_add_case_node(Fn, CASE_LOW (case_label), CASE_HIGH (case_label), 
                     CASE_LABEL_DECL (case_label));  
}

/*===----------------------------------------------------------------------===**
                   ... Variable Declaration Expansion ...
 *===----------------------------------------------------------------------===*/

/* Generate LLVM for the automatic variable declaration DECL.
   (Other kinds of declarations are simply ignored if seen here.)  */

static void llvm_expand_decl (llvm_function *Fn, tree decl) {
  tree type = TREE_TYPE (decl);
  llvm_instruction *I;   /* The instruction created for the variable */
  llvm_type  *Ty;        /* Type to allocate */
  llvm_value *Size;      /* Amount to alloca */
  const char *Name;      /* Name of variable */

  /* For a CONST_DECL, set mode, alignment, and sizes from those of the
     type in case this node is used in a reference.  */
  if (TREE_CODE (decl) == CONST_DECL) {
    DECL_MODE (decl) = TYPE_MODE (type);
    DECL_ALIGN (decl) = TYPE_ALIGN (type);
    DECL_SIZE (decl) = TYPE_SIZE (type);
    DECL_SIZE_UNIT (decl) = TYPE_SIZE_UNIT (type);
    return;
  }

  /* Otherwise, only automatic (and result) variables need any expansion done.
     Static and external variables, and external functions, will be handled by
     `assemble_variable' (called from finish_decl).  TYPE_DECL requires nothing.
     PARM_DECLs are handled in `llvm_expand_function_start'.  */
  if ((TREE_CODE(decl) != VAR_DECL && TREE_CODE(decl) != RESULT_DECL) ||
      TREE_STATIC(decl) || DECL_EXTERNAL(decl))
    return;

  /* Create the LLVM representation for the variable.  */
  if (type == error_mark_node) return;

  if (DECL_SIZE (decl) == 0) {
    /* Variable with incomplete type.  */
    if (DECL_INITIAL (decl) == 0)
      /* Error message was already done; now avoid a crash.  */
      return;

    LLVM_TODO_TREE(decl);

  } else if (TREE_CODE (DECL_SIZE_UNIT (decl)) == INTEGER_CST) {
    /* Variable of fixed size that goes on the stack.  */
    Ty = llvm_type_get_from_tree(type);
    
    /* Set alignment we actually gave this decl.  */
    DECL_ALIGN (decl) = (DECL_MODE (decl) == BLKmode ? BIGGEST_ALIGNMENT
                         : GET_MODE_BITSIZE (DECL_MODE (decl)));
    DECL_USER_ALIGN (decl) = 0;
    
    Size = llvm_constant_uint_1;
  } else {
    /* Dynamic-size object: must push space on the stack.  */
    if (TREE_CODE (type) == ARRAY_TYPE && TYPE_DOMAIN (type)) {
      /* Compute the size of the number of elements of the array */
      Size = llvm_expand_expr(Fn, TYPE_MAX_VALUE(TYPE_DOMAIN(type)), 0);
      Size = cast_if_type_not_equal(Fn, Size, UIntTy);
      Ty = llvm_type_get_from_tree(TREE_TYPE(type));

      /* Unfortunately for us, TYPE_MAX_VALUE returns the maximum valid
       * index, NOT the number of elements in the array.  Thus, we must add one
       * to the returned value.  This addition should be optimized out.
       */
      I = create_binary_inst("tmp", O_Add, Size, llvm_constant_uint_1);
      Size = append_inst(Fn, I);

    } else {
      /* Compute the variable's size, in bytes.  */
      Size = llvm_expand_expr(Fn, DECL_SIZE_UNIT(decl), 0);
      Ty = SByteTy;
    }
  }

  /* Use an alloca to allocate this value... add it to the current basic
     block */
  if (DECL_NAME(decl))
    Name = IDENTIFIER_POINTER(DECL_NAME(decl));
  else if (TREE_CODE(decl) == RESULT_DECL)
    Name = "result";
  else
    Name = "tmp";

  /* an LLVM value pointer for this decl may already be set, for example, if the
   *  named return value optimization is being applied to this function, and
   *  this variable is the one being returned.
   */
  if (!DECL_LLVM_SET_P (decl)) {
    I = create_alloca_inst(Name, Ty, Size);
    if (Size->VTy == Constant)    /* Fixed size alloca */
      insert_alloca_into_entry_block(Fn, I);
    else
      append_inst(Fn, I);
    SET_DECL_LLVM (decl, D2V(I));
  } else {
    assert(DECL_LLVM(decl)->Ty == llvm_type_get_pointer(Ty) &&
           "Incompatible types!");
  }
}


/* Emit code to perform the initialization of a declaration DECL.  */
static void llvm_expand_decl_init (llvm_function *Fn, tree decl) {
  int was_used = TREE_USED (decl);

  /* If this is a CONST_DECL, we don't have to generate any code.  Likewise
     for static decls.  */
  if (TREE_CODE (decl) == CONST_DECL
      || TREE_STATIC (decl))
    return;

  /* Compute and store the initial value now: "If this variable is initialized
   * (but does not require a constructor), the DECL_INITIAL will be an
   * expression for the initializer. The initializer should be evaluated, and a
   * bitwise copy into the variable performed. If the DECL_INITIAL is the
   * error_mark_node, there is an initializer, but it is given by an explicit
   * statement later in the code; no bitwise copy is required."
   */
  if (DECL_INITIAL (decl) == error_mark_node) {
    enum tree_code code = TREE_CODE (TREE_TYPE (decl));
    
    if (code == INTEGER_TYPE || code == REAL_TYPE || code == ENUMERAL_TYPE
        || code == POINTER_TYPE || code == REFERENCE_TYPE)
      llvm_expand_assignment(Fn, decl,
                             convert(TREE_TYPE(decl), integer_zero_node), 0);
  } else if (DECL_INITIAL(decl) && TREE_CODE(DECL_INITIAL(decl)) != TREE_LIST) {
    llvm_expand_assignment(Fn, decl, DECL_INITIAL(decl), 0);
  }

  /* Don't let the initialization count as "using" the variable.  */
  TREE_USED (decl) = was_used;
}


/* CLEANUP is an expression to be executed at exit from this binding contour;
   for example, in C++, it might call the destructor for this variable.

   We wrap CLEANUP in an UNSAVE_EXPR node, so that we can expand the CLEANUP
   multiple times, and have the correct semantics.  This happens in exception
   handling, for gotos, returns, breaks that leave the current scope.

   If CLEANUP is nonzero and DECL is zero, we record a cleanup that is not
   associated with any particular variable.  */

static int llvm_expand_decl_cleanup(llvm_function *Fn, tree decl, tree cleanup){
  llvm_nesting *thisblock = Fn->ExpandInfo->InnermostBlockScope;
  tree *cleanups = &thisblock->x.block.cleanups;

  /* Error if we are not in any block.  */
  assert(thisblock != 0);

  /* Nothing to do if there is no cleanup */
  if (cleanup == 0) return 1;

  /* Add the unsaved cleanup to the cleanup list */
  *cleanups = tree_cons(decl, unsave_expr(cleanup), *cleanups);
  return 1;
}


/* Like llvm_expand_decl_cleanup, but maybe only run the cleanup if an exception
   is thrown.  */
static int llvm_expand_decl_cleanup_eh(llvm_function *Fn, tree decl,
                                       tree cleanup, int eh_only) {
  int ret = llvm_expand_decl_cleanup (Fn, decl, cleanup);
  if (cleanup && ret) {
    tree node = Fn->ExpandInfo->InnermostBlockScope->x.block.cleanups;
    CLEANUP_EH_ONLY (node) = eh_only;
  }
  return ret;
}




/* Let the back-end know about DECL.  */
static void llvm_emit_local_var (llvm_function *Fn, tree decl) {
  if (DECL_C_HARD_REGISTER (decl)) {
    LLVM_TODO_TREE(decl);
#if 0
    /* The user specified an assembler name for this variable.
       Set that up now.  */
    rest_of_decl_compilation
      (decl, IDENTIFIER_POINTER (DECL_ASSEMBLER_NAME (decl)),
       /*top_level=*/0, /*at_end=*/0);
#endif
  }
  llvm_expand_decl (Fn, decl);
    
  /* Actually do the initialization.  */
  if (stmts_are_full_exprs_p ())    /* Provide a scope C++ temporaries */
    llvm_expand_start_bindings(Fn);

  llvm_expand_decl_init (Fn, decl);

  if (stmts_are_full_exprs_p ())
    llvm_expand_end_bindings(Fn, 0);
}

static void llvm_expand_expr_stmt_value(llvm_function *Fn, tree exp,
                                        int isLast) {
  llvm_value *Val, *DestLoc = 0;

  /* If EXP is of function type and we are expanding statements for
     value, convert it to pointer-to-function.  */
  if (TREE_CODE (TREE_TYPE (exp)) == FUNCTION_TYPE)
    exp = build1 (ADDR_EXPR, build_pointer_type (TREE_TYPE (exp)), exp);

  if (isLast && llvm_type_is_composite(llvm_type_get_from_tree(TREE_TYPE(exp))))
    DestLoc = Fn->ExpandInfo->last_expr_value_location;

  Val = llvm_expand_expr(Fn, exp, DestLoc);

  /* Keep track of the last EXPR_STMT expanded so that STMT_EXPR blocks ({...})
   * can retrieve this value and use it as _their_ return value 
   */
  Fn->ExpandInfo->last_expr_value = Val;
}

/* Generate the RTL for EXPR, which is an EXPR_STMT. */
static void genllvm_expr_stmt(llvm_function *Fn, tree expr, int isLast) {
  if (expr == 0) return;

  if (stmts_are_full_exprs_p ())    /* Provide a scope for C++ temporaries */
    llvm_expand_start_bindings(Fn);
  
  if (expr != error_mark_node)
    llvm_expand_expr_stmt_value(Fn, expr, isLast);
  
  if (stmts_are_full_exprs_p ())
    llvm_expand_end_bindings(Fn, 0);
}

/* Create LLVM code for the local static variable decl. */
static void make_llvm_for_local_static(tree decl) {
  const char *asmspec = NULL;

  /* If we inlined this variable, we could see it's declaration
     again.  */
  if (TREE_ASM_WRITTEN (decl))
    return;

  /* If the DECL_ASSEMBLER_NAME is not the same as the DECL_NAME, then
     either we already created RTL for this DECL (and since it was a
     local variable, its DECL_ASSEMBLER_NAME got hacked up to prevent
     clashes with other local statics with the same name by a previous
     call to make_decl_rtl), or the user explicitly requested a
     particular assembly name for this variable, using the GNU
     extension for this purpose:

       int i asm ("j");

     There's no way to know which case we're in, here.  But, it turns
     out we're safe.  If there's already RTL, then
     rest_of_decl_compilation ignores the ASMSPEC parameter, so we
     may as well not pass it in.  If there isn't RTL, then we didn't
     already create RTL, which means that the modification to
     DECL_ASSEMBLER_NAME came only via the explicit extension.  */
  if (DECL_ASSEMBLER_NAME (decl) != DECL_NAME (decl)
      && !DECL_RTL_SET_P (decl))
    asmspec = IDENTIFIER_POINTER (DECL_ASSEMBLER_NAME (decl));

  rest_of_decl_compilation(decl, asmspec, 0/*top_level*/, 0/*at_end*/);

  /* Forward declarations for nested functions are not "external",
     but we need to treat them as if they were.  */
  if (TREE_STATIC (decl) || DECL_EXTERNAL (decl)
      || TREE_CODE (decl) == FUNCTION_DECL)
    {
      if (asmspec)
	llvm_make_decl_llvm(decl, asmspec);

      /* Don't output anything when a tentative file-scope definition
	 is seen.  But at end of compilation, do output code for them.  */
      if (!DECL_DEFER_OUTPUT (decl))
	assemble_variable (decl, 0, 0, 0);
    }
}


/* Generate LLVM code for T, which is a DECL_STMT.  */
static void genllvm_decl_stmt(llvm_function *F, tree t) {
  tree decl;
  decl = DECL_STMT_DECL (t);
  /* If this is a declaration for an automatic local
     variable, initialize it.  Note that we might also see a
     declaration for a namespace-scope object (declared with
     `extern').  We don't have to handle the initialization
     of those objects here; they can only be declarations,
     rather than definitions.  */
  if (TREE_CODE (decl) == VAR_DECL) {
    if (!TREE_STATIC (decl) && !DECL_EXTERNAL (decl)) {
      /* Let the back-end know about this variable.  */
      if (!anon_aggr_type_p (TREE_TYPE (decl))) {
        llvm_emit_local_var (F, decl);
      } else {
        /* LLVM: See info about lhd_tree_inlining_anon_aggr_type_p */
        LLVM_TODO_TREE(t);
        expand_anon_union_decl (decl, NULL_TREE, 
                                DECL_ANON_UNION_ELEMS (decl));
      }
    } else if (TREE_STATIC (decl)) {
      make_llvm_for_local_static(decl);
    }
  } else if (TREE_CODE (decl) == LABEL_DECL 
             && C_DECLARED_LABEL_FLAG (decl)) {
    LLVM_TODO_TREE(decl);
    declare_nonlocal_label (decl);
  } else if (lang_expand_decl_stmt) {
    LLVM_TODO_TREE(t);
    (*lang_expand_decl_stmt) (t);
  }
}

/* Generate LLVM for the statement T, its substatements, and any other
   statements at its nesting level.  */
void llvm_expand_stmt(llvm_function *Fn, tree t) {
  if (errorcount || sorrycount)
    return;  /* Don't do anything if an error has occurred. */

  while (t && t != error_mark_node) {
    /* Set up context appropriately for handling this statement.  */
    int saved_stmts_are_full_exprs_p = stmts_are_full_exprs_p ();
    prep_stmt (t);

    switch (TREE_CODE (t)) {
    case FILE_STMT:
      input_filename = FILE_STMT_FILENAME (t);
      break;

    case RETURN_STMT:
      genllvm_return_stmt (Fn, RETURN_STMT_EXPR(t));
      break;
      
    case EXPR_STMT:
      genllvm_expr_stmt(Fn, EXPR_STMT_EXPR(t),
                        TREE_CHAIN (t) == NULL
                        || (TREE_CODE (TREE_CHAIN (t)) == SCOPE_STMT
                            && TREE_CHAIN (TREE_CHAIN (t)) == NULL));
      break;

    case DECL_STMT:
      genllvm_decl_stmt(Fn, t);
      break;

    case FOR_STMT:
      genllvm_for_stmt (Fn, t);
      break;
      
    case WHILE_STMT:
      genllvm_while_stmt(Fn, t);
      break;

    case DO_STMT:
      genllvm_do_stmt(Fn, t);
      break;

    case IF_STMT:
      genllvm_if_stmt(Fn, t);
      break;

    case COMPOUND_STMT:
      llvm_expand_stmt(Fn, COMPOUND_BODY(t));
      break;

    case BREAK_STMT:
      if (!llvm_expand_exit_something(Fn))
        error ("break statement not within loop or switch");
      break;
      
    case CONTINUE_STMT:
      if (!llvm_expand_continue_loop(Fn, 0))
        error ("continue statement not within a loop");   
      break;

    case SWITCH_STMT:
      genllvm_switch_stmt(Fn, t);
      break;
      
    case CASE_LABEL:
      genllvm_case_label(Fn, t);
      break;

    case LABEL_STMT:
      llvm_expand_label(Fn, LABEL_STMT_LABEL(t));
      break;

    case GOTO_STMT:
      genllvm_goto_stmt(Fn, GOTO_DESTINATION (t));
      break;

    case SCOPE_STMT: {
      int saved = stmts_are_full_exprs_p ();
      prep_stmt (t);
      genllvm_scope_stmt(Fn, t);
      current_stmt_tree ()->stmts_are_full_exprs_p = saved;
      break;
    }

    case CLEANUP_STMT:
      genllvm_decl_cleanup(Fn, t);
      break;

    case ASM_STMT:
      error("LLVM does not yet support inline assembly!  Code: '%s'",
            TREE_STRING_POINTER(ASM_STRING(t)));
      break;

    default: {
      extern void lhd_llvm_expand_stmt(llvm_function *, tree);
      if (lang_hooks.llvm_expand_stmt != lhd_llvm_expand_stmt)
        (*lang_hooks.llvm_expand_stmt)(Fn, t);
      else
        LLVM_TODO_TREE(t);
      break;
    }
    }

    /* Restore saved state */
    current_stmt_tree()->stmts_are_full_exprs_p = saved_stmts_are_full_exprs_p;
    
    /* Go on to the next statement in this scope */
    t = TREE_CHAIN(t);
  }
}

/*===----------------------------------------------------------------------===**
                        ... Expression Expansion ...
 *===----------------------------------------------------------------------===*/

/* ReadBitField - Given a pointer to a value Src, read the bitfield from
 * BitStart to BitSize.
 */
static llvm_value *ReadBitField(llvm_function *Fn, llvm_value *Src,
                                unsigned BitStart, unsigned BitSize) {
  /* Mask the bits out by shifting left first, then shifting right.  The
   * LLVM optimizer will turn this into an AND if this is an unsigned
   * expression.
   */
  unsigned ValSize = llvm_type_get_size(Src->Ty)*8;
  llvm_value *Idx;

  if (BitSize == 0) return Src;   /* Not a bitfield reference */
  if (BitStart+BitSize != ValSize) {
    Idx = llvm_constant_new_integral(UByteTy,
                                     ValSize-(BitStart+BitSize));
    Src = append_inst(Fn, create_binary_inst("tmp", O_Shl, Src, Idx));
  }
  
  Idx = llvm_constant_new_integral(UByteTy, ValSize-BitSize);
  return append_inst(Fn, create_binary_inst("tmp", O_Shr, Src, Idx));
}

static llvm_value *WriteBitField(llvm_function *Fn, llvm_value *Src,
                                 llvm_value *Ptr,
                                 unsigned BitStart, unsigned BitSize,
                                 int isVolatile) {
  llvm_value *OldVal;
  llvm_type *ResultType;

  /* Get a mask of all ones of the right size */
  long long Mask = (1LL << BitSize)-1;
  /* Shift it over to the right place. */
  Mask <<= BitStart;

  if (BitSize == 0) return Src;
  
  /* If we are not storing starting at the zero'th bit, emit a shift of the
   * computed value.
   */
  if (BitStart) {
    llvm_value *Idx = llvm_constant_new_integral(UByteTy, BitStart);
    Src = append_inst(Fn, create_binary_inst("tmp", O_Shl, Src, Idx));
  }

  ResultType = GET_POINTER_TYPE_ELEMENT(Ptr->Ty);

  /* Mask off any upper bits of the value we computed, but don't want. */
  if (BitStart + BitSize != llvm_type_get_size(ResultType)) {
    /* Make an LLVM value for the constant. */
    llvm_value *MaskVal = llvm_constant_new_integral(ResultType, Mask);
    Src = append_inst(Fn, create_binary_inst("tmp", O_And, Src, MaskVal));
  }
  
  /* Now emit a load of the old lvalue. */
  OldVal = append_inst(Fn, create_load_inst("tmp", Ptr, isVolatile));
  
  /* Mask out the bits we will be replacing. */
  {
    llvm_value *MaskVal = llvm_constant_new_integral(ResultType, ~Mask);
    OldVal = append_inst(Fn, create_binary_inst("tmp", O_And, OldVal,
                                                MaskVal));
  }
  
  /* The final value computed is an 'or' of these two values. */
  return append_inst(Fn, create_binary_inst("tmp", O_Or, OldVal, Src));
}


/* llvm_store_expr - Store the expression computed by from into the lvalue
 * specified by Dest.  If COMPVAL is not null, use it to return the value being
 * stored.  If BITSTART and BITSIZE are not null (and BITSIZE is not zero), they
 * specify a slice of the value that should be updated.
 */
static void llvm_store_expr(llvm_function *Fn, tree From, llvm_value *Dest,
                            llvm_value **CompVal, unsigned BitStart,
                            unsigned BitSize, int isVolatile) {
  llvm_type *ResultType = GET_POINTER_TYPE_ELEMENT(Dest->Ty);
  if (!llvm_type_is_composite(ResultType)) {
    llvm_value *Val = llvm_expand_expr(Fn, From, 0);
    
    /* If expand was not able to provide the correct type, cast now */
    Val = cast_if_type_not_equal(Fn, Val, ResultType);
    if (CompVal) *CompVal = Val;
    
    /* Copy the value computed into the destination.  If this is not a bitfield,
     * this is just a store, otherwise we need to emit a load, some masking,
     * then a store.
     */
    Val = WriteBitField(Fn, Val, Dest, BitStart, BitSize, isVolatile);

    append_inst(Fn, create_store_inst(Val, Dest, isVolatile));

  } else {
    /* Expand the RHS into the appropriate location directly. */
    llvm_value *Val = llvm_expand_expr(Fn, From, Dest);
    if (CompVal) *CompVal = 0;
    assert(Val == 0 && "Structure value returned a value??");
    assert(!BitSize && "Store of aggregate into a bitfield??");
  }
}


/* llvm_expand_assignment - Expand an assignment that stores the value of FROM
 *  into TO.  Returns an llvm_value* for the address of TO, which must be an
 *  lvalue.  If CompVal is not null, use it to return the value that is actually
 *  calculated if an lvalue is not desired.
 */
static llvm_value *llvm_expand_assignment(llvm_function *Fn, tree to,
                                          tree from, llvm_value **CompVal) {
  llvm_value *lvalue_addr;
  unsigned BitfieldStart = 0, BitfieldSize = 0;

  /* Crash if the lhs of the assignment was erroneous.  */
  assert(TREE_CODE (to) != ERROR_MARK);

  /* Assignment of a structure component needs special treatment if the
     structure component's rtx is not simply a MEM (for example, it is a
     bitfield.  This should be handled here: FIXME! */
  assert(TREE_CODE(to) != BIT_FIELD_REF);

  /* Expand the l-value address to get the address to store to. */
  lvalue_addr = llvm_expand_lvalue_expr(Fn, to, &BitfieldStart, &BitfieldSize);

  /* Compute FROM and store the value in the lvalue we got.  */
  llvm_store_expr(Fn, from, lvalue_addr, CompVal, BitfieldStart, BitfieldSize,
                  TYPE_VOLATILE(TREE_TYPE(to)));
  return lvalue_addr;
}

/* PassStructureByValue - This is used to pass a structure argument by value
   into a callee.
*/
static unsigned PassStructureByValue(llvm_function *Fn, llvm_value *ArgAddr,
                                     llvm_instruction *Call,
                                     llvm_type *CalledFuncType,
                                     unsigned ArgOffset, unsigned NumArgs) {
  llvm_type *ValTy = GET_POINTER_TYPE_ELEMENT(ArgAddr->Ty);
  if (!llvm_type_is_composite(ValTy)) {
    /* Finally got down to a simple scalar value.  Load it out. */
    llvm_value *Val = append_inst(Fn, create_load_inst("tmp", ArgAddr, 0));
    Call->Operands[NumArgs+ArgOffset] = Val;
    CalledFuncType->Elements[1+NumArgs] = Val->Ty;
    return NumArgs+1;
  } else {
    unsigned i, e;
    for (i = 0, e = llvm_type_get_composite_num_elements(ValTy); i != e; ++i) {
      llvm_value *Element = llvm_constant_new_integral(ValTy->ID == StructTyID ?
                                                       UByteTy : LongTy, i);
      llvm_value *Addr = append_inst(Fn, create_gep3(ArgAddr,
                                             llvm_constant_long_0, Element));
      NumArgs = PassStructureByValue(Fn, Addr, Call, CalledFuncType,
                                     ArgOffset, NumArgs);
    }
    return NumArgs;
  }
}

static llvm_value *llvm_expand_call_of(llvm_function *Fn, llvm_value *Callee,
                                       tree exp, llvm_value *DestLoc) {
  unsigned NumArgs = 0;
  tree arg;
  llvm_instruction *Call;
  llvm_type *FnType;
  llvm_type *CallRetTy = llvm_type_get_from_tree(TREE_TYPE(exp));

  /* Determine if we need to generate an invoke instruction (instead of a simple
     call) and if so, what the exception destination will be... */
  llvm_basicblock *ExceptBlock = 0;
  unsigned ArgOffset;
  int FunctionMatches = 1;
  llvm_type *CalledFuncType;

  /* Check to see if this is an intrinsic.  If so, do not turn it into an
   * invoke!
   */
  if ((Callee->VTy != Function ||
       Callee->Name[0] != 'l' || Callee->Name[1] != 'l' || 
       Callee->Name[2] != 'v' || Callee->Name[3] != 'm' || 
       Callee->Name[4] != '.')) {
    /* If this function call can throw, see if we need a landing pad */
    if (!TREE_NOTHROW(exp)) {
      if (Fn->ExpandInfo->ThrownExceptionsCallTerminate)
        ExceptBlock = get_terminate_block(Fn);
      else
        ExceptBlock = get_invoke_except_dest(Fn);
    }
  }

  ArgOffset = ExceptBlock ? 3 : 1;  /* Invoke has 2 extra args */

  /* If the callee returns a structure, pass as the first argument, and call
     returns void. */
  if (llvm_type_is_composite(CallRetTy)) {
    if (!CALL_EXPR_HAS_RETURN_SLOT_ADDR(exp)) {
      if (DestLoc == 0) {
        /* If there is no return location specified for the result of the call,
           we need to make a temporary location to capture the return result. */
        DestLoc = D2V(make_temporary_alloca(Fn, CallRetTy));
      }
      assert(llvm_type_get_pointer(CallRetTy) == DestLoc->Ty);
      NumArgs++;
    }
    CallRetTy = VoidTy;
  } else {
    assert(!DestLoc &&
           "Dest location specified, but call doesn't return structure!");
  }

  /* Loop over the CALL_EXPR, counting the number of arguments passed in... */
  for (arg = TREE_OPERAND(exp, 1); arg; arg = TREE_CHAIN(arg)) {
    llvm_type *Ty = llvm_type_get_from_tree(TREE_TYPE(TREE_VALUE(arg)));
    NumArgs += llvm_type_get_num_recursive_elements(Ty);
  }
  
  Call = llvm_instruction_new(CallRetTy, CallRetTy != VoidTy ? "tmp" : "",
                              ExceptBlock ? O_Invoke : O_Call,
                              NumArgs+ArgOffset);
  Call->Operands[0] = Callee;

  FnType = GET_POINTER_TYPE_ELEMENT(Call->Operands[0]->Ty);

  /* Construct the function type that the function call expects... */
  CalledFuncType = llvm_type_create_function(NumArgs, CallRetTy);
                                       
  if (CallRetTy != GET_FUNCTION_TYPE_RETURN(FnType))
    FunctionMatches = 0;  /* The function ptr type doesn't match call! */

  NumArgs = 0;
  /* Returns a structure implicitly by value? */
  if (DestLoc && !CALL_EXPR_HAS_RETURN_SLOT_ADDR(exp)) {
    llvm_type *ArgTy = 0;
    if (FnType->NumElements > 1)
      ArgTy = GET_FUNCTION_TYPE_ARGUMENT(FnType, 0);
    else if (!FnType->x.Function.isVarArg)
      FunctionMatches = 0;
    DestLoc = cast_if_type_not_equal(Fn, DestLoc, ArgTy);
    Call->Operands[ArgOffset] = DestLoc;
    CalledFuncType->Elements[1] = DestLoc->Ty;
    NumArgs++;
  }

  /* Loop over the arguments, expanding them and adding them to the call inst */
  for (arg = TREE_OPERAND(exp, 1); arg; arg = TREE_CHAIN(arg)) {
    llvm_type *ArgTy = 0;
    llvm_value *ArgVal;
    llvm_type *ActualArgTy =llvm_type_get_from_tree(TREE_TYPE(TREE_VALUE(arg)));

    if (NumArgs < FnType->NumElements-1)
      ArgTy = GET_FUNCTION_TYPE_ARGUMENT(FnType, NumArgs);
    else if (!FnType->x.Function.isVarArg)
      FunctionMatches = 0;

    if (!ArgTy) ArgTy = ActualArgTy;

    /* If this argument is a structure passed by value... */
    if (llvm_type_is_composite(ActualArgTy)) {
      /* Get the address of the parameters passed in. */
      llvm_value *ArgAddr = llvm_expand_lvalue_expr(Fn, TREE_VALUE(arg), 0, 0);
      assert(ActualArgTy == GET_POINTER_TYPE_ELEMENT(ArgAddr->Ty));
      NumArgs = PassStructureByValue(Fn, ArgAddr, Call, CalledFuncType,
                                     ArgOffset, NumArgs);
    } else {                /* Otherwise it is a simple scalar argument. */
      ArgVal = llvm_expand_expr(Fn, TREE_VALUE(arg), 0);
      if (ArgTy)
        ArgVal = cast_if_type_not_equal(Fn, ArgVal, ArgTy);
      Call->Operands[NumArgs+ArgOffset] = ArgVal;
      CalledFuncType->Elements[1+NumArgs] = ArgVal->Ty;
      ++NumArgs;
    }
  }

  CalledFuncType = llvm_type_get_cannonical_version(CalledFuncType);
  if (!FunctionMatches) {
    /* If the function pointer argument is not compatible with the arguments
     * being passed into the call, cast the function pointer.
     */
    Call->Operands[0] = cast_if_type_not_equal(Fn, Call->Operands[0],
                                         llvm_type_get_pointer(CalledFuncType));
  }

  append_inst(Fn, Call);

  if (ExceptBlock) {
    llvm_basicblock *NormalDest = llvm_basicblock_new("invoke_cont");
    Call->Operands[1] = D2V(NormalDest);

    if (!Fn->ExpandInfo->ThrownExceptionsCallTerminate) {
      llvm_basicblock *CleanupDest = llvm_basicblock_new("invoke_catch");
      Call->Operands[2] = D2V(CleanupDest);
      llvm_emit_label(Fn, CleanupDest);

      /* a block for cleanups */
      llvm_expand_goto_internal(Fn, 0, ExceptBlock, 0, 1);
    } else {    /* This should just go directly to the terminate block */
      Call->Operands[2] = D2V(ExceptBlock);
    }
    llvm_emit_label(Fn, NormalDest);
  }

  return D2V(Call)->Ty != VoidTy ? D2V(Call) : 0;
}

/* llvm_expand_dummy_return - output a return instruction so that the optimizer
 * knows that control flow doesn't reach here.  Unless elide_new_block is set,
 * this also adds a block immediately after the return.
 */
static void llvm_expand_dummy_return(llvm_function *Fn, bool elide_new_block) {
  llvm_type *RetTy =
    GET_FUNCTION_TYPE_RETURN(GET_POINTER_TYPE_ELEMENT(G2V(Fn)->Ty));
  if (RetTy != VoidTy) {
    llvm_instruction *Ret = llvm_instruction_new(VoidTy, "", O_Ret, 1);
    Ret->Operands[0] = llvm_constant_get_null(RetTy);
    append_inst(Fn, Ret);
  } else {
    append_inst(Fn, llvm_instruction_new(VoidTy, "", O_Ret, 0));
  }

  if (!elide_new_block) {
    /* Start a new block so that if statements are emitted after the return,
     * that they will have the correct "current block".
     */
    llvm_emit_label(Fn, llvm_basicblock_new("dead_block"));
  }
}

/* llvm_expand_call - This is _much_ simpler than expand_call  */
static llvm_value *llvm_expand_call(llvm_function *Fn, tree exp,
                                    llvm_value *DestLoc) {
  tree fn = TREE_OPERAND(exp, 0), fndecl;
  llvm_value *Callee = 0, *Result;

  /* Perform necessary processing */
  if ((fndecl = get_callee_fndecl (exp))) {
    (*lang_hooks.mark_addressable) (fndecl);
  
    if (DECL_NAME(fndecl) && IDENTIFIER_POINTER(DECL_NAME(fndecl))) {
      const char *Name = IDENTIFIER_POINTER(DECL_NAME(fndecl));
      unsigned NameLen = IDENTIFIER_LENGTH(DECL_NAME(fndecl));

      /* If this is a call to setjmp, replace the setjmp function itself with
       * the llvm builtin for setjmp...
       */
      if (setjmp_call_p(fndecl)) {
        if (!strcmp(Name+NameLen-9, "sigsetjmp")) {
          static llvm_function *llvm_sigsetjmp = 0;
          if (!llvm_sigsetjmp)
            llvm_sigsetjmp = CreateIntrinsicFunction("llvm.sigsetjmp",
                                                     TREE_TYPE(fndecl));
          Callee = G2V(llvm_sigsetjmp);
        } else if (!strcmp(Name+NameLen-6, "setjmp")) {
          static llvm_function *llvm_setjmp = 0;
          if (!llvm_setjmp)
            llvm_setjmp = CreateIntrinsicFunction("llvm.setjmp",
                                                  TREE_TYPE(fndecl));
          Callee = G2V(llvm_setjmp);
        }

      } else if (longjmp_call_p(fndecl)) {
        if (!strcmp(Name+NameLen-10, "siglongjmp")) {
          static llvm_function *llvm_siglongjmp = 0;
          if (!llvm_siglongjmp)
            llvm_siglongjmp = CreateIntrinsicFunction("llvm.siglongjmp",
                                                      TREE_TYPE(fndecl));
          Callee = G2V(llvm_siglongjmp);
        } else if (!strcmp(Name+NameLen-7, "longjmp")) {
          static llvm_function *llvm_longjmp = 0;
          if (!llvm_longjmp)
            llvm_longjmp = CreateIntrinsicFunction("llvm.longjmp",
                                                   TREE_TYPE(fndecl));
          Callee = G2V(llvm_longjmp);
        }
      }
    }
  }

  if (!Callee)
    Callee = llvm_expand_expr(Fn, fn, 0);
  Result = llvm_expand_call_of(Fn, Callee, exp, DestLoc);

  /* If the function has the volatile bit set, then it is a "noreturn" function.
   * Output a return right after the function to prevent LLVM from thinking that
   * control flow will fall into the subsequent block.
   */
  if (TREE_CODE(fn) == ADDR_EXPR && TREE_THIS_VOLATILE(TREE_OPERAND(fn, 0))) {
    llvm_expand_dummy_return(Fn, 0);
  }

  return Result;
}

/* llvm_expand_increment - expand the code for a pre- or post- increment or
   decrement instruction, returning the appropriate value. */
static llvm_value *llvm_expand_increment(llvm_function *Fn, tree exp,
                                         int isIncrement, int isPre) {
  int isVolatile = TYPE_VOLATILE(TREE_TYPE(TREE_OPERAND(exp, 0)));
  unsigned BitStart = 0, BitSize = 0;
  llvm_value *OpAddr = llvm_expand_lvalue_expr(Fn, TREE_OPERAND(exp, 0),
                                               &BitStart, &BitSize);
  llvm_instruction *I;
  llvm_value *Op = append_inst(Fn, create_load_inst("tmp", OpAddr, isVolatile));
  llvm_value *IV;

  /* If we are incrementing a bitfield, handle the masking and shifting. */
  Op = ReadBitField(Fn, Op, BitStart, BitSize);


  if (Op->Ty->ID == PointerTyID) {
    /* Figure out how much we are incrementing by.  The 1th operand should be
     * the number of bytes to increment.  If we can't figure out what the size
     * is, or if the size is not equal to the size of the pointed-to type, emit
     * a series of pointer unsafe code.
     */
    unsigned TySize = llvm_type_get_size(GET_POINTER_TYPE_ELEMENT(Op->Ty));
    tree Op1 = TREE_OPERAND(exp, 1);
    if (TREE_CODE(Op1) == INTEGER_CST && TREE_INT_CST_LOW(Op1) == TySize) {
      I = llvm_instruction_new(Op->Ty, isIncrement ? "inc" : "dec",
                               O_GetElementPtr, 2);
      I->Operands[0] = Op;
      I->Operands[1] = llvm_constant_new_integral(LongTy, isIncrement ? 1 : -1);
      IV = append_inst(Fn, I);
    } else {
      llvm_type *IntPtrTy = llvm_type_get_size(VoidPtrTy) == 4 ? IntTy : LongTy;
      llvm_value *OpTmp = cast_if_type_not_equal(Fn, Op, IntPtrTy);
      llvm_value *Inc = llvm_expand_expr(Fn, TREE_OPERAND(exp, 1), 0);

      Inc = cast_if_type_not_equal(Fn, Inc, IntPtrTy);
      I = create_binary_inst(isIncrement ? "inc" : "dec",
                             isIncrement ? O_Add : O_Sub, OpTmp, Inc);
      
      IV = append_inst(Fn, I);
      IV = cast_if_type_not_equal(Fn, IV, Op->Ty);
    }
  } else {
    llvm_value *Inc = llvm_expand_expr(Fn, TREE_OPERAND(exp, 1), 0);
    Inc = cast_if_type_not_equal(Fn, Inc, Op->Ty);
    I = create_binary_inst(isIncrement ? "inc" : "dec",
                           isIncrement ? O_Add : O_Sub, Op, Inc);
    IV = append_inst(Fn, I);
  }

  /* If we are incrementing a bitfield, handle the masking and shifting. */
  IV = WriteBitField(Fn, IV, OpAddr, BitStart, BitSize, isVolatile);

  /* Store the final value */
  append_inst(Fn, create_store_inst(IV, OpAddr, isVolatile));

  /* Depending on whether it was a pre- or post- expression, return the right
     value */
  return isPre ? IV : Op;
}


/* llvm_expand_shortcircuit_truth_expr - Expand a TRUTH_ANDIF_EXPR or
   TRUTH_ORIF_EXPR node. */
static llvm_value *llvm_expand_shortcircuit_truth_expr(llvm_function *Fn,
                                                       tree exp) {
  int isAndExpr = TREE_CODE(exp) == TRUTH_ANDIF_EXPR;
  llvm_value *FirstOp = llvm_expand_expr(Fn, TREE_OPERAND(exp, 0), 0);
  llvm_basicblock *FromBlock =llvm_ilist_back(llvm_basicblock, Fn->BasicBlocks);
  llvm_value *SecondOp;
  llvm_basicblock *TestBlock = llvm_basicblock_new("shortcirc_next");
  llvm_basicblock *DoneBlock = llvm_basicblock_new("shortcirc_done");
  llvm_instruction *PHI;

  FirstOp = cast_if_type_not_equal(Fn, FirstOp, BoolTy);
  append_inst(Fn, create_cond_branch(FirstOp, isAndExpr ? TestBlock : DoneBlock,
                                     isAndExpr ? DoneBlock : TestBlock));
  llvm_emit_label(Fn, TestBlock);

  SecondOp = llvm_expand_expr(Fn, TREE_OPERAND(exp, 1), 0);
  SecondOp = cast_if_type_not_equal(Fn, SecondOp, BoolTy);
  TestBlock = llvm_ilist_back(llvm_basicblock, Fn->BasicBlocks);
  
  llvm_emit_label(Fn, DoneBlock);

  /* Add a PHI node to merge together the two computed values */
  PHI = llvm_instruction_new(BoolTy, "shortcirc_val", O_PHINode, 4);
  PHI->Operands[0] = isAndExpr ? llvm_constant_bool_false :
                                 llvm_constant_bool_true;
  PHI->Operands[1] = D2V(FromBlock);
  PHI->Operands[2] = SecondOp;
  PHI->Operands[3] = D2V(TestBlock);
  return cast_if_type_not_equal(Fn, append_inst(Fn, PHI),
                                llvm_type_get_from_tree(TREE_TYPE(exp)));
}


/* llvm_expand_pointer_addsub - Attempt to expand an addition/subtraction of a
 * pointer and a constant into a getelementptr instruction.  If this is not
 * possible, return null.
 */
static llvm_value *llvm_expand_pointer_addsub(llvm_function *Fn, int isAdd,
                                              llvm_value *op0, llvm_value *op1,
                                              llvm_type *DestTy) {
  /* The common case that we want to handle here is when accessing a subobject
   * of a composite type.  In this case, we would get code generated that looks
   * like this:
   *    %T1 = cast %S1* %P1 to %S3*
   *    %P2 = add %S3* %T1, uint 4     <- instruction we are generating
   * But instead, we try to generate code like this:
   *    %T1 = cast %S1* %P1 to %S3*    <- Instruction left for dead
   *    %P2 = getelementptr %S1* %P1, long 0, ubyte 1
   */
  unsigned Value, CurValue;
  unsigned Size;
  unsigned Depth = 0;
  llvm_type *CTy, *OTy;

  /*return 0;    // Used to disabled addsub transformation */

  assert(DestTy->ID == PointerTyID && op0->Ty->ID == PointerTyID);
  if (!isAdd) return 0;   /* Only handle add so far */

  /* Dig through constant-expr casts. */
  if (op1->VTy == ConstantExpr &&
      ((llvm_constant_expr*)op1)->Inst->Opcode == O_Cast)
    op1 = ((llvm_constant_expr*)op1)->Inst->Operands[0];

  if (op1->VTy != Constant) return 0;  /* Only works for constants */
  if (V2C(op1)->Repr[0] < '0' || V2C(op1)->Repr[0] > '9')
    return 0; /* Not a positive numeric constant? */
  Value = llvm_constant_get_integer_val(V2C(op1)); /* Get the constant value */

  while (op0->VTy == Instruction && ((llvm_instruction*)op0)->Opcode == O_Cast)
    op0 = ((llvm_instruction*)op0)->Operands[0]; /* Ignore cast instrs */
  
  while (op0->VTy == ConstantExpr &&         /* Strip off constant expr casts */
         ((llvm_constant_expr*)op0)->Inst->Opcode == O_Cast)
    op0 = ((llvm_constant_expr*)op0)->Inst->Operands[0];

  /* Okay, check to make sure our source is still a pointer. */
  if (op0->Ty->ID != PointerTyID) return 0;
  
  CTy = OTy = GET_POINTER_TYPE_ELEMENT(op0->Ty); /* Get the current type. */
  Size = llvm_type_get_size(CTy);
  if (Size == 0) return 0;

  /* Okay, traverse the type hierarchy now to see if we can reach DestTy at
   * offset Value.
   */
  CurValue = Value % Size; Depth++;  /* Step into the pointer. */
  
  for (; CurValue && llvm_type_is_composite(CTy); Depth++)
    if (CTy->ID == ArrayTyID) {
      CTy = CTy->Elements[0];
      CurValue %= llvm_type_get_size(CTy);
    } else {
      unsigned i;
      assert(CTy->ID == StructTyID && "Unknown composite type!");
      assert(CurValue < llvm_type_get_size(CTy) && "Value out of range!"); 
      for (i = 0; i < CTy->NumElements-1 && 
                  CTy->x.Struct.MemberOffsets[i+1] <= CurValue; ++i)
        /* empty */;
      assert(i < CTy->NumElements && CTy->x.Struct.MemberOffsets[i] <=CurValue);
      CurValue -= CTy->x.Struct.MemberOffsets[i];
      CTy = CTy->Elements[i];
    }
  
  /* Could we aquire the correct offset? */
  if (CurValue == 0) {
    /* Create and construct the appropriate GEP instruction. */
    llvm_instruction *GEP = llvm_instruction_new(llvm_type_get_pointer(CTy),
                                                 "tmp", O_GetElementPtr,
                                                 1+Depth);
    Depth = 0;
    GEP->Operands[Depth++] = op0;
    GEP->Operands[Depth++] = llvm_constant_new_integral(LongTy, Value / Size);
    Value %= Size;
    CTy = OTy;
    while (Value && llvm_type_is_composite(CTy))
      if (CTy->ID == ArrayTyID) {
        unsigned ElSize = llvm_type_get_size(CTy->Elements[0]);
        GEP->Operands[Depth++]=llvm_constant_new_integral(LongTy, Value/ElSize);
        Value %= ElSize;
        CTy = CTy->Elements[0];
      } else {
        unsigned i;
        for (i = 0; i < CTy->NumElements-1 && 
               CTy->x.Struct.MemberOffsets[i+1] <= Value; ++i)
          /* empty */;
        assert(i < CTy->NumElements && CTy->x.Struct.MemberOffsets[i] <= Value);
        Value -= CTy->x.Struct.MemberOffsets[i];
        CTy = CTy->Elements[i];
        GEP->Operands[Depth++] = llvm_constant_new_integral(UByteTy, i);
      }

    /* Now that the pointer has been adjusted by the appropriate amount, convert
     * to the right type.
     */
    return cast_if_type_not_equal(Fn, append_inst(Fn, GEP), DestTy);
  }
  return 0;
}


/* IndexIntoCompositeToByteOffset - Given a pointer to a composite object PTR,
   index into it until we reach the specified offset. */
static llvm_value *IndexIntoCompositeToByteOffset(llvm_function *Fn,
                                                  llvm_value *Ptr,
                                                  unsigned Offset,
                                                  unsigned *ResOffset) {
  llvm_type *ElTy = GET_POINTER_TYPE_ELEMENT(Ptr->Ty);
  assert(Offset < llvm_type_get_size(ElTy) && "Offset out of range!");

  if (!llvm_type_is_composite(ElTy)) {  /* Cannot index into non-composite. */
    return Ptr;
  } else if (ElTy->ID == StructTyID) {
    unsigned Idx;
    for (Idx = 1; Idx < ElTy->NumElements; ++Idx)
      if (ElTy->x.Struct.MemberOffsets[Idx] > Offset)
        break;
    --Idx;
    Offset -= ElTy->x.Struct.MemberOffsets[Idx];
    *ResOffset += ElTy->x.Struct.MemberOffsets[Idx];
    Ptr = append_inst(Fn, create_gep3(Ptr, llvm_constant_long_0,
                                      llvm_constant_new_integral(UByteTy,Idx)));
    return IndexIntoCompositeToByteOffset(Fn, Ptr, Offset, ResOffset);
  } else if (ElTy->ID == ArrayTyID) {
    llvm_type *ArrEl = GET_ARRAY_TYPE_ELEMENT(ElTy);
    unsigned ElSize = llvm_type_get_size(ArrEl);
    unsigned Idx = Offset / ElSize;
    assert(Idx < ElTy->x.Array.Size && "Array idx out of range!");
    Offset -= ElSize*Idx;
    *ResOffset += ElSize*Idx;
    Ptr = append_inst(Fn, create_gep3(Ptr, llvm_constant_long_0,
                                      llvm_constant_new_integral(LongTy,Idx)));
    return IndexIntoCompositeToByteOffset(Fn, Ptr, Offset, ResOffset);
  } else {
    assert(0 && "Unknown composite type!");
  }
}

/* llvm_expand_bitfield_ref - Expand LLVM code for exp, which is a BIT_FIELD_REF
   tree. */
static llvm_value *llvm_expand_bitfield_ref(llvm_function *Fn, tree exp) {
  tree NumBitsT = TREE_OPERAND(exp, 1), FirstBitT = TREE_OPERAND(exp, 2);
  unsigned NumBits, FirstBit, TypeSize;
  llvm_type *ValTy = llvm_type_get_from_tree(TREE_TYPE(TREE_OPERAND(exp, 0)));
  llvm_type *DestTy = llvm_type_get_from_tree(TREE_TYPE(exp));
  llvm_value *Val;

  assert(TREE_CODE(NumBitsT) == INTEGER_CST && 
         TREE_CODE(FirstBitT) == INTEGER_CST &&
         "Non constant bit indexes in BIT_FIELD_REF!");
  assert(TREE_INT_CST_HIGH(NumBitsT) == 0 &&
         TREE_INT_CST_HIGH(FirstBitT) == 0 &&
         "Incredibly large bit field reference!");
  
  NumBits  = TREE_INT_CST_LOW(NumBitsT);
  FirstBit = TREE_INT_CST_LOW(FirstBitT);

  /* If we are indexing into a composite type, figure out which field is being
     addressed. */
  if (llvm_type_is_composite(ValTy)) {
    unsigned ByteOffset = 0;
    llvm_type *PT;
    /* FIXME: This might expand to a bitfield?? */
    Val = llvm_expand_lvalue_expr(Fn, TREE_OPERAND(exp, 0), 0, 0);
    Val = IndexIntoCompositeToByteOffset(Fn, Val, FirstBit/8, &ByteOffset);
    FirstBit -= ByteOffset*8;
    
    /* Figure out what type we are now pointing to... */
    PT = GET_POINTER_TYPE_ELEMENT(Val->Ty);

    /* If we cannot load this value directly (because it is a composite type),
     * if the loaded number of bits would be insufficient, or if the type is not
     * integral, cast the pointer to be a pointer to an integral type of the
     * appropriate size.
     */
    if (llvm_type_get_size(PT)*8 < FirstBit+NumBits ||
        !llvm_type_is_scalar(PT) || !llvm_type_is_integral(PT)) {
      unsigned NewSize = 8;
      llvm_type *NewTy;
      while (NewSize < NumBits)
        NewSize += NewSize;

      NewTy = llvm_type_get_integer(NewSize, llvm_type_is_unsigned(DestTy));
      Val = cast_if_type_not_equal(Fn, Val, llvm_type_get_pointer(NewTy));
    }

    Val = append_inst(Fn, create_load_inst("tmp", Val,
                                           TYPE_VOLATILE(TREE_TYPE(exp))));
    ValTy = Val->Ty;

  } else {
    /* If it is not composite, just get the value directly. */
    Val = llvm_expand_expr(Fn, TREE_OPERAND(exp, 0), 0);
    Val = cast_if_type_not_equal(Fn, Val, ValTy);
  }

  assert(Val && llvm_type_is_integral(Val->Ty) && Val->Ty == ValTy &&
         "Bad bitfield ref!");
  TypeSize = llvm_type_get_size(ValTy)*8; /* Type size in bits */
  
  assert(NumBits+FirstBit <= TypeSize && "BIT_FIELD_REF out of range!");

  if (!TREE_UNSIGNED(exp)) {
    /* First shift left to the top, then shift right to the bottom. */
    unsigned ShiftAmt = TypeSize-(FirstBit+NumBits);
    if (ShiftAmt) {
      llvm_value *Idx = llvm_constant_new_integral(UByteTy, ShiftAmt);
      assert(llvm_type_is_signed(Val->Ty));
      Val = append_inst(Fn, create_binary_inst("tmp", O_Shl, Val, Idx));
      FirstBit += ShiftAmt;
    }
  }
  
  if (FirstBit != 0) {   /* Shift the value right a bit or two. */
    llvm_value *Idx = llvm_constant_new_integral(UByteTy, FirstBit);
    Val = append_inst(Fn, create_binary_inst("tmp", O_Shr, Val, Idx));
    assert(TREE_UNSIGNED(exp) || llvm_type_is_signed(Val->Ty));
  }
  
  /* If we are producing an unsigned value, mask off top bits. */
  if (TREE_UNSIGNED(exp) && NumBits != llvm_type_get_size(DestTy)*8) {
    llvm_value *Mask = llvm_constant_new_integral(Val->Ty,
                                                  (1 << NumBits) - 1);
    assert(NumBits < 32 &&
           "FIXME: This needs to be adjusted to work with 64 bits");
    Val = append_inst(Fn, create_binary_inst("tmp", O_And, Val, Mask));
  }
  return cast_if_type_not_equal(Fn, Val, DestTy);
}



/*===----------------------------------------------------------------------===**
                      ... Expansion of CONSTRUCTOR nodes ...
 *===----------------------------------------------------------------------===*/

/* llvm_expand_constructor_element - This function handles the case of
 * initialization of either a contructor constant element or a constructor value
 * element in a function scope.
 */
static llvm_value *llvm_expand_constructor_element(llvm_function *Fn,
                                                   llvm_value *Target,
                                                   tree value, llvm_type *ElTy,
                                                   llvm_value *IdxExpr,
                                                   int isVolatile) {

  /* If this field is a composite type and we are expanding a constructor
   * into a function, we cannot produce a structure by value.
   */
  if (llvm_type_is_composite(ElTy) && Target) {
    llvm_instruction *OffsetInst
      = create_gep3(Target, llvm_constant_long_0, IdxExpr);

    llvm_value *Offset = append_inst(Fn, OffsetInst);

    if (value) {
      llvm_type *ExpTy = llvm_type_get_from_tree(TREE_TYPE(value));
      if (llvm_type_is_composite(ExpTy))
        llvm_expand_constructor(Fn, value, Offset, isVolatile);
      else {
        llvm_store_expr(Fn, value,
                        cast_if_type_not_equal(Fn, Offset, 
                                               llvm_type_get_pointer(ExpTy)),
                        0, 0, 0, isVolatile);
      }
    } else
      llvm_zero_initialize(Fn, Offset);
    return llvm_constant_long_0;  /* Random non-null pointer */        
  } else if (!value) {               /* Zero initializer */
    return llvm_constant_get_null(ElTy);
  } else if (Fn) {
    /* If ElTy != ReqTy and we have a function body available, just go through
     * memory to make sure the correct conversion occurs.
     */
    llvm_value *Val = llvm_expand_expr(Fn, value, 0);

    if (Val->Ty == ElTy)
      return Val;
    else if (llvm_type_is_integral(Val->Ty) && llvm_type_is_integral(ElTy))
      return cast_if_type_not_equal(Fn, Val, ElTy);
    else {
      /* Allocate one of the types: either one works, but pick the larger one */
      llvm_type *LargerTy =
        llvm_type_get_size(ElTy) > llvm_type_get_size(Val->Ty) ? ElTy : Val->Ty;
      llvm_value *All = D2V(make_temporary_alloca(Fn, LargerTy));
      llvm_value *Tmp;

      /* Store the computed value to memory */
      Tmp = cast_if_type_not_equal(Fn, All, llvm_type_get_pointer(Val->Ty));
      append_inst(Fn, create_store_inst(Val, Tmp, 0));
    
      /* Reload the computed value in the right type */
      Tmp = cast_if_type_not_equal(Fn, All, llvm_type_get_pointer(ElTy));
      return append_inst(Fn, create_load_inst("tmp", Tmp, 0));
    }
  } else if (TREE_CODE(value) == STRING_CST) {
    return D2V(llvm_decode_string_constant(value, GET_ARRAY_TYPE_SIZE(ElTy),
                                           GET_ARRAY_TYPE_ELEMENT(ElTy)));
  } else {
    /* If the type is a scalar, just add a cast. */
    if (llvm_type_is_scalar(ElTy)) {
      return D2V(llvm_expand_constant_expr(value, ElTy));
    } else {
      /* If this is an aggregate type and the source is a scalar, initialize
       * only the first element of the aggregate.
       */
      llvm_type *SourceTy = llvm_type_get_from_tree(TREE_TYPE(value));
      llvm_value *Val = D2V(llvm_expand_constant_expr(value, SourceTy));
      if (Val->Ty == ElTy)
        return Val;

      if (llvm_type_is_scalar(SourceTy)) {
        llvm_value **Elements;

        if (ElTy->ID == ArrayTyID) {
          unsigned i, Size = GET_ARRAY_TYPE_SIZE(ElTy);
          llvm_type *ArrayElTy = GET_ARRAY_TYPE_ELEMENT(ElTy);
          Elements = (llvm_value**)xcalloc(Size, sizeof(llvm_value*));
          
          /* Expand the initializer into the zero'th element. */
          Elements[0] = llvm_expand_constructor_element(Fn, 0, value,
                                                        ArrayElTy, 0, 0);
          
          /* For the rest of the array initializer, expand nulls. */
          for (i = 1; i != Size; ++i)
            Elements[i] = 
              llvm_expand_constructor_element(0, 0, 0, ArrayElTy, 0, 0);
          
        } else if (ElTy->ID == StructTyID) {
          unsigned i, Size = ElTy->NumElements;
          Elements = (llvm_value**)xcalloc(Size, sizeof(llvm_value*));
          
          /* Expand the initializer into the zero'th element. */
          Elements[0] =
            llvm_expand_constructor_element(Fn, 0, value,
                                            GET_STRUCT_TYPE_ELEMENT(ElTy, 0),
                                            0, 0);
          
          /* For the rest of the struct initializer, expand nulls. */
          for (i = 1; i != Size; ++i)
            Elements[i] = 
              llvm_expand_constructor_element(0, 0, 0,
                                              GET_STRUCT_TYPE_ELEMENT(ElTy,i),
                                              0, 0);
          
        } else {
          assert(0 && "Don't know how to expand this!");
        }
        Val = G2V(llvm_constant_aggregate_new(ElTy, Elements));
      } else {
        assert(0 && "Cannot adjust type of aggregate constant initializer!");
      }
      return Val;
    }
  }
}

/* GetFieldOffset - Return the offset (in bits) of a FIELD_DECL in a
 * structure.
 */
static unsigned GetFieldOffset(tree Field) {
  assert(DECL_FIELD_BIT_OFFSET(Field) != 0 && DECL_FIELD_OFFSET(Field) != 0);
  return TREE_INT_CST_LOW(DECL_FIELD_BIT_OFFSET(Field)) +
         TREE_INT_CST_LOW(DECL_FIELD_OFFSET(Field))*8;
}

/* GetDeclSize - Return the size of the declaration, in bits. */
static unsigned GetDeclSize(tree Field) {
  if (DECL_SIZE(Field))
    return TREE_INT_CST_LOW(DECL_SIZE(Field));
  else if (TYPE_SIZE(TREE_TYPE(Field)))
    return TREE_INT_CST_LOW(TYPE_SIZE(TREE_TYPE(Field)));
  else
    return 0; /* Must be something like a "flexible array" member in a struct */
}

/* GetFieldDeclOffset - Given a FIELD_DECL for a struct, LLVM has converted the
 * field to live in some element of the corresponding structure type.  Return
 * the offset from the start of the structure to this structure element.
 */
static unsigned GetFieldDeclOffset(tree FieldDecl) {
  /* First, get the field number... */
  unsigned Idx = llvm_constant_get_integer_val(V2C(DECL_LLVM(FieldDecl)));
  /* Second, get the structure type that contains the field */
  llvm_type *Ty = llvm_type_get_from_tree(DECL_CONTEXT(FieldDecl));
  assert(Ty->ID == StructTyID && "Field not in a struct??");
  assert(Idx < Ty->NumElements && "Invalid structure field number!");
  return Ty->x.Struct.MemberOffsets[Idx];
}

/* llvm_expand_constructor_elements - This function is used to expand EXP (a
 * CONSTRUCTOR node) into a list of values for each field of the structure/array
 * to get.  If FN is not null, this expansion is allowed to generate
 * instructions to compute the values, otherwise, only constant initializers are
 * allowed.
 *
 * This function returns an array which has been populated with all of the
 * values indicated by the constructor.  The Elements array is sized according
 * to the type of the constructor (ie, size = # structure elements or array
 * size), and must be freed by the caller.
 */
static llvm_value **llvm_expand_constructor_elements(llvm_function *Fn,
                                                     llvm_value *target,
                                                     tree exp, int isVolatile) {
  tree type = TREE_TYPE(exp);
  llvm_type *Ty = llvm_type_get_from_tree(type);
  unsigned Size = llvm_type_get_composite_num_elements(Ty);
  llvm_value **Result = (llvm_value**)xcalloc(Size, sizeof(llvm_value*));
  unsigned i;

  if (TREE_CODE(type) == QUAL_UNION_TYPE)
    LLVM_TODO_TREE(exp);

  if (TREE_CODE(type) == RECORD_TYPE || TREE_CODE(type) == UNION_TYPE) {
    tree elt;

    /* Store each element of the constructor into the corresponding field of
       DEST.  */
    for (elt = CONSTRUCTOR_ELTS(exp); elt; elt = TREE_CHAIN(elt))
      if (TREE_PURPOSE(elt)) {                      /* Ignore missing fields. */
        tree field = TREE_PURPOSE (elt);  /* The FIELD_DECL for the field */
        tree value = TREE_VALUE (elt);
        llvm_value *FieldIndex = DECL_LLVM(field);
        unsigned FieldIndexVal = llvm_constant_get_integer_val(V2C(FieldIndex));
        llvm_type *FieldType = GET_STRUCT_TYPE_ELEMENT(Ty, FieldIndexVal);
        unsigned FieldOffset = GetFieldOffset(field);
        unsigned FieldSize = TREE_INT_CST_LOW(DECL_SIZE(field));
        llvm_value *ElVal;
        
        assert(FieldIndex && "Structure isn't laid out by LLVM yet!");
        
        /* Expand out the constructor element value. */
        ElVal = llvm_expand_constructor_element(Fn, target, value, FieldType,
                                                FieldIndex, isVolatile);

        /* If this field does not fill the entire LLVM structure element
         * (because it is part of a bit field), emit the appropriate masking and
         * shift operations now.  This should only occur for integral types
         * (which are the only ones allowed in bitfields).
         */
        FieldOffset -= Ty->x.Struct.MemberOffsets[FieldIndexVal]*8;
        if (FieldOffset ||
            (llvm_type_get_size(FieldType)*8 != FieldSize &&
             TREE_CODE(type) != UNION_TYPE)) {
          assert(llvm_type_is_integral(FieldType) && "Bad bitfield member ty!");
          assert(ElVal->Ty == FieldType && "Types do not agree!");
          
          /* If there is already a value set for this field, mask out any bits
           * that are part of the current field (in case the current field is
           * multiply initialized to different values).  The LLVM stuff should
           * constant propagate these operations.
           */
          if (Result[FieldIndexVal]) {
            long long MaskVal = ~(((1 << FieldSize)-1) << FieldOffset);
            llvm_value *Mask;
            assert(sizeof(long long) == 8 && "Must have 64-bit long long!");

            /* If this is an unsigned type, mask off bits outside the range of
               the data type in question... */
            if (!llvm_type_is_signed(FieldType))
              MaskVal &= (1 << llvm_type_get_size(FieldType))-1;

            Mask = llvm_constant_new_integral(FieldType, MaskVal);
            Result[FieldIndexVal] =
              append_inst(0, create_binary_inst("", O_And,
                                                Result[FieldIndexVal], Mask));
          }

          /* If there is a field offset, we need to shift the computed value by
           * the appropriate amount...
           */
          if (FieldOffset) {
            llvm_value *ShiftVal =
              llvm_constant_new_integral(UByteTy, FieldOffset);
            ElVal = append_inst(0, create_binary_inst("", O_Shl, ElVal,
                                                      ShiftVal));
          }

          /* If there was a previous value for this LLVM element, just "or" the
           * newly computed field into the old value.  Any overlapping bits have
           * already been masked out.
           */
          if (Result[FieldIndexVal])
            ElVal = append_inst(0, create_binary_inst("", O_Or, ElVal,
                                                      Result[FieldIndexVal]));
        }
        
        /* Save the value computed into our result array. */
        Result[FieldIndexVal] = ElVal;
      }

    /* Now we loop over all of the fields in the type, making sure they were
     * initialized, and if not, initializing them with zeros.
     */
    for (i = 0; i != Size; ++i)
      if (Result[i] == 0) {
        llvm_type *FieldType = Ty->Elements[i];
        Result[i] = llvm_expand_constructor_element(Fn, target, 0, FieldType,
                                   llvm_constant_new_integral(UByteTy, i),
                                                    isVolatile);
      }
    
  } else if (TREE_CODE(exp) == STRING_CST) {
    /* Expand a string like an array. */
    unsigned Len = TREE_STRING_LENGTH(exp);
    llvm_type *ElementType = GET_ARRAY_TYPE_ELEMENT(Ty);
    unsigned ElSize = llvm_type_get_size(ElementType);

    if (Size < Len/ElSize) Len = Size*ElSize;   /* min(Size,Len) */

    switch (ElSize) {
    case 1: {
      const char *Str = TREE_STRING_POINTER(exp);
      for (i = 0; i < Len; ++i)
        Result[i] = llvm_constant_new_integral(ElementType, Str[i]);
      break;
    }
    case 2: {
      const short *Str = (const short*)TREE_STRING_POINTER(exp);
      for (i = 0; i < Len/2; ++i)
        Result[i] = llvm_constant_new_integral(ElementType, Str[i]);
      break;
    }
    case 4: {
      const int *Str = (const int*)TREE_STRING_POINTER(exp);
      for (i = 0; i < Len/4; ++i)
        Result[i] = llvm_constant_new_integral(ElementType, Str[i]);
      break;
    }
    default:  assert(0 && "Unknown character type in STRING_CST!");
    }

    for (; i < Size; ++i)         /* Null suffix */
      Result[i] = llvm_constant_new_integral(ElementType, 0);

  } else if (TREE_CODE(type) == ARRAY_TYPE || TREE_CODE(type) == VECTOR_TYPE) {
    tree elt;
    tree domain = TYPE_DOMAIN (type);
    llvm_type *FieldType = GET_ARRAY_TYPE_ELEMENT(Ty);
    HOST_WIDE_INT minelt = 0;

    /* Vectors are like arrays, but the domain is stored via an array
       type indirectly.  */
    if (TREE_CODE (type) == VECTOR_TYPE) {
      /* Note that although TYPE_DEBUG_REPRESENTATION_TYPE uses
         the same field as TYPE_DOMAIN, we are not guaranteed that
         it always will.  */
      domain = TYPE_DEBUG_REPRESENTATION_TYPE (type);
      domain = TYPE_DOMAIN (TREE_TYPE (TYPE_FIELDS (domain)));
    }

    /* If we have constant lower bound for the range of the type, get it.  */
    if (TYPE_MIN_VALUE (domain) && host_integerp (TYPE_MIN_VALUE (domain), 0))
      minelt = tree_low_cst (TYPE_MIN_VALUE (domain), 0);

    /* Store each element of the constructor into the corresponding element of
       TARGET, determined by counting the elements.  */
    for (elt = CONSTRUCTOR_ELTS (exp); elt; elt = TREE_CHAIN (elt)) {
      tree value = TREE_VALUE (elt);
      tree index = TREE_PURPOSE (elt);

      if (index && TREE_CODE(index) == RANGE_EXPR) {
        LLVM_TODO_TREE(exp);
      } else {
        int FieldOffset;
        if (index == 0)
          index = ssize_int(1);
        if (minelt)
          index = convert (ssizetype,
                           fold (build (MINUS_EXPR, index,
                                        TYPE_MIN_VALUE (domain))));
        assert(TREE_CODE(index) == INTEGER_CST);
        FieldOffset = TREE_INT_CST_LOW(index);

        Result[FieldOffset] =
          llvm_expand_constructor_element(Fn, target, value, FieldType,
                               llvm_constant_new_integral(LongTy, FieldOffset),
                                          isVolatile);
      }
    }
      
    for (i = 0; i != Size; ++i)
      if (Result[i] == 0)
        Result[i] = llvm_expand_constructor_element(Fn, target, 0, FieldType,
                                      llvm_constant_new_integral(LongTy, i),
                                                    isVolatile);

  } else
    abort ();  

  
  return Result;
}


/* llvm_expand_constructor - Store the value of a CONSTRUCTOR (exp) into the
 * LLVM value (Dest).  Dest is guaranteed to be a pointer to the appropriate
 * memory location.
 */
static void llvm_expand_constructor(llvm_function *Fn, tree exp,
                                    llvm_value *target, int isVolatile) {
  llvm_type *Ty = llvm_type_get_from_tree(TREE_TYPE(exp));
  unsigned Size = llvm_type_get_composite_num_elements(Ty);
  llvm_value **Elements = llvm_expand_constructor_elements(Fn, target, exp,
                                                           isVolatile);
  llvm_instruction *OffsetInst;
  llvm_value *Offset;
  unsigned i;

  if (Ty->ID == StructTyID) {
    for (i = 0; i != Size; ++i)
      /* Composite elements handled already */
      if (!llvm_type_is_composite(Ty->Elements[i])) {
        /* Make a getelementptr instruction that addresses the field */
        OffsetInst = create_gep3(target, llvm_constant_long_0,
                                 llvm_constant_new_integral(UByteTy, i));
        Offset = append_inst(Fn, OffsetInst);   /* Add it to the program */
        append_inst(Fn, create_store_inst(Elements[i], Offset, isVolatile));
      }

  } else {
    assert(Ty->ID == ArrayTyID && "Not struct or array type?");

    /* Composite elements handled already */
    if (!llvm_type_is_composite(Ty->Elements[0])) {
      for (i = 0; i != Size; ++i) {
        /* Make a getelementptr instruction that addresses the field */
        OffsetInst = create_gep3(target, llvm_constant_long_0,
                                 llvm_constant_new_integral(LongTy, i));
        Offset = append_inst(Fn, OffsetInst);   /* Add it to the program */
        append_inst(Fn, create_store_inst(Elements[i], Offset, isVolatile));
      }

    }
  }

  free(Elements);
}

static llvm_constant *llvm_expand_get_constructor_constant(tree exp) {
  llvm_type *Ty = llvm_type_get_from_tree(TREE_TYPE(exp));
  llvm_value **Elements = llvm_expand_constructor_elements(0, 0, exp, 0);
  return G2C(llvm_constant_aggregate_new(Ty, Elements));
}

static llvm_value *llvm_expand_minmaxabs_expr(llvm_function *Fn, tree exp,
                                              llvm_value *op0, llvm_value *op1){
  llvm_basicblock *Stub = llvm_basicblock_new("minmaxabs");
  llvm_basicblock *Cont = llvm_basicblock_new("cont");
  llvm_basicblock *FromBlock =llvm_ilist_back(llvm_basicblock, Fn->BasicBlocks);
  enum InstOpcode Opcode;
  llvm_value *Compare;
  llvm_instruction *PHI;

  assert(op0->Ty == op1->Ty && "Operands must have same type!");
  assert(llvm_type_is_scalar(op0->Ty) && "Min/Max/Abs require scalar type!");

  switch (TREE_CODE(exp)) {
  case ABS_EXPR: Opcode = O_SetGE; break;
  case MAX_EXPR: Opcode = O_SetGE; break;
  case MIN_EXPR: Opcode = O_SetLE; break;
  default: abort();      
  }

  /* FIXME: This could use a conditional move instead of branches! */
  Compare = append_inst(Fn, create_binary_inst("comp", Opcode, op0, op1));
  append_inst(Fn, create_cond_branch(Compare, Cont, Stub));
  llvm_emit_label(Fn, Stub);
  
  if (TREE_CODE(exp) == ABS_EXPR)
    op1 = append_inst(Fn, create_binary_inst("abs", O_Sub, op1, op0));
  
  append_inst(Fn, create_uncond_branch(Cont));
  llvm_emit_label(Fn, Cont);
  PHI = llvm_instruction_new(op0->Ty, "minmax", O_PHINode, 4);
  PHI->Operands[0] = op0;
  PHI->Operands[1] = D2V(FromBlock);
  PHI->Operands[2] = op1;
  PHI->Operands[3] = D2V(Stub);
  return append_inst(Fn, PHI);
}

static llvm_function *CreateIntrinsicFnWithType(const char *Name,
                                                llvm_type *FnTy) {
  llvm_function *Fn = llvm_function_new(FnTy, Name);
  
  /* Add the LLVM Function to the program */
  llvm_ilist_push_back(llvm_function, TheProgram.Functions, Fn);
  return Fn;
}

static llvm_function *CreateIntrinsicFunction(const char *Name, tree FnType) {
  llvm_type *FnTy = llvm_type_get_from_tree(FnType);
  return CreateIntrinsicFnWithType(Name, FnTy);
}

static void llvm_expand_builtin_va_start(llvm_function *Fn, tree exp) {
  tree arglist = TREE_OPERAND (exp, 1);

  static llvm_function *llvm_va_start_fn = 0;
  tree fntype = TREE_TYPE(current_function_decl);
  tree last_parm, arg;
  llvm_instruction *Call;
  llvm_value *DestVal;
  llvm_type *VAListTy;

  if (!llvm_va_start_fn) {
    tree fndecl = TREE_OPERAND (TREE_OPERAND (exp, 0), 0);
    llvm_type *FnType = llvm_type_get_from_tree(TREE_TYPE(fndecl));
    llvm_type *VAListTy = GET_FUNCTION_TYPE_ARGUMENT(FnType, 0);
    llvm_type *Ty = llvm_type_create_function(0, GET_POINTER_TYPE_ELEMENT(VAListTy));
    Ty = llvm_type_get_cannonical_version(Ty);
    llvm_va_start_fn = CreateIntrinsicFnWithType("llvm.va_start", Ty);
  }
  
  if (TYPE_ARG_TYPES (fntype) == 0 ||
      (TREE_VALUE (tree_last (TYPE_ARG_TYPES (fntype))) == void_type_node)) {
    error("`va_start' used in function with fixed args");
    return;
  }

  last_parm = tree_last(DECL_ARGUMENTS(current_function_decl));
  arg = TREE_VALUE(TREE_CHAIN(arglist));
  
  /* Strip off all nops for the sake of the comparison.  This
     is not quite the same as STRIP_NOPS.  It does more.
     We must also strip off INDIRECT_EXPR for C++ reference
     parameters.  */
  while (TREE_CODE (arg) == NOP_EXPR
         || TREE_CODE (arg) == CONVERT_EXPR
         || TREE_CODE (arg) == NON_LVALUE_EXPR
         || TREE_CODE (arg) == INDIRECT_REF)
    arg = TREE_OPERAND (arg, 0);

  if (arg != last_parm)
    error ("second parameter of `va_start' not last named argument");
  
  /* %llvm.va_start does not take an argument indicating the last
   * parameter... the LLVM compiler can figure this out for itself.  Because of
   * this, we expand a custom function call here...
   */
  DestVal = llvm_expand_expr(Fn, TREE_VALUE(arglist), 0);
  VAListTy = GET_FUNCTION_TYPE_RETURN(GET_POINTER_TYPE_ELEMENT(G2V(llvm_va_start_fn)->Ty));
  Call = llvm_instruction_new(VAListTy, "begin", O_Call, 1);
  Call->Operands[0] = G2V(llvm_va_start_fn);
  append_inst(Fn, Call);

  DestVal = cast_if_type_not_equal(Fn, DestVal,
                                   llvm_type_get_pointer(VAListTy));
  append_inst(Fn, create_store_inst(D2V(Call), DestVal, 0));
}

static void llvm_expand_builtin_va_end(llvm_function *Fn, tree exp) {
  tree fndecl = TREE_OPERAND (TREE_OPERAND (exp, 0), 0);
  static llvm_function *llvm_va_end_fn = 0;
  llvm_type *VAListType;
  llvm_instruction *Call;
  llvm_value *Arg;

  if (!llvm_va_end_fn) {
    llvm_type *VACopyTy = llvm_type_get_from_tree(TREE_TYPE(fndecl));
    llvm_type *PtrVAListTy = GET_FUNCTION_TYPE_ARGUMENT(VACopyTy, 0);
    llvm_type *FnTy = llvm_type_create_function(1, VoidTy);
    FnTy->Elements[1] = GET_POINTER_TYPE_ELEMENT(PtrVAListTy);
    FnTy = llvm_type_get_cannonical_version(FnTy);
    llvm_va_end_fn = CreateIntrinsicFnWithType("llvm.va_end", FnTy);
  }

  VAListType = GET_FUNCTION_TYPE_ARGUMENT(GET_POINTER_TYPE_ELEMENT(G2V(llvm_va_end_fn)->Ty), 0);

  Arg = llvm_expand_expr(Fn, TREE_VALUE(TREE_OPERAND(exp, 1)), 0);
  Arg = append_inst(Fn, create_load_inst("valist", Arg, 0));

  Call = llvm_instruction_new(VoidTy, "", O_Call, 2);
  Call->Operands[0] = G2V(llvm_va_end_fn);
  Call->Operands[1] = cast_if_type_not_equal(Fn, Arg, VAListType);
  append_inst(Fn, Call);
}

static void llvm_expand_builtin_va_copy(llvm_function *Fn, tree exp) {
  tree fndecl = TREE_OPERAND (TREE_OPERAND (exp, 0), 0);

  static llvm_function *llvm_va_copy_fn = 0;
  llvm_type *VAListType;
  if (!llvm_va_copy_fn) {
    llvm_type *VACopyTy = llvm_type_get_from_tree(TREE_TYPE(fndecl));
    llvm_type *VAListTy = GET_FUNCTION_TYPE_ARGUMENT(VACopyTy, 1);
    llvm_type *FnTy = llvm_type_create_function(1, VAListTy);
    FnTy->Elements[1] = VAListTy;
    FnTy = llvm_type_get_cannonical_version(FnTy);
    llvm_va_copy_fn = CreateIntrinsicFnWithType("llvm.va_copy", FnTy);
  }

  VAListType = GET_FUNCTION_TYPE_RETURN(GET_POINTER_TYPE_ELEMENT(G2V(llvm_va_copy_fn)->Ty));

  {
    tree SrcArg = TREE_VALUE(TREE_CHAIN(TREE_OPERAND(exp, 1)));
    llvm_instruction *I = llvm_instruction_new(VAListType, "tmp", O_Call, 2);
    llvm_value *DestAddr;
    I->Operands[0] = G2V(llvm_va_copy_fn);
    I->Operands[1] = llvm_expand_expr(Fn, SrcArg, 0);
    I->Operands[1] = cast_if_type_not_equal(Fn, I->Operands[1], VAListType);
    append_inst(Fn, I);
    
    DestAddr = llvm_expand_expr(Fn, TREE_VALUE(TREE_OPERAND(exp, 1)), 0);
    DestAddr = cast_if_type_not_equal(Fn, DestAddr,
                                      llvm_type_get_pointer(VAListType));
    append_inst(Fn, create_store_inst(D2V(I), DestAddr, 0));
  }
}

static llvm_value *llvm_expand_builtin_alloca(llvm_function *Fn, tree arglist) {
  llvm_value *Size;

  /*if (!validate_arglist(arglist, INTEGER_TYPE, VOID_TYPE)) return 0; */
  
  /* Compute the argument.  */
  Size = llvm_expand_expr(Fn, TREE_VALUE(arglist), 0);
  Size = cast_if_type_not_equal(Fn, Size, UIntTy);
  return append_inst(Fn, create_alloca_inst("tmp", SByteTy, Size));
}

/* llvm_expand_builtin - This is patterned off of expand_builtin. */
static llvm_value *llvm_expand_builtin(llvm_function *Fn, tree exp,
                                       llvm_value *DestLoc) {
  tree fndecl = TREE_OPERAND (TREE_OPERAND (exp, 0), 0);
  tree arglist = TREE_OPERAND (exp, 1);
  enum built_in_function fcode = DECL_FUNCTION_CODE (fndecl);
  llvm_type *DestTy = llvm_type_get_from_tree(TREE_TYPE(exp));

  assert(DECL_BUILT_IN_CLASS (fndecl) != BUILT_IN_MD);

  /* Generate library calls for functions that we can do so for. */
  switch (fcode) {
  case BUILT_IN_SQRT:
  case BUILT_IN_SQRTF:
  case BUILT_IN_SQRTL:
  case BUILT_IN_SIN:
  case BUILT_IN_SINF:
  case BUILT_IN_SINL:
  case BUILT_IN_COS:
  case BUILT_IN_COSF:
  case BUILT_IN_COSL:
  case BUILT_IN_EXP:
  case BUILT_IN_EXPF:
  case BUILT_IN_EXPL:
  case BUILT_IN_LOG:
  case BUILT_IN_LOGF:
  case BUILT_IN_LOGL:
  case BUILT_IN_POW:
  case BUILT_IN_POWF:
  case BUILT_IN_POWL:
  case BUILT_IN_ATAN2:
  case BUILT_IN_ATAN2F:
  case BUILT_IN_ATAN2L:
  case BUILT_IN_MEMSET:
  case BUILT_IN_MEMCPY:
  case BUILT_IN_MEMCMP:
  case BUILT_IN_BCMP:
  case BUILT_IN_BZERO:
  case BUILT_IN_INDEX:
  case BUILT_IN_RINDEX:
  case BUILT_IN_STRCHR:
  case BUILT_IN_STRRCHR:
  case BUILT_IN_STRLEN:
  case BUILT_IN_STRCPY:
  case BUILT_IN_STRNCPY:
  case BUILT_IN_STRNCMP:
  case BUILT_IN_STRSTR:
  case BUILT_IN_STRPBRK:
  case BUILT_IN_STRCAT:
  case BUILT_IN_STRNCAT:
  case BUILT_IN_STRSPN:
  case BUILT_IN_STRCSPN:
  case BUILT_IN_STRCMP:
  case BUILT_IN_FFS:
  case BUILT_IN_PUTCHAR:
  case BUILT_IN_PUTS:
  case BUILT_IN_PRINTF:
  case BUILT_IN_FPUTC:
  case BUILT_IN_FPUTS:
  case BUILT_IN_FWRITE:
  case BUILT_IN_PUTCHAR_UNLOCKED:
  case BUILT_IN_PUTS_UNLOCKED:
  case BUILT_IN_PRINTF_UNLOCKED:
  case BUILT_IN_FPUTC_UNLOCKED:
  case BUILT_IN_FPUTS_UNLOCKED:
  case BUILT_IN_FWRITE_UNLOCKED:
  case BUILT_IN_FLOOR:
  case BUILT_IN_FLOORF:
  case BUILT_IN_FLOORL:
  case BUILT_IN_CEIL:
  case BUILT_IN_CEILF:
  case BUILT_IN_CEILL:
  case BUILT_IN_TRUNC:
  case BUILT_IN_TRUNCF:
  case BUILT_IN_TRUNCL:
  case BUILT_IN_ROUND:
  case BUILT_IN_ROUNDF:
  case BUILT_IN_ROUNDL:
  case BUILT_IN_NEARBYINT:
  case BUILT_IN_NEARBYINTF:
  case BUILT_IN_NEARBYINTL:
    return llvm_expand_call (Fn, exp, DestLoc);
  default:
    break;
  }

  switch (fcode) {
  case BUILT_IN_ABS:
  case BUILT_IN_LABS:
  case BUILT_IN_LLABS:
  case BUILT_IN_IMAXABS:
  case BUILT_IN_FABS:
  case BUILT_IN_FABSF:
  case BUILT_IN_FABSL:
    /* build_function_call changes these into ABS_EXPR.  */
    abort ();

  case BUILT_IN_CONJ:
  case BUILT_IN_CONJF:
  case BUILT_IN_CONJL:
  case BUILT_IN_CREAL:
  case BUILT_IN_CREALF:
  case BUILT_IN_CREALL:
  case BUILT_IN_CIMAG:
  case BUILT_IN_CIMAGF:
  case BUILT_IN_CIMAGL:
    /* expand_tree_builtin changes these into CONJ_EXPR, REALPART_EXPR
       and IMAGPART_EXPR.  */
    abort ();

  case BUILT_IN_SIN:
  case BUILT_IN_SINF:
  case BUILT_IN_SINL:
  case BUILT_IN_COS:
  case BUILT_IN_COSF:
  case BUILT_IN_COSL:
  case BUILT_IN_EXP:
  case BUILT_IN_EXPF:
  case BUILT_IN_EXPL:
  case BUILT_IN_LOG:
  case BUILT_IN_LOGF:
  case BUILT_IN_LOGL:
  case BUILT_IN_SQRT:
  case BUILT_IN_SQRTF:
  case BUILT_IN_SQRTL:
  case BUILT_IN_FLOOR:
  case BUILT_IN_FLOORF:
  case BUILT_IN_FLOORL:
  case BUILT_IN_CEIL:
  case BUILT_IN_CEILF:
  case BUILT_IN_CEILL:
  case BUILT_IN_TRUNC:
  case BUILT_IN_TRUNCF:
  case BUILT_IN_TRUNCL:
  case BUILT_IN_ROUND:
  case BUILT_IN_ROUNDF:
  case BUILT_IN_ROUNDL:
  case BUILT_IN_NEARBYINT:
  case BUILT_IN_NEARBYINTF:
  case BUILT_IN_NEARBYINTL:
  case BUILT_IN_POW:
  case BUILT_IN_POWF:
  case BUILT_IN_POWL:
  case BUILT_IN_ATAN2:
  case BUILT_IN_ATAN2F:
  case BUILT_IN_ATAN2L:
    break;
#if 0
  case BUILT_IN_APPLY_ARGS:
    return expand_builtin_apply_args ();

    /* __builtin_apply (FUNCTION, ARGUMENTS, ARGSIZE) invokes
       FUNCTION with a copy of the parameters described by
       ARGUMENTS, and ARGSIZE.  It returns a block of memory
       allocated on the stack into which is stored all the registers
       that might possibly be used for returning the result of a
       function.  ARGUMENTS is the value returned by
       __builtin_apply_args.  ARGSIZE is the number of bytes of
       arguments that must be copied.  ??? How should this value be
       computed?  We'll also need a safe worst case value for varargs
       functions.  */
  case BUILT_IN_APPLY:
    if (!validate_arglist (arglist, POINTER_TYPE,
                           POINTER_TYPE, INTEGER_TYPE, VOID_TYPE)
        && !validate_arglist (arglist, REFERENCE_TYPE,
                              POINTER_TYPE, INTEGER_TYPE, VOID_TYPE))
      return const0_rtx;
    else
      {
        int i;
        tree t;
        rtx ops[3];

        for (t = arglist, i = 0; t; t = TREE_CHAIN (t), i++)
          ops[i] = expand_expr (TREE_VALUE (t), NULL_RTX, VOIDmode, 0);

        return expand_builtin_apply (ops[0], ops[1], ops[2]);
      }

    /* __builtin_return (RESULT) causes the function to return the
       value described by RESULT.  RESULT is address of the block of
       memory returned by __builtin_apply.  */
  case BUILT_IN_RETURN:
    if (validate_arglist (arglist, POINTER_TYPE, VOID_TYPE))
      expand_builtin_return (expand_expr (TREE_VALUE (arglist),
                                          NULL_RTX, VOIDmode, 0));
    return const0_rtx;

  case BUILT_IN_SAVEREGS:
    return expand_builtin_saveregs ();

  case BUILT_IN_ARGS_INFO:
    return expand_builtin_args_info (exp);

    /* Return the address of the first anonymous stack arg.  */
  case BUILT_IN_NEXT_ARG:
    return expand_builtin_next_arg (arglist);

  case BUILT_IN_CLASSIFY_TYPE:
    return expand_builtin_classify_type (arglist);
#endif
  case BUILT_IN_CONSTANT_P:/*Constant folding already took care of easy cases.*/
    return llvm_constant_get_null(DestTy);

  case BUILT_IN_ALLOCA:
    return llvm_expand_builtin_alloca(Fn, arglist);

#if 0
  case BUILT_IN_FRAME_ADDRESS:
  case BUILT_IN_RETURN_ADDRESS:
    return expand_builtin_frame_address (exp);

    /* Returns the address of the area where the structure is returned.
       0 otherwise.  */
  case BUILT_IN_AGGREGATE_INCOMING_ADDRESS:
    if (arglist != 0
        || ! AGGREGATE_TYPE_P (TREE_TYPE (TREE_TYPE (current_function_decl)))
        || GET_CODE (DECL_RTL (DECL_RESULT (current_function_decl))) != MEM)
      return const0_rtx;
    else
      return XEXP (DECL_RTL (DECL_RESULT (current_function_decl)), 0);

  case BUILT_IN_FFS:
  case BUILT_IN_FFSL:
  case BUILT_IN_FFSLL:
    target = expand_builtin_unop (target_mode, arglist, target,
                                  subtarget, ffs_optab);
    if (target)
      return target;
    break;

  case BUILT_IN_CLZ:
  case BUILT_IN_CLZL:
  case BUILT_IN_CLZLL:
    target = expand_builtin_unop (target_mode, arglist, target,
                                  subtarget, clz_optab);
    if (target)
      return target;
    break;

  case BUILT_IN_CTZ:
  case BUILT_IN_CTZL:
  case BUILT_IN_CTZLL:
    target = expand_builtin_unop (target_mode, arglist, target,
                                  subtarget, ctz_optab);
    if (target)
      return target;
    break;

  case BUILT_IN_POPCOUNT:
  case BUILT_IN_POPCOUNTL:
  case BUILT_IN_POPCOUNTLL:
    target = expand_builtin_unop (target_mode, arglist, target,
                                  subtarget, popcount_optab);
    if (target)
      return target;
    break;

  case BUILT_IN_PARITY:
  case BUILT_IN_PARITYL:
  case BUILT_IN_PARITYLL:
    target = expand_builtin_unop (target_mode, arglist, target,
                                  subtarget, parity_optab);
    if (target)
      return target;
    break;

  case BUILT_IN_STRLEN:
    target = expand_builtin_strlen (exp, target);
    if (target)
      return target;
    break;

  case BUILT_IN_STRCPY:
    target = expand_builtin_strcpy (exp, target, mode);
    if (target)
      return target;
    break;

  case BUILT_IN_STRNCPY:
    target = expand_builtin_strncpy (arglist, target, mode);
    if (target)
      return target;
    break;

  case BUILT_IN_STRCAT:
    target = expand_builtin_strcat (arglist, target, mode);
    if (target)
      return target;
    break;

  case BUILT_IN_STRNCAT:
    target = expand_builtin_strncat (arglist, target, mode);
    if (target)
      return target;
    break;

  case BUILT_IN_STRSPN:
    target = expand_builtin_strspn (arglist, target, mode);
    if (target)
      return target;
    break;

  case BUILT_IN_STRCSPN:
    target = expand_builtin_strcspn (arglist, target, mode);
    if (target)
      return target;
    break;

  case BUILT_IN_STRSTR:
    target = expand_builtin_strstr (arglist, target, mode);
    if (target)
      return target;
    break;

  case BUILT_IN_STRPBRK:
    target = expand_builtin_strpbrk (arglist, target, mode);
    if (target)
      return target;
    break;

  case BUILT_IN_INDEX:
  case BUILT_IN_STRCHR:
    target = expand_builtin_strchr (arglist, target, mode);
    if (target)
      return target;
    break;

  case BUILT_IN_RINDEX:
  case BUILT_IN_STRRCHR:
    target = expand_builtin_strrchr (arglist, target, mode);
    if (target)
      return target;
    break;

  case BUILT_IN_MEMCPY:
    target = expand_builtin_memcpy (arglist, target, mode);
    if (target)
      return target;
    break;

  case BUILT_IN_MEMSET:
    target = expand_builtin_memset (exp, target, mode);
    if (target)
      return target;
    break;

  case BUILT_IN_BZERO:
    target = expand_builtin_bzero (exp);
    if (target)
      return target;
    break;

  case BUILT_IN_STRCMP:
    target = expand_builtin_strcmp (exp, target, mode);
    if (target)
      return target;
    break;

  case BUILT_IN_STRNCMP:
    target = expand_builtin_strncmp (exp, target, mode);
    if (target)
      return target;
    break;

  case BUILT_IN_BCMP:
  case BUILT_IN_MEMCMP:
    target = expand_builtin_memcmp (exp, arglist, target, mode);
    if (target)
      return target;
    break;

  case BUILT_IN_SETJMP:
    target = expand_builtin_setjmp (arglist, target);
    if (target)
      return target;
    break;

    /* __builtin_longjmp is passed a pointer to an array of five words.
       It's similar to the C library longjmp function but works with
       __builtin_setjmp above.  */
  case BUILT_IN_LONGJMP:
    if (!validate_arglist (arglist, POINTER_TYPE, INTEGER_TYPE, VOID_TYPE))
      break;
    else
      {
        rtx buf_addr = expand_expr (TREE_VALUE (arglist), subtarget,
                                    VOIDmode, 0);
        rtx value = expand_expr (TREE_VALUE (TREE_CHAIN (arglist)),
                                 NULL_RTX, VOIDmode, 0);

        if (value != const1_rtx)
          {
            error ("__builtin_longjmp second argument must be 1");
            return const0_rtx;
          }

        expand_builtin_longjmp (buf_addr, value);
        return const0_rtx;
      }

  case BUILT_IN_TRAP:
    expand_builtin_trap ();
    return const0_rtx;

  case BUILT_IN_FPUTS:
    target = expand_builtin_fputs (arglist, ignore,/*unlocked=*/ 0);
    if (target)
      return target;
    break;
  case BUILT_IN_FPUTS_UNLOCKED:
    target = expand_builtin_fputs (arglist, ignore,/*unlocked=*/ 1);
    if (target)
      return target;
    break;

    /* Various hooks for the DWARF 2 __throw routine.  */
  case BUILT_IN_UNWIND_INIT:
    expand_builtin_unwind_init ();
    return const0_rtx;
  case BUILT_IN_DWARF_CFA:
    return virtual_cfa_rtx;
#ifdef DWARF2_UNWIND_INFO
  case BUILT_IN_DWARF_FP_REGNUM:
    return expand_builtin_dwarf_fp_regnum ();
  case BUILT_IN_INIT_DWARF_REG_SIZES:
    expand_builtin_init_dwarf_reg_sizes (TREE_VALUE (arglist));
    return const0_rtx;
#endif
  case BUILT_IN_FROB_RETURN_ADDR:
    return expand_builtin_frob_return_addr (TREE_VALUE (arglist));
  case BUILT_IN_EXTRACT_RETURN_ADDR:
    return expand_builtin_extract_return_addr (TREE_VALUE (arglist));
  case BUILT_IN_EH_RETURN:
    expand_builtin_eh_return (TREE_VALUE (arglist),
                              TREE_VALUE (TREE_CHAIN (arglist)));
    return const0_rtx;
#ifdef EH_RETURN_DATA_REGNO
  case BUILT_IN_EH_RETURN_DATA_REGNO:
    return expand_builtin_eh_return_data_regno (arglist);
#endif
#endif

  case BUILT_IN_VA_START:
  case BUILT_IN_STDARG_START:
    llvm_expand_builtin_va_start(Fn, exp);
    return 0;
  case BUILT_IN_VA_END:
    llvm_expand_builtin_va_end(Fn, exp);
    return 0;
  case BUILT_IN_VA_COPY:
    llvm_expand_builtin_va_copy(Fn, exp);
    return 0;

  case BUILT_IN_EXPECT:  /* LLVM: Ignore the hint */
    if (arglist == NULL_TREE || TREE_CHAIN (arglist) == NULL_TREE)
      return 0;
    return llvm_expand_expr(Fn, TREE_VALUE (TREE_CHAIN (arglist)), DestLoc);
#if 0
  case BUILT_IN_PREFETCH:
    expand_builtin_prefetch (arglist);
    return const0_rtx;
#endif
  default:	/* just do library call, if unknown builtin */
    if (!DECL_ASSEMBLER_NAME_SET_P (fndecl))
      error ("built-in function `%s' not currently supported",
             IDENTIFIER_POINTER (DECL_NAME (fndecl)));
  }

  /* The switch statement above can drop through to cause the function
     to be called normally.  */
  return llvm_expand_call(Fn, exp, DestLoc);
}



/*===----------------------------------------------------------------------===**
               ... Top-Level Expression Expansion Dispatchers...
 *===----------------------------------------------------------------------===*/

/* llvm_decode_string_constant - This helper function allows STRING_CST nodes to
 * be decoded into an arbitrary sized string region.  This is necessary because
 * the user can do things like this:
 *    char foo[100] = "testing";  char foo2[3] = "testing";
 */
static llvm_constant *llvm_decode_string_constant(tree exp, unsigned Len,
                                                  llvm_type *ElTy) {
  char *Buffer = (char*)alloca(Len*3+4);
  const char *InStr = TREE_STRING_POINTER(exp);
  unsigned i, CP = 0;
  unsigned MinLen = (unsigned)TREE_STRING_LENGTH(exp);
  if (MinLen > Len) MinLen = Len;
    
  if (ElTy != SByteTy && ElTy != UByteTy) {
    llvm_value **Elements = llvm_expand_constructor_elements(0, 0, exp, 0);
    llvm_type *Ty = llvm_type_get_from_tree(TREE_TYPE(exp));
    return G2C(llvm_constant_aggregate_new(Ty, Elements));
  }

  Buffer[CP++] = 'c'; Buffer[CP++] = '"';
  for (i = 0; i != MinLen; ++i)
    if (isprint((int)InStr[i]) && InStr[i] != '"' && InStr[i] != '\\')
      Buffer[CP++] = InStr[i];
    else {
      sprintf(Buffer+CP, "\\%02X", ((unsigned)InStr[i] & 0xFF));
      CP += 3;
    }

  for (; i != Len; ++i) {  /* Expand out any zero suffix */
    Buffer[CP++] = '\\';
    Buffer[CP++] = '0';
    Buffer[CP++] = '0';
  }

  Buffer[CP++] = '\"'; Buffer[CP++] = 0;
  return V2C(llvm_constant_new(llvm_type_get_array(ElTy, Len), Buffer));
}

/* llvm_expand_constant_expr - This function is responsible for translating a
 * constant tree expression into a suitable LLVM constant value.  This is
 * seperate from other expresion evaluation code because it is used to compute
 * the initializers for global variables, which are required to be constants.
 *
 * ReqTy specifies the type that the result must be.  Note that this may be very
 * different from the type of 'exp'.  For example, exp may be an integer typed
 * value, and reqty may be a floating point type.  This means that a floating
 * point value should be returned with the bit pattern specified by the integer:
 * not an integer casted to a float.  This type of thing happens when generating
 * union initializers.
 */
static llvm_constant *llvm_expand_constant_expr(tree exp, llvm_type *ReqTy) {
  llvm_type *Ty = llvm_type_get_from_tree(TREE_TYPE(exp));
  llvm_value *Val = 0;

  switch (TREE_CODE(exp)) {
  case INTEGER_CST: {  /* Integer constant */
    HOST_WIDE_INT HI = (unsigned HOST_WIDE_INT)TREE_INT_CST_HIGH(exp);
    HOST_WIDE_INT LO = (unsigned HOST_WIDE_INT)TREE_INT_CST_LOW(exp);
    long long IntValue;

    switch (Ty->ID) {
    default: assert(0 && "Unexpected type for INTEGER_CST!");
    case VoidTyID: 
      return 0;
    case PointerTyID:
      if (LO == 0 && HI == 0)
        return V2C(llvm_constant_get_null(ReqTy));

      if (Pmode == SImode)     /* Sign extend the constant as appropriate. */
        HI = (int)LO < 0 ? -1 : 0;

      /* FALL THROUGH */
    case ULongTyID:
    case LongTyID:
      if (sizeof(LO) == 8) {
        IntValue = (long long)LO;
      } else {
        assert(sizeof(LO) == 4 && "64 and 32 bit HOST_WIDE_INT's supported!");
        IntValue = ((long long)(unsigned)HI << 32) | (long long)(unsigned)LO;
      }
      break;

    case BoolTyID:
      IntValue = LO != 0;
      break;

    case SByteTyID:
    case ShortTyID:
    case IntTyID:
      IntValue = (int)LO;
      break;
    case UByteTyID:
    case UShortTyID:
    case UIntTyID:
      IntValue = (unsigned)LO;
      break;
    }

    /* Now that we have computed the value we have, convert it to the desired
     * type!
     */
    if (llvm_type_is_integral(ReqTy))
      return V2C(llvm_constant_new_integral(ReqTy, IntValue));
    else if (ReqTy->ID == PointerTyID) {
      Val = llvm_constant_new_integral(LongTy, IntValue);
      return V2C(cast_if_type_not_equal(0, Val, Ty));
    } else {
      char Buffer[50];
      assert(llvm_type_is_fp(ReqTy) && "Unknown requested type!");

      if (ReqTy == FloatTy) {
        /* Convert from the integer representation of a float to the integer
         * representation of a double
         */
        union {
          int Fi;
          float F;
          long long Di;
          double D;
        } u;
        u.Fi = IntValue;
        u.D = u.F;
        IntValue = u.Di;
      }
      sprintf(Buffer, "0x%016llX", IntValue);
      return V2C(llvm_constant_new(ReqTy, Buffer));
    }
    break;
  }

  case REAL_CST: {        /* Floating point constant */
    long RealArr[2];
    char Buffer[50], *BufPtr = Buffer;
    unsigned Size = 8;
    char *Values;
    REAL_VALUE_TO_TARGET_DOUBLE(TREE_REAL_CST(exp), RealArr);

    if (llvm_type_is_integral(ReqTy)) {
      long long IntVal = *(long long*)RealArr;
      return V2C(llvm_constant_new_integral(ReqTy, IntVal));
    }    

    /* FIXME: This won't work right if endianness is non-agreeing? */
    
    *BufPtr++ = '0';
    *BufPtr++ = 'x';
    if (*(char*)&Size == 8) {   /* If little endian */
      Values = (char*)RealArr+Size;
      while (Size--) {
        sprintf(BufPtr, "%02X", (unsigned char)*--Values);
        BufPtr += 2;
      }
    } else {
      Values = (char*)RealArr;
      while (Size--) {
        sprintf(BufPtr, "%02X", (unsigned char)*Values++);
        BufPtr += 2;
      }
    }
    *BufPtr = 0;  /* Null terminate */

    Val = llvm_constant_new(Ty, Buffer);
    break;
  }

  case ADDR_EXPR:       /* & Expression  */
    /* This can never expand into a bitfield */
    Val = llvm_expand_lvalue_expr(0, TREE_OPERAND(exp, 0), 0, 0);
    Val = cast_if_type_not_equal(0, Val, Ty);
    break;

  case CONSTRUCTOR:      /* Initializer for global structs and arrays */
    assert(llvm_type_is_composite(Ty) && "Constructor for non-composite type?");
    Val = D2V(llvm_expand_get_constructor_constant(exp));
    Val = cast_if_type_not_equal(0, Val, Ty);
    break;

  case NOP_EXPR:         /* Cast constant_expr */
  case CONVERT_EXPR:
    Val = D2V(llvm_expand_constant_expr(TREE_OPERAND(exp, 0),
                     llvm_type_get_from_tree(TREE_TYPE(TREE_OPERAND(exp, 0)))));
    break;

  case PLUS_EXPR:
  case MINUS_EXPR: {
    llvm_value *op0 = D2V(llvm_expand_constant_expr(TREE_OPERAND(exp,0),ReqTy));
    llvm_value *op1 = D2V(llvm_expand_constant_expr(TREE_OPERAND(exp,1),ReqTy));
    llvm_instruction *Inst;
    int isPlus = TREE_CODE(exp) == PLUS_EXPR;
    if (Ty->ID == PointerTyID && op0->Ty->ID == PointerTyID) {
      /* Attempt to convert an ADD or SUB expression operand on pointer types
       * into a getelementptr instruction.
       */
      Val = llvm_expand_pointer_addsub(0, isPlus, op0, op1, Ty);
      if (Val) break;
    }

    /* Attempt to unify the types of the left and right operand... */
    if (TREE_CODE(TREE_OPERAND(exp, 1)) == INTEGER_CST)
      op1 = cast_if_type_not_equal(0, op1, op0->Ty);

    if (op0->Ty->ID == PointerTyID && op1->Ty->ID == PointerTyID) {
      op0 = cast_if_type_not_equal(0, op0, LongTy);
      op1 = cast_if_type_not_equal(0, op1, LongTy);
    }

    Inst = create_binary_inst("tmp", isPlus ? O_Add : O_Sub, op0, op1);
    Val = append_inst(0, Inst);
    Val = cast_if_type_not_equal(0, Val, Ty);
    break;
  }

  /* Create a string constant suitable to initialize a global array */
  case STRING_CST:
    Val = D2V(llvm_decode_string_constant(exp, TREE_STRING_LENGTH(exp),
                                          GET_ARRAY_TYPE_ELEMENT(Ty)));
    Val = cast_if_type_not_equal(0, Val, Ty);
    break;

  default:
    LLVM_TODO_TREE(exp);
  }

  Val = cast_if_type_not_equal(0, Val, ReqTy);
  return V2C(Val); 
}



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
llvm_value *llvm_expand_lvalue_expr(llvm_function *Fn, tree exp,
                                    unsigned *BitStart, unsigned *BitSize) {
  tree context;
  llvm_type *ElTy = llvm_type_get_from_tree(TREE_TYPE(exp));
  llvm_type *Ty = llvm_type_get_pointer(ElTy);
  llvm_value *Result;

  switch (TREE_CODE(exp)) {
  default: {
    extern llvm_value *lhd_llvm_expand_lvalue_expr(llvm_function *, tree,
                                                   unsigned*, unsigned *);

    if (lang_hooks.llvm_expand_lvalue_expr != lhd_llvm_expand_lvalue_expr)
      return (*lang_hooks.llvm_expand_lvalue_expr)(Fn, exp, BitStart, BitSize);
    LLVM_TODO_TREE(exp);
  }

  case PARM_DECL:
    if (!DECL_LLVM_SET_P (exp)) {
      error ("%Hprior parameter's size depends on '%D'",
             &DECL_SOURCE_LOCATION (exp), exp);
      return llvm_constant_VoidPtr_null;
    }
    /* ... fall through ...  */

  case VAR_DECL:
    /* If a static var's type was incomplete when the decl was written,
       but the type is complete now, lay out the decl now.  */
    if (DECL_SIZE (exp) == 0 && COMPLETE_TYPE_P (TREE_TYPE (exp))
        && (TREE_STATIC (exp) || DECL_EXTERNAL (exp)))
      layout_decl (exp, 0);
    
    /* ... fall through ...  */
  case FUNCTION_DECL:
  case RESULT_DECL:
    if (DECL_LLVM(exp) == 0) {
      debug_tree(exp);
      DECL_LLVM(exp);
      abort();
    }

    /* Ensure variable marked as used even if it doesn't go through a parser.
       If it hasn't be used yet, write out an external definition.  */
    if (!TREE_USED(exp)) {
      assemble_external(exp);
      TREE_USED(exp) = 1;
    }

    /* Return the address of the LVALUE */
    Result = DECL_LLVM(exp);

    /* Handle variables inherited from containing functions.  */
    context = decl_function_context(exp);
    if (context != 0 && context != current_function_decl &&
        /*context != inline_function_decl &&*/
        /* If var is static, we don't need a static chain to access it.  */
        !llvm_value_is_constant(Result))
      LLVM_TODO_TREE(exp);  /* Doesn't handle nested functions yet! */

    if (TREE_CODE(TREE_TYPE(exp)) == ARRAY_TYPE && ElTy->ID != ArrayTyID)
      return Result;   /* Avoid casting away arrayness */

    if (llvm_value_is_global(Result))
      llvm_get_or_make_decl_llvm(exp, 0);  /* Make sure to emit inline funcs */
    break;

  case INDIRECT_REF:
    assert(Fn && "Cannot use INDIRECT_REFS to initialize constants!");
    Result = llvm_expand_expr(Fn, TREE_OPERAND(exp, 0), 0);
    break;

  case ARRAY_REF: {
    llvm_type *Op0Ty = llvm_type_get_from_tree(TREE_TYPE(TREE_OPERAND(exp, 0)));

    if (llvm_type_is_composite(Op0Ty)) {
      llvm_value *Op0 = llvm_expand_lvalue_expr(Fn, TREE_OPERAND(exp, 0),
                                                BitStart, BitSize);
      llvm_value *Op1 = llvm_expand_expr(Fn, TREE_OPERAND(exp, 1), 0);
      Op1 = cast_if_type_not_equal(Fn, Op1, LongTy);
      Result = append_inst(Fn, create_gep3(Op0, llvm_constant_long_0, Op1));
    } else {
      llvm_instruction *I;
      /* As a "special extension" we have perverted ARRAY_REF's so that they can
       * take a pointer as the first operand.  In this case, we generate a two
       * operand GEP.
       */
      llvm_value *Op0 = llvm_expand_expr(Fn, TREE_OPERAND(exp, 0), 0);
      llvm_value *Op1 = llvm_expand_expr(Fn, TREE_OPERAND(exp, 1), 0);
      Op1 = cast_if_type_not_equal(Fn, Op1, LongTy);
      /* FIXME: What do we do about bitfields here??? */
      
      assert(Op0->Ty->ID == PointerTyID &&
             "Cannot subscript non-pointer, non-array type!");

      I = llvm_instruction_new(Op0->Ty, "tmp", O_GetElementPtr, 2);
      I->Operands[0] = Op0;
      I->Operands[1] = Op1;
      Result = append_inst(Fn, I);
    }
    break;
  }

  case COMPONENT_REF: {
    /* The structure itself cannot produce a bitfield! */
    llvm_value *Op0 = llvm_expand_lvalue_expr(Fn, TREE_OPERAND(exp, 0), 0, 0);
    tree FieldDecl = TREE_OPERAND(exp, 1);
    tree FieldDeclType = TREE_TYPE(FieldDecl);
    llvm_type *FieldDeclTy = llvm_type_get_from_tree(FieldDeclType);
    llvm_instruction *I;
    unsigned Offset = GetFieldOffset(FieldDecl);
    unsigned Size = llvm_type_get_size(FieldDeclTy)*8;
    if (Size > GetDeclSize(FieldDecl)) Size = GetDeclSize(FieldDecl);

    /* Special case handling for vtable pointers.  For some reason, the C++
     * front-end has vtable decls that are not fields of the class that we are
     * interested in.  Because they are not fields of the classes themselves,
     * they never get their DECL_LLVM set to specify their field number.
     * Actually it gets worse than that because we may be looking at a derived
     * class, so there may not BE a single index that gets us to the vtable.
     *
     * The only redeeming fact of this situation is that vtable pointers always
     * start at offset 0.  For this reason we can just insert a "cast" of the
     * structure type to the field type (which should get converted the the
     * right GEP) to access the field.
     */
    if (!DECL_LLVM_SET_P(FieldDecl) && Offset == 0) {
      Result = cast_if_type_not_equal(Fn, Op0, Ty);
      assert((Size == 32 || Size == 64) && "vtable pointer not integer size?");
    } else {
      unsigned ActualOffset = GetFieldDeclOffset(FieldDecl)*8;
      unsigned ActualSize;
      llvm_value *FieldNo = DECL_LLVM(FieldDecl);
      llvm_type *ResultElTy;
      I = create_gep3(Op0, llvm_constant_long_0, FieldNo);
      Result = append_inst(Fn, I);

      ResultElTy = GET_POINTER_TYPE_ELEMENT(Result->Ty);
      ActualSize = llvm_type_get_size(ResultElTy)*8;

      /* If this is accessing a union element, we can go ahead and cast the
       *  pointer to the desired type now.
       */
      if (ActualOffset == Offset && Offset == 0 && Size > ActualSize) {
        assert((ActualSize & 7) == 0 && (Size & 7) == 0 &&
               "Illegal union field reference!");
        Result = cast_if_type_not_equal(Fn, Op0,
                                        llvm_type_get_pointer(FieldDeclTy));
        ResultElTy = GET_POINTER_TYPE_ELEMENT(Result->Ty);
        ActualSize = llvm_type_get_size(ResultElTy)*8;
      }

      assert(ActualOffset <= Offset && ActualSize >= Size &&
             "Did not generate a legal reference!");

      /* Check to see if this field is a bitfield.  If so, we have to set the
       * BitStart/BitSize fields to the right values.
       */
      if (ActualSize != Size || ActualOffset != Offset) {
        /* Check to see if this is a field that was folded into other stuff
         * because it was a bitfield.  If this is the case, we try extra hard to
         * generate a legitiment address, because this is a legitimate
         * (non-bitfield) lvalue.  Also, if we cannot generate a bitfield
         * reference (because the final field was not integral), do not attempt
         * to generate extraction operations for non-int fields.
         */
        if ((BitStart == 0 || !llvm_type_is_integral(ResultElTy)) &&
             (Offset & 7) == 0 && (Size & 7) == 0) {
          /* Generate casts to adjust the result pointer.  We know that it is
           * going to land on a byte boundary, so it is addressible.
           */
          llvm_type *SBPtr = llvm_type_get_pointer(SByteTy);
          llvm_value *Ptr = cast_if_type_not_equal(Fn, Result, SBPtr);
          if (Offset) {
            llvm_instruction *GEP = llvm_instruction_new(SBPtr, "tmp",
                                                         O_GetElementPtr, 2);
            GEP->Operands[0] = Ptr;
            GEP->Operands[1] = llvm_constant_new_integral(LongTy, Offset/8);
            Ptr = append_inst(Fn, GEP);
          }
          Result = cast_if_type_not_equal(Fn, Ptr, Result->Ty);
        } else {
          assert(BitStart && BitSize && "Caller can not support a bitfield!");
          *BitStart = Offset-ActualOffset;
          *BitSize = Size;
          /* Do not cast to be a pointer to the requested type! */
          return Result;
        }
      }
    }
    break;
  }

  case STRING_CST: {     /* Literal string lvalue: "x" expression */
    static int StrCounter = 0;
    /* Create a new global variable for the constant string */
    char Name[20];
    llvm_global *G;
    llvm_type *GlobTy = GET_POINTER_TYPE_ELEMENT(Ty);
    assert(GlobTy->ID == ArrayTyID && "STRING_CST initializing non-array?");
    sprintf(Name, ".str_%d", ++StrCounter);
    G = llvm_global_new(GlobTy, Name);
    G->isConstant = 1;
    G->Linkage = L_Internal;
    /* Get the string initializer. */
    G->Init = llvm_decode_string_constant(exp, GET_ARRAY_TYPE_SIZE(GlobTy),
                                          GET_ARRAY_TYPE_ELEMENT(GlobTy));
    llvm_ilist_push_back(llvm_global, TheProgram.Globals, G);
    
    if (EMIT_CODE_INCREMENTALLY) llvm_global_print(G, llvm_out_file);
    Result = G2V(G);
    break;
  }

  case CALL_EXPR:
    /* CALL_EXPR - If we are using a call_expr as an lvalue, this means that we
     * are doing something with the result of a call that returns an aggregate
     * type.  In order to handle this correctly, we allocate some temporary
     * space, code generate the call into it, then return the address of the
     * temporary space.
     */
    Result = D2V(make_temporary_alloca(Fn, ElTy));
    assert(llvm_type_is_composite(ElTy) && "Return type isn't composite?");
    llvm_expand_call(Fn, exp, Result);
    break;
    
  case TARGET_EXPR:
    /* TARGET_EXPR's are really wierd.  If the EXPR is found in an address-of
     * expression, it must necessarily be "orphaned", so just expand it without
     * a destination.  This will cause the VAR_DECL to have its DECL_LLVM set,
     * which is the l-value we want.
     */
    llvm_expand_expr(Fn, exp, 0);
    assert(DECL_LLVM_SET_P(TARGET_EXPR_SLOT(exp)));
    Result = DECL_LLVM(TARGET_EXPR_SLOT(exp));
    break;
#if 0
    {
    /* Something needs to be initialized, but we didn't know where that thing
       was when building the tree.  For example, it could be the return value of
       a function, or a parameter to a function which lays down in the stack, or
       a temporary variable which must be passed by reference.

       We guarantee that the expression will either be constructed or copied
       into our original target.  */

    tree decl = TARGET_EXPR_SLOT (exp);
    tree initializer;
    assert(TREE_CODE(decl) == VAR_DECL);
    assert(Fn && "Cannot use TARGET_EXPRs to initialize constants!");

    if (DECL_LLVM_SET_P (decl)) {
      /* If we have already expanded the decl, so don't do it again. */
      assert(TARGET_EXPR_INITIAL (exp) == NULL_TREE);
      Result = DECL_LLVM (decl);
      break;
    }

    /* Insert an alloca instruction for the declaration. */
    llvm_expand_decl(Fn, decl);

    /* Since DECL is not known to the called function to belong to its stack
       frame, we must build an explicit cleanup.  This case occurs when we
       must build up a reference to pass the reference as an argument.  In
       this case, it is very likely that such a reference need not be built
       here.  */
    
    if (TARGET_EXPR_CLEANUP (exp) == 0)
      TARGET_EXPR_CLEANUP (exp) = (*lang_hooks.maybe_build_cleanup) (decl);

    initializer = TREE_OPERAND (exp, 3) = TARGET_EXPR_INITIAL (exp);
    /* Mark it as expanded.  */
    TARGET_EXPR_INITIAL(exp) = NULL_TREE;

    llvm_store_expr(Fn, initializer, DECL_LLVM(decl), 0, 0, 0,
                    TREE_THIS_VOLATILE(decl));

    if (TARGET_EXPR_CLEANUP (exp))
      llvm_expand_decl_cleanup_eh(Fn, 0, TARGET_EXPR_CLEANUP (exp),
                                  CLEANUP_EH_ONLY(exp));

    Result = DECL_LLVM(decl);
    break;
  }
#endif
  case COMPOUND_LITERAL_EXPR: {
    /* Initialize the anonymous variable declared in the compound
       literal, then return the variable.  */
    tree decl = COMPOUND_LITERAL_EXPR_DECL (exp);
    llvm_emit_local_var(Fn, decl);
    return llvm_expand_lvalue_expr(Fn, decl, BitStart, BitSize);
  }

  case COMPOUND_EXPR:    /* Comma expression */
    llvm_expand_expr(Fn, TREE_OPERAND(exp, 0), 0);
    Result = llvm_expand_lvalue_expr(Fn, TREE_OPERAND(exp, 1),
                                     BitStart, BitSize);
    break;

  case COMPLEX_EXPR:
  case REALPART_EXPR:
  case IMAGPART_EXPR:
    /* Get the address of the complex */
    Result = llvm_expand_lvalue_expr(Fn, TREE_OPERAND(exp, 0), 0, 0);
    /* Get a pointer to the 0th or 1st element */
    Result = append_inst(Fn, create_gep3(Result, llvm_constant_long_0,
         llvm_constant_new_integral(UByteTy, TREE_CODE(exp) == IMAGPART_EXPR)));
    break;

  case CONSTRUCTOR:
    Result = D2V(make_temporary_alloca(Fn, ElTy));
    llvm_expand_expr(Fn, exp, Result);
    break;
  }

  return cast_if_type_not_equal(Fn, Result, Ty);
}

/* InitializeComplex - Initialize the lvalue pointed to by DestLoc with the real
 * and imaginary components specified.
 */
static void InitializeComplex(llvm_function *Fn, llvm_value *DestLoc,
                              llvm_value *Real, llvm_value *Imag,
                              int isVolatile) {
  llvm_instruction *I;
  I = create_gep3(DestLoc, llvm_constant_long_0,
                  llvm_constant_new_integral(UByteTy, 0));
  append_inst(Fn, create_store_inst(Real, append_inst(Fn, I), isVolatile));
  
  I = create_gep3(DestLoc, llvm_constant_long_0,
                  llvm_constant_new_integral(UByteTy, 1));
  append_inst(Fn, create_store_inst(Imag, append_inst(Fn, I), isVolatile));  
}

/* llvm_load_complex_part - Load either the real or imaginary part of a complex
 * number.
 */
static llvm_value *llvm_load_complex_part(llvm_function *Fn,
                                          llvm_value *Complex,
                                          int ImagPart, int isVolatile) {
  llvm_value *Addr =
    append_inst(Fn, create_gep3(Complex, llvm_constant_long_0,
                                llvm_constant_new_integral(UByteTy, ImagPart)));
  return append_inst(Fn, create_load_inst("tmp", Addr, isVolatile));
}


/* llvm_expand_complex_binary_expr - Expand one of the supported binary
 * expressions on complex numbers (including both complex floating point and
 * complex integer).  Supported operations are +, -, *, and /.
 */
static void llvm_expand_complex_binary_expr(llvm_function *Fn, tree exp,
                                            llvm_value *DestLoc) {
  llvm_type *DestTy = llvm_type_get_from_tree(TREE_TYPE(exp));  
  llvm_value *Op0 = D2V(make_temporary_alloca(Fn, DestTy));
  llvm_value *Op1 = D2V(make_temporary_alloca(Fn, DestTy));
  llvm_value *Op0r, *Op0i;   /* real and imaginary components. */
  llvm_value *Op1r, *Op1i;
  llvm_value *ResultR, *ResultI;

  /* Expand the two operands, loading real/imag parts... */

  /* FIXME: instead of expanding into temporary values then loading, this should
   * just expand them as lvalues!
   */
  llvm_expand_expr(Fn, TREE_OPERAND(exp, 0), Op0);
  Op0r = llvm_load_complex_part(Fn, Op0, 0, 0);
  Op0i = llvm_load_complex_part(Fn, Op0, 1, 0);
  llvm_expand_expr(Fn, TREE_OPERAND(exp, 1), Op1);
  Op1r = llvm_load_complex_part(Fn, Op1, 0, 0);
  Op1i = llvm_load_complex_part(Fn, Op1, 1, 0);

  switch (TREE_CODE(exp)) {
  case PLUS_EXPR:  /* (a+ib) + (c+id) = (a+c) + i(b+d) */
    ResultR = append_inst(Fn, create_binary_inst("tmp", O_Add, Op0r, Op1r));
    ResultI = append_inst(Fn, create_binary_inst("tmp", O_Add, Op0i, Op1i));
    break;
  case MINUS_EXPR:  /* (a+ib) - (c+id) = (a-c) + i(b-d) */
    ResultR = append_inst(Fn, create_binary_inst("tmp", O_Sub, Op0r, Op1r));
    ResultI = append_inst(Fn, create_binary_inst("tmp", O_Sub, Op0i, Op1i));
    break;
  case MULT_EXPR: {  /* (a+ib) * (c+id) = (ac-bd) + i(ad+cb) */
    llvm_value *Tmp1 =  /* a*c */
      append_inst(Fn, create_binary_inst("tmp", O_Mul, Op0r, Op1r));
    llvm_value *Tmp2 =  /* b*d */
      append_inst(Fn, create_binary_inst("tmp", O_Mul, Op0i, Op1i));
    ResultR = append_inst(Fn, create_binary_inst("tmp", O_Sub, Tmp1, Tmp2));

    /* a*d */
    Tmp1 = append_inst(Fn, create_binary_inst("tmp", O_Mul, Op0r, Op1i));
    /* c*b */
    Tmp2 = append_inst(Fn, create_binary_inst("tmp", O_Mul, Op1r, Op0i));
    ResultI = append_inst(Fn, create_binary_inst("tmp", O_Add, Tmp1, Tmp2));
    break;
  }

  /*case DIV_EXPR:*/  /* (a+ib) / (c+id) = ((ac+bd)/(cc+dd)) + i((bc-ad)/(cc+dd)) */

  default:
    debug_tree(exp);
    assert(0 && "Unknown complex expression!");
  }

  InitializeComplex(Fn, DestLoc, ResultR, ResultI, 0);
}

/* llvm_expand_expr: generate code for computing expression EXP.  If the
 * expression produces a scalar value (which can be held in an LLVM register),
 * an llvm_value* for the computed R-value is returned.  The value is null if
 * the expression returns void.
 *
 * If the computed value is of aggregate type, the DESTLOC argument is a pointer
 * to the memory which the expression should be evaluated into.  This pointer
 * should always be null for scalar values, and may be null for composite
 * expressions whose return value is ignored.
 */
llvm_value *llvm_expand_expr(llvm_function *Fn, tree exp, llvm_value *DestLoc) {
  tree type = TREE_TYPE(exp), context;
  int expVolatile = TYPE_VOLATILE(type);
  llvm_type *DestTy;
  llvm_value *op0, *op1, *Result = 0;
  int isDestTyComposite;

  /* Handle ERROR_MARK before anybody tries to access its type.  */
  if (TREE_CODE(exp) == ERROR_MARK || TREE_CODE (type) == ERROR_MARK)
    return llvm_constant_VoidPtr_null;

  DestTy = llvm_type_get_from_tree(type);
  isDestTyComposite = llvm_type_is_composite(DestTy);

  /* Check to make sure DestLoc is set when it is supposed to be. */
  assert((DestLoc == 0 || isDestTyComposite) &&
         "Cannot specify DestLoc for non-composite types!");

  switch (TREE_CODE(exp)) {
  default: {
    extern llvm_value *lhd_llvm_expand_expr(llvm_function *, tree, llvm_value*);

    if (lang_hooks.llvm_expand_expr != lhd_llvm_expand_expr)
      return (*lang_hooks.llvm_expand_expr)(Fn, exp, DestLoc);
    else {
      LLVM_TODO_TREE(exp);
    }
  }

  case RESULT_DECL:    /* Reading the return value?? */
    LLVM_TODO_TREE(exp);
  case PARM_DECL:      /* Parameter reference */
  case VAR_DECL:       /* Variable reference */
  case INDIRECT_REF:   /* *P reference */
  case ARRAY_REF:      /* A[i] reference */
  case COMPONENT_REF:  /* S.x reference */
  case COMPOUND_LITERAL_EXPR: /* C99 Compound Literal */
    if (TREE_CODE_CLASS(TREE_CODE(exp)) == 'd' ||
        TREE_CODE_CLASS(TREE_CODE(exp)) == 'r')
      expVolatile |= TREE_THIS_VOLATILE(exp);

    /* These are all lvalue expressions, so just compute the address, then load
     * it.
     */
    {
      unsigned BitStart = 0, BitSize = 0;
      op0 = llvm_expand_lvalue_expr(Fn, exp, &BitStart, &BitSize);

      if (!isDestTyComposite) {  /* Return a normal scalar by loading it */
        Result = append_inst(Fn, create_load_inst("tmp", op0, expVolatile));

        /* If this is a read of a bitfield value, we have to mask and shift the
         * cruft out.
         */
        Result = ReadBitField(Fn, Result, BitStart, BitSize);

      } else if (DestLoc) {              /* Generating structure, using value */
        assert(BitSize == 0 && "Invalid bitfield read of composite value!");
        llvm_copy_aggregate(Fn, DestLoc, op0, expVolatile, 0);
      }
    }
    break;                 /* Generating structure, ignoring value */

  case TARGET_EXPR: {      /* Temporary value */
    /* The space for the temporary result has already been allocated.  Just
     * evaluate the RHS into this space.
     */
    tree decl = TARGET_EXPR_SLOT (exp);
    tree initializer;
    int isOrphanedTargetExpr = 0;

    assert(TREE_CODE(decl) == VAR_DECL);
    assert(Fn && "Cannot use TARGET_EXPRs to initialize constants!");

    /* If this isn't a composite value, just expand as an lvalue and load the
     * scalar result.
     */
    if (DECL_LLVM_SET_P(decl)) {
      /* If we have already expanded the decl, so don't do it again. */
      assert(TARGET_EXPR_INITIAL (exp) == NULL_TREE);

      op0 = DECL_LLVM(decl);
      if (!isDestTyComposite) {  /* Return a normal scalar by loading it */
        Result = append_inst(Fn, create_load_inst("tmp", op0, expVolatile));
      } else {
        llvm_copy_aggregate(Fn, DestLoc, op0, expVolatile, 0);
      }
      break;
    }

    /* Since DECL is not known to the called function to belong to its stack
       frame, we must build an explicit cleanup.  This case occurs when we
       must build up a reference to pass the reference as an argument.  In
       this case, it is very likely that such a reference need not be built
       here.  */
    
    if (TARGET_EXPR_CLEANUP (exp) == 0)
      TARGET_EXPR_CLEANUP (exp) = (*lang_hooks.maybe_build_cleanup) (decl);

    /* If this is an orphaned target expression, create a destination location
     * now, and remember that it was orphaned.
     */
    if (!DestLoc) {
      isOrphanedTargetExpr = 1;
      DestLoc = D2V(make_temporary_alloca(Fn, DestTy));
    }

    SET_DECL_LLVM(decl, DestLoc);

    initializer = TREE_OPERAND (exp, 3) = TARGET_EXPR_INITIAL (exp);
    /* Mark it as expanded.  */
    TARGET_EXPR_INITIAL(exp) = NULL_TREE;

    llvm_store_expr(Fn, initializer, DestLoc, 0, 0, 0,
                    TREE_THIS_VOLATILE(decl));

    if (!isDestTyComposite)
      Result = append_inst(Fn, create_load_inst("tmp", DestLoc, expVolatile));

    if (isOrphanedTargetExpr && TARGET_EXPR_CLEANUP(exp))
      llvm_expand_decl_cleanup_eh(Fn, 0, TARGET_EXPR_CLEANUP(exp),
                                  CLEANUP_EH_ONLY(exp));
    break;
  }

  case ADDR_EXPR:        /* & Expression  */
    /* Are we taking the address of a nested function?  */
    if (TREE_CODE (TREE_OPERAND (exp, 0)) == FUNCTION_DECL
        && decl_function_context (TREE_OPERAND (exp, 0)) != 0
        && ! DECL_NO_STATIC_CHAIN (TREE_OPERAND (exp, 0))
        && ! TREE_STATIC (exp)) {
      LLVM_TODO_TREE(exp);
    }
    /* This can never address a bitfield */
    return llvm_expand_lvalue_expr(Fn, TREE_OPERAND(exp, 0), 0, 0);

  case FUNCTION_DECL:  /* Function references are always lvalues */
    Result = llvm_expand_lvalue_expr(Fn, exp, 0, 0);
    break;

  case STRING_CST:
    llvm_expand_constructor(Fn, exp, DestLoc, 0);
    break;
  case CONSTRUCTOR:
    assert(isDestTyComposite && "Constructor for non-composite type?");
    llvm_expand_constructor(Fn, exp, DestLoc, expVolatile);
    return 0;
  case COMPLEX_CST:
    op0 = llvm_expand_expr(Fn, TREE_REALPART(exp), 0);
    op1 = llvm_expand_expr(Fn, TREE_IMAGPART(exp), 0);
    InitializeComplex(Fn, DestLoc, op0, op1, expVolatile);
    break;

  case COMPLEX_EXPR:
    op0 = llvm_expand_expr(Fn, TREE_OPERAND(exp, 0), 0);
    op1 = llvm_expand_expr(Fn, TREE_OPERAND(exp, 1), 0);
    InitializeComplex(Fn, DestLoc, op0, op1, expVolatile);
    break;

  case INTEGER_CST:
  case REAL_CST:
    Result = D2V(llvm_expand_constant_expr(exp, DestTy));
    break;

  case CONST_DECL:
    Result = llvm_expand_expr(Fn, DECL_INITIAL(exp), DestLoc);
    break;

  case CALL_EXPR:         /* Function call */
    /* Check for a built-in function.  */
    if (TREE_CODE (TREE_OPERAND (exp, 0)) == ADDR_EXPR &&
        (TREE_CODE(TREE_OPERAND(TREE_OPERAND(exp, 0), 0)) == FUNCTION_DECL)
        && DECL_BUILT_IN (TREE_OPERAND (TREE_OPERAND (exp, 0), 0))) {
      tree Callee = TREE_OPERAND (TREE_OPERAND (exp, 0), 0);
      if (DECL_BUILT_IN_CLASS (Callee) != BUILT_IN_FRONTEND)
        return llvm_expand_builtin(Fn, exp, DestLoc);
    }
    
    return llvm_expand_call(Fn, exp, DestLoc);
    
  case NON_LVALUE_EXPR:
  case NOP_EXPR:
  case CONVERT_EXPR:    /* Cast expression */
  case FIX_TRUNC_EXPR:  /* FP -> Integer cast */
  case FLOAT_EXPR:      /* Int -> FP cast */
  case REFERENCE_EXPR:
    assert(TREE_OPERAND(exp, 0) != error_mark_node);
    if (TREE_CODE (type) == UNION_TYPE && llvm_type_is_composite(DestTy)) {
      tree valtype = TREE_TYPE (TREE_OPERAND (exp, 0));

      /* If both input and output are BLKmode, this conversion isn't doing
         anything except possibly changing memory attribute.  */
      if (TYPE_MODE(type) == BLKmode && TYPE_MODE (valtype) == BLKmode) {
        return llvm_expand_expr(Fn, TREE_OPERAND (exp, 0), DestLoc);
      }
      LLVM_TODO_TREE(exp);
    }

    Result = llvm_expand_expr(Fn, TREE_OPERAND(exp, 0), DestLoc);
    break;

  case EXPR_WITH_FILE_LOCATION:
    Result = llvm_expand_expr(Fn, EXPR_WFL_NODE(exp), DestLoc);
    break;

  case SAVE_EXPR:
    /* Return the innermost context enclosing DECL that is a FUNCTION_DECL, or
       zero if none.  */
    context = decl_function_context (exp);

    /* If this SAVE_EXPR was at global context, assume we are an
       initialization function and move it into our context.  */
    if (context == 0)
      SAVE_EXPR_CONTEXT (exp) = current_function_decl;

    /* We treat inline_function_decl as an alias for the current function
       because that is the inline function whose vars, types, etc.
       are being merged into the current function.
       See expand_inline_function.  */
    if (context == current_function_decl)
      context = 0;

    /* If this is non-local, handle it.  */
    if (context) LLVM_TODO_TREE(exp);  /* Don't handle nested functions yet! */

    /* If the expression has not been computed yet... */
    if (SAVE_EXPR_LLVM(exp) == 0) {
      llvm_value *Val, *SEVal;
      /* SAVE_EXPRs of non-void values are represented as memory allocated on
       * the stack with an alloca instruction.  These allocas should be
       * completely mem2reg'able, so this should not cause a problem at all.
       */

      if (DestTy == VoidTy)
        Val = llvm_constant_VoidPtr_null;
      else
        Val = D2V(make_temporary_alloca(Fn, DestTy));

      SAVE_EXPR_LLVM(exp) = Val;

      /* Expand the saved expression */
      SEVal = llvm_expand_expr(Fn, TREE_OPERAND(exp, 0), DestLoc);

      TREE_USED(exp) = 1;

      if (DestTy != VoidTy) {
        /* If the value expanded does not match the required type, we must need
           to promote it.  Insert a cast now.
        */
        SEVal = cast_if_type_not_equal(Fn, SEVal, DestTy);

        /* Store the appropriate value into the alloca... */
        append_inst(Fn, create_store_inst(SEVal, Val, 0));

        /* The first time we evaluate the saveexpr, we don't need to reload it
           from the stored value. */
        Result = SEVal;
        break;
      }
    }

    if (DestTy != VoidTy) {
      llvm_value *V = SAVE_EXPR_LLVM(exp);
      /* If this assert fires, we need to insert a cast here */
      assert(GET_POINTER_TYPE_ELEMENT(V->Ty) == DestTy &&
             "SaveExpr used in different type contexts?");

      /* Emit a load of the saved value */
      Result = append_inst(Fn, create_load_inst("se_val", V, 0));
      break;
    }
    return 0;      /* If it is a void expression, return null */

  case UNSAVE_EXPR:
    Result = llvm_expand_expr(Fn, TREE_OPERAND(exp, 0), DestLoc);
    TREE_OPERAND(exp, 0) = lang_hooks.unsave_expr_now(TREE_OPERAND(exp, 0));
    break;

  case NEGATE_EXPR:    /* -A === 0-A */
    op1 = llvm_expand_expr(Fn, TREE_OPERAND(exp, 0), 0);
    op0 = llvm_constant_get_null(op1->Ty);
    Result = append_inst(Fn, create_binary_inst("tmp", O_Sub, op0, op1));
    break;
  case BIT_NOT_EXPR:   /* ~A === A^-1 */
  case TRUTH_NOT_EXPR: /* !A === A^true */
    op0 = llvm_expand_expr(Fn, TREE_OPERAND(exp, 0), 0);
    if (TREE_CODE(exp) == TRUTH_NOT_EXPR)
      op0 = cast_if_type_not_equal(Fn, op0, BoolTy);

    switch (op0->Ty->ID) {
    case BoolTyID:   op1= llvm_constant_new(BoolTy, "true"); break;
    case SByteTyID: 
    case ShortTyID: 
    case IntTyID:   
    case LongTyID:   op1 = llvm_constant_new(op0->Ty, "-1"); break;
    case UByteTyID:  op1 = llvm_constant_new(UByteTy, "255"); break;
    case UShortTyID: op1 = llvm_constant_new(UShortTy, "65535"); break;
    case UIntTyID:   op1 = llvm_constant_new(UIntTy, "4294967295"); break;
    case ULongTyID:op1=llvm_constant_new(ULongTy, "18446744073709551615");break;
    default: LLVM_TODO_TREE(exp);  /* Unexpected type for ~ expr */
    }

    Result = append_inst(Fn, create_binary_inst("tmp", O_Xor, op0, op1));
    break;

  case MAX_EXPR: case MIN_EXPR:                            /* min, max */
  case EXACT_DIV_EXPR:
  case PLUS_EXPR: case MINUS_EXPR: case MULT_EXPR:         /* Plus, Sub, Mult */
  case TRUNC_DIV_EXPR: case TRUNC_MOD_EXPR: case RDIV_EXPR:/* Division, Rem   */
  case BIT_AND_EXPR: case BIT_IOR_EXPR: case BIT_XOR_EXPR: /* Bit operators */
  case TRUTH_AND_EXPR: case TRUTH_OR_EXPR: case TRUTH_XOR_EXPR: /* Bit ops */
  case LSHIFT_EXPR: case RSHIFT_EXPR:                      /* Shifts */
  case LT_EXPR: case LE_EXPR: case GT_EXPR:                /* Comparisons */
  case GE_EXPR: case EQ_EXPR: case NE_EXPR: {              /* Comparisons */
    enum InstOpcode Opcode;

    if (llvm_type_is_composite(DestTy)) {
      llvm_expand_complex_binary_expr(Fn, exp, DestLoc);
      return 0;
    }

    op0 = llvm_expand_expr(Fn, TREE_OPERAND(exp, 0), 0);
    op1 = llvm_expand_expr(Fn, TREE_OPERAND(exp, 1), 0);

    if ((TREE_CODE(exp) == PLUS_EXPR || TREE_CODE(exp) == MINUS_EXPR) &&
        DestTy->ID == PointerTyID && op0->Ty->ID == PointerTyID) {
      /* Attempt to convert an ADD or SUB expression operand on pointer types
       * into a getelementptr instruction.
       */
      llvm_value *V = llvm_expand_pointer_addsub(Fn, TREE_CODE(exp)==PLUS_EXPR,
                                                 op0, op1, DestTy);
      if (V) return V;
    }

    /* Attempt to unify the types of the left and right operand... */
    if (TREE_CODE(TREE_OPERAND(exp, 1)) == INTEGER_CST)
      op1 = cast_if_type_not_equal(Fn, op1, op0->Ty);

    /* If the types don't match, but have the same basic type (as in, they are
     * pointers to different types), cast one operand to the other.
     */
    if (op0->Ty != op1->Ty) {
      if (op0->Ty->ID == op1->Ty->ID)
        op1 = cast_if_type_not_equal(Fn, op1, op0->Ty);
      else if (llvm_type_get_size(op0->Ty) == llvm_type_get_size(op1->Ty)) {
        if ((llvm_type_is_integral(op0->Ty) || op0->Ty->ID == PointerTyID) &&
            (llvm_type_is_integral(op1->Ty) || op1->Ty->ID == PointerTyID))
          op1 = cast_if_type_not_equal(Fn, op1, op0->Ty);
      }
    }

    switch (TREE_CODE(exp)) {
    case PLUS_EXPR:       Opcode = O_Add; break;
    case MINUS_EXPR:      Opcode = O_Sub; break;
    case MULT_EXPR:       Opcode = O_Mul; break;
    case MIN_EXPR: case MAX_EXPR: Opcode = O_Call; break;  /* special code. */
    case TRUNC_DIV_EXPR: case EXACT_DIV_EXPR:
    case RDIV_EXPR:       Opcode = O_Div; break;
    case TRUNC_MOD_EXPR:  Opcode = O_Rem; break;
    case TRUTH_AND_EXPR: case BIT_AND_EXPR:    Opcode = O_And; break;
    case TRUTH_OR_EXPR:  case BIT_IOR_EXPR:    Opcode = O_Or; break;
    case TRUTH_XOR_EXPR: case BIT_XOR_EXPR:    Opcode = O_Xor; break;
    case LT_EXPR:         Opcode = O_SetLT; break;
    case LE_EXPR:         Opcode = O_SetLE; break;
    case GT_EXPR:         Opcode = O_SetGT; break;
    case GE_EXPR:         Opcode = O_SetGE; break;
    case EQ_EXPR:         Opcode = O_SetEQ; break;
    case NE_EXPR:         Opcode = O_SetNE; break;
    case LSHIFT_EXPR:     Opcode = O_Shl;   break;
    case RSHIFT_EXPR:     Opcode = O_Shr;   break;
    default: abort();
    }

    /* Deal with special cases used by particular opcodes. */
    switch (TREE_CODE(exp)) {
    case TRUTH_AND_EXPR:
    case TRUTH_OR_EXPR:
    case TRUTH_XOR_EXPR:  /* Ensure the operands are boolean values. */
      op0 = cast_if_type_not_equal(Fn, op0, BoolTy);
      op1 = cast_if_type_not_equal(Fn, op1, BoolTy);
      break;

    case LSHIFT_EXPR:
    case RSHIFT_EXPR:     /* Shift amount -> ubyte */
      op1 = cast_if_type_not_equal(Fn, op1, UByteTy);
      break;

    case NE_EXPR:
    case EQ_EXPR:  /* Handle case where comparing: int <op> uint */
      if (op0->Ty == op1->Ty) break;

      assert(llvm_type_is_integral(op0->Ty));
      assert(llvm_type_is_integral(op1->Ty));
      assert(llvm_type_get_size(op0->Ty) == llvm_type_get_size(op1->Ty));

      /* Convert one to the other. */
      op1 = cast_if_type_not_equal(Fn, op1, op0->Ty);
    case LT_EXPR:
    case LE_EXPR:
    case GT_EXPR:
    case GE_EXPR:
      break;

    default:
      if (Opcode < O_SetEQ && (op0->Ty->ID == PointerTyID || 
                               op1->Ty->ID == PointerTyID)) {
        /* Disallow pointer arithmetic. */
        op0 = cast_if_type_not_equal(Fn, op0, LongTy);
        op1 = cast_if_type_not_equal(Fn, op1, LongTy);
        break;
      }

      if (op0->Ty == op1->Ty) break;
      assert(llvm_type_is_integral(op0->Ty));
      assert(llvm_type_is_integral(op1->Ty));
      assert(llvm_type_is_integral(DestTy));
      assert(llvm_type_get_size(op0->Ty) == llvm_type_get_size(op1->Ty));
      assert(llvm_type_get_size(op0->Ty) == llvm_type_get_size(DestTy));

      /* Convert both arguments to the result type. */
      op0 = cast_if_type_not_equal(Fn, op0, DestTy);
      op1 = cast_if_type_not_equal(Fn, op1, DestTy);
      break;
    }

    assert((op0->Ty == op1->Ty || Opcode == O_Shl || Opcode == O_Shr) &&
           "Binary operator argument types not same!");

    if (Opcode != O_Call)
      Result = append_inst(Fn, create_binary_inst("tmp", Opcode, op0, op1));
    else   /* Min or Max */
      Result = llvm_expand_minmaxabs_expr(Fn, exp, op0, op1);
    break;
  }
  case ABS_EXPR: {
    op0 = llvm_expand_expr(Fn, TREE_OPERAND(exp, 0), 0);
    op1 = llvm_constant_get_null(op0->Ty);
    Result = llvm_expand_minmaxabs_expr(Fn, exp, op0, op1);
    break;
  }
  case TRUTH_ANDIF_EXPR:
  case TRUTH_ORIF_EXPR:
    Result = llvm_expand_shortcircuit_truth_expr(Fn, exp);
    break;

  case COMPOUND_EXPR: {   /* Comma expression */
    llvm_expand_expr(Fn, TREE_OPERAND(exp, 0), 0);
    Result = llvm_expand_expr(Fn, TREE_OPERAND(exp, 1), DestLoc);
    break;
  }
  case COND_EXPR: {      /* ?: expression */
    /* FIXME: This does not correctly conditionalize CLEANUP expressions because
       no scopes are created!!! */

    /* Allocate a new temporary to hold the result of the expression */
    llvm_basicblock *TrueBlock = llvm_basicblock_new("cond_true");
    llvm_basicblock *FalseBlock = llvm_basicblock_new("cond_false");
    llvm_basicblock *ContinueBlock = llvm_basicblock_new("cond_continue");

    /* Expand condition and branch */
    llvm_value *Cond = llvm_expand_expr(Fn, TREE_OPERAND(exp, 0), 0);
    if (DestLoc) {       /* This is an aggregate ?: expression */
      Result = DestLoc;
    } else {
      Result = DestTy != VoidTy ? D2V(make_temporary_alloca(Fn, DestTy)) : 0;
    }
    Cond = cast_if_type_not_equal(Fn, Cond, BoolTy);
    append_inst(Fn, create_cond_branch(Cond, TrueBlock, FalseBlock));
    
    /* Add the true block as the fall through */
    llvm_ilist_push_back(llvm_basicblock, Fn->BasicBlocks, TrueBlock);

    /* One branch of the cond can be void, if it never returns. For
       example A ? throw : E  */
    if (Result && TREE_TYPE(TREE_OPERAND(exp, 1)) != void_type_node)
      llvm_store_expr(Fn, TREE_OPERAND(exp, 1), Result, 0, 0, 0, 0);
    else
      llvm_expand_expr(Fn, TREE_OPERAND (exp, 1), 0);

    /* Branch to the mainline computation */
    append_inst(Fn, create_uncond_branch(ContinueBlock));

    /* Add the false block next */
    llvm_ilist_push_back(llvm_basicblock, Fn->BasicBlocks, FalseBlock);

    if (Result && TREE_TYPE(TREE_OPERAND(exp, 2)) != void_type_node)
      llvm_store_expr(Fn, TREE_OPERAND(exp, 2), Result, 0, 0, 0, 0);
    else
      llvm_expand_expr(Fn, TREE_OPERAND (exp, 2), 0);

    /* Add the branch and continue block */
    llvm_emit_label(Fn, ContinueBlock);
    
    /* Load the result out of the temporary */
    if (Result && !isDestTyComposite)
      Result = append_inst(Fn, create_load_inst("tmp", Result, 0));
    else 
      Result = 0;        /* We produce a composite value */
    break;
  }

  case INIT_EXPR:        /* initialization of a variable */
  case MODIFY_EXPR:      /* = expression */
    /* Expand the assignment out.  The result of a modify expr is the value
       produced, not the lvalue returned by llvm_expand_assignment.  */
    llvm_expand_assignment(Fn, TREE_OPERAND (exp, 0),
                           TREE_OPERAND (exp, 1), &Result);
    break;

  case PREINCREMENT_EXPR:  return llvm_expand_increment(Fn, exp, 1, 1);
  case PREDECREMENT_EXPR:  return llvm_expand_increment(Fn, exp, 0, 1);
  case POSTINCREMENT_EXPR: return llvm_expand_increment(Fn, exp, 1, 0);
  case POSTDECREMENT_EXPR: return llvm_expand_increment(Fn, exp, 0, 0);


  case BIT_FIELD_REF: /* Reference to a group of bits within an object.  */
    Result = llvm_expand_bitfield_ref(Fn, exp);
    break;

  case EXIT_EXPR:
    llvm_expand_exit_loop_if_false(Fn, 0,
                                   invert_truthvalue(TREE_OPERAND(exp, 0)));
    return 0;

  case LOOP_EXPR:
    llvm_expand_start_loop(Fn, 1);
    llvm_expand_expr_stmt_value(Fn, TREE_OPERAND(exp, 0), 1);
    llvm_expand_end_loop(Fn);
    return 0;

  case REALPART_EXPR:
  case IMAGPART_EXPR:
    /* Expand the complex operand into a temporary memory location. */
    /* FIXME: as an lvalue! */
    op0 = D2V(make_temporary_alloca(Fn,
                    llvm_type_get_from_tree(TREE_TYPE(TREE_OPERAND(exp, 0)))));
    llvm_expand_expr(Fn, TREE_OPERAND(exp, 0), op0);

    /* Load the portion we want. */
    Result = llvm_load_complex_part(Fn, op0, TREE_CODE(exp) == IMAGPART_EXPR,
                                    expVolatile);
    break;
  case BIND_EXPR: {
    tree vars = TREE_OPERAND(exp, 0);
    
    /* Start a new binding layer that will keep track of all cleanup actions to
       be performed.  */
    llvm_expand_start_bindings(Fn);
    
    /* Mark the corresponding BLOCK for output in its proper place.  */
    if (TREE_OPERAND(exp, 2) != 0 && !TREE_USED(TREE_OPERAND(exp, 2))) {
      LLVM_TODO_TREE(TREE_OPERAND(exp, 2));
      (*lang_hooks.decls.insert_block)(TREE_OPERAND(exp, 2));
    }

    /* If VARS have not yet been expanded, expand them now.  */
    for (; vars; vars = TREE_CHAIN(vars)) {
      if (!DECL_LLVM_SET_P(vars))
        llvm_expand_decl(Fn, vars);
      llvm_expand_decl_init(Fn, vars);
    }

    op0 = llvm_expand_expr(Fn, TREE_OPERAND(exp, 1), DestLoc);
    
    /* End the bindings level */
    llvm_expand_end_bindings(Fn, 0);
    Result = op0;
    break;
  }

  case VA_ARG_EXPR:
    op0 = llvm_expand_lvalue_expr(Fn, TREE_OPERAND(exp, 0), 0, 0);
    if (llvm_type_is_composite(DestTy)) {
      assert(DestLoc && GET_POINTER_TYPE_ELEMENT(DestLoc->Ty) == DestTy &&
             "Invalid type for aggregate va_arg expression!");
      llvm_get_composite_vararg(Fn, op0, DestLoc);
    } else {
      Result = llvm_get_scalar_vararg(Fn, op0, DestTy);
    }
    break;

   case CLEANUP_POINT_EXPR:
     /* Start a new binding layer that will keep track of all cleanup
        actions to be performed.  */
     llvm_expand_start_bindings(Fn);
     Result = llvm_expand_expr(Fn, TREE_OPERAND(exp, 0), DestLoc);
     
     /* End the bindings level */
     llvm_expand_end_bindings(Fn, 0);
     break;
  
  case EXC_PTR_EXPR:
    fprintf(stderr, "case EXC_PTR_EXPR: SHOULD GO AWAY!  Eliminate all callers of build_exc_ptr!\n");
    debug_tree(exp);
    Result = llvm_constant_VoidPtr_null; /*llvm_get_exception_pointer(Fn);*/
    break;
  }

  if (Result == 0 || DestTy == VoidTy)
    return 0;
  return cast_if_type_not_equal(Fn, Result, DestTy);
}

/* c_llvm_expand_expr - Corresponds to c_expand_expr, used by the C frontend
 * (and chained to by the C++ frontend to expand C specific tree nodes
 */
struct llvm_value *c_llvm_expand_expr(struct llvm_function *Fn, tree exp,
                                      struct llvm_value *DestLoc) {
  llvm_value *Tmp;
  switch (TREE_CODE(exp)) {
  default:
    LLVM_TODO_TREE(exp);

  case STMT_EXPR:
    Tmp = Fn->ExpandInfo->last_expr_value_location; /* Save stack */
    Fn->ExpandInfo->last_expr_value_location = DestLoc;
    llvm_expand_stmt(Fn, STMT_EXPR_STMT(exp));
    Fn->ExpandInfo->last_expr_value_location = Tmp;

    if (!VOID_TYPE_P(TREE_TYPE(exp)))
      return Fn->ExpandInfo->last_expr_value;

    /* Otherwise, it returns void */
    return 0;
  }
  return 0;
}

llvm_value *c_llvm_expand_lvalue_expr(llvm_function *Fn, tree exp,
                                      unsigned *BitStart, unsigned *BitSize) {
  switch (TREE_CODE(exp)) {
  case STMT_EXPR: {
    llvm_value *Tmp = Fn->ExpandInfo->last_expr_value_location; /* Save stack */
    llvm_value *Dest =
      D2V(make_temporary_alloca(Fn, llvm_type_get_from_tree(TREE_TYPE(exp))));

    /* Create a temporary to expand the value into... */
    Fn->ExpandInfo->last_expr_value_location = Dest;

    llvm_expand_stmt(Fn, STMT_EXPR_STMT(exp));
    Fn->ExpandInfo->last_expr_value_location = Tmp;

    assert(!VOID_TYPE_P(TREE_TYPE(exp)) && "Void lvalue expr??");
    return Dest;
  }
  default:
    LLVM_TODO_TREE(exp);
  }

  return 0;
}



/*===----------------------------------------------------------------------===**
                     ... Function Start/End Expansion ...
 *===----------------------------------------------------------------------===*/


/* AddArguments - Given a PARAM_DECL, add appropriate arguments to the specified
 * function, and insert store instructions to store the actual argument into the
 * specified memory location.
 */
static void AddArguments(llvm_function *Fn, llvm_type *Ty, const char *Name,
                         llvm_value *Address, unsigned *ArgNo) {
  if (!llvm_type_is_composite(Ty)) {
    llvm_type *FuncTy = GET_POINTER_TYPE_ELEMENT(G2V(Fn)->Ty);
    llvm_type *ArgTy = Ty;
    llvm_argument *Arg;

    if (*ArgNo < GET_FUNCTION_TYPE_NUMARGS(FuncTy) && 
        ArgTy != GET_FUNCTION_TYPE_ARGUMENT(FuncTy, *ArgNo)) {
      fprintf(stderr, "WARNING: Function declared to have type '");
      llvm_type_print(GET_FUNCTION_TYPE_ARGUMENT(FuncTy, *ArgNo), stderr);
      fprintf(stderr, "' but it actually has type '");
      llvm_type_print(ArgTy, stderr);
      ArgTy = GET_FUNCTION_TYPE_ARGUMENT(FuncTy, *ArgNo);
      fprintf(stderr, "'!\n");
    }

    Arg = llvm_argument_new(ArgTy, Name);
    llvm_ilist_push_back(llvm_argument, Fn->Arguments, Arg);
    if (Address) {
      llvm_value *ArgV = cast_if_type_not_equal(Fn, D2V(Arg),
                                        GET_POINTER_TYPE_ELEMENT(Address->Ty));
      append_inst(Fn, create_store_inst(ArgV, Address, 0));
    }
    ++*ArgNo;
  } else {
    /* Composite arguments require the addition of one argument for
     *  each element... to be nice, name each argument something different.
     */
    unsigned i, NameLen = strlen(Name);
    char *SubName = (char*)xmalloc(NameLen+6); /* Should use alloca, oh well */
    llvm_type *ElIdxTy = Ty->ID == StructTyID ? UByteTy : LongTy;
    strcpy(SubName, Name);
    for (i = 0; i != llvm_type_get_composite_num_elements(Ty); ++i) {
      llvm_type *ElTy = llvm_type_get_composite_element(Ty, i);
      /* Create a getelementptr instruction to access the subelements of the
       * structure...
       */
      llvm_value *Offset = 0;
      if (Address) {
        llvm_instruction *GEP = 0;
        sprintf(SubName+NameLen, ".%d", i);
        GEP = create_gep3(Address, llvm_constant_long_0,
                          llvm_constant_new(ElIdxTy, SubName+NameLen+1));
        Offset = append_inst(Fn, GEP);  /* Add the inst to the stream */
      }
      AddArguments(Fn, ElTy, SubName, Offset, ArgNo);
    }
    free(SubName);
  }
}



/* GetFunctionDeclType - This code is here to deal with a problem that occurs
 * when a forward declaration doesn't have a correct type signature.  When the
 * real definition of the function comes around (if it is a K&R style
 * declaration), GCC does not update the TREE_TYPE for the function decl, thus,
 * the function type may not match up with the arguments present.  To handle
 * this case, we build a new function type, from the arguments present.  The
 * -funcresolve pass will resolve the two together.
 */
static llvm_type *GetFunctionDeclType(tree fd) {
  llvm_type *BaseType = llvm_type_get_from_tree(TREE_TYPE(fd));
  llvm_type *RetType;
  int isExternal = !DECL_SAVED_TREE(fd);  /* no body? */
  tree Args;
  unsigned NumArgs = 0;
  assert(TREE_CODE(fd) == FUNCTION_DECL);
  
  if (isExternal) return BaseType;  /* Still external, used declared type. */

  /* Count the number of arguments. */
  RetType = VoidTy;
  if (DECL_RESULT(fd)) {
    RetType = llvm_type_get_from_tree(TREE_TYPE(DECL_RESULT(fd)));
    if (llvm_type_is_composite(RetType)) {
      RetType = VoidTy;
      ++NumArgs;
    }
  }

  if (!DECL_ARGUMENTS(fd) || BaseType->NumElements > NumArgs+1)
    return BaseType;  /* Not a K&R style declaration */

  for (Args = DECL_ARGUMENTS(fd); Args; Args = TREE_CHAIN(Args)) {
    llvm_type *Ty = llvm_type_get_from_tree(TREE_TYPE(Args));
    NumArgs += llvm_type_get_num_recursive_elements(Ty);
  }
  
  BaseType = llvm_type_create_function(NumArgs, RetType);
  NumArgs = 1;

  if (DECL_RESULT(fd)) {
    RetType = llvm_type_get_from_tree(TREE_TYPE(DECL_RESULT(fd)));
    if (llvm_type_is_composite(RetType))
      BaseType->Elements[NumArgs++] = llvm_type_get_pointer(RetType);
  }

  for (Args = DECL_ARGUMENTS(fd); Args; Args = TREE_CHAIN(Args)) {
    llvm_type *Ty = llvm_type_get_from_tree(TREE_TYPE(Args));
    NumArgs += SetFunctionArgs(BaseType, NumArgs, Ty);
  }
  
  return llvm_type_get_cannonical_version(BaseType);
}


/* Initialize the function, adding arguments to the function as appropriate.
   Set up parameters and prepare for return, for the function.  If subr is an
   external function, we just set up the arguments.
*/
llvm_function *llvm_expand_function_start(tree subr, int parms_have_cleanups) {
  tree Args = DECL_ARGUMENTS(subr);
  llvm_function *Fn;
  llvm_type *FnTy = GetFunctionDeclType(subr);
  llvm_type *PFnTy;
  int isExternal = !DECL_SAVED_TREE(subr);  /* no body, YET */
  llvm_type *DeclResultTy;
  int ReturnsComposite = 0;

  if (!isExternal && FnTy->x.Function.isVarArg && Args == 0) {
    /* Check to see if this is a false varargs function.  In C, declaring a
     * function with an argument list of () will cause it to be treated as
     * (...).  When a function body is provided, there is no way they could call
     * va_start if there are _zero_ arguments to the function, besides the ...,
     * so we can safely remove the varargsness.
     */
    llvm_type *NewFn = llvm_type_create_function(FnTy->NumElements-1,
                                                 FnTy->Elements[0]);
    /* Do not set the vararg flag, but if we are returning a structure by value,
     * copy it over...
     */
    assert(FnTy->NumElements < 3 && "Inappropriate number of arguments!");
    if (FnTy->NumElements == 2)
      NewFn->Elements[1] = FnTy->Elements[1];
    FnTy = llvm_type_get_cannonical_version(NewFn);    
  }

  PFnTy = llvm_type_get_pointer(FnTy);

  if (!DECL_LLVM_SET_P(subr) || DECL_LLVM(subr)->Ty != PFnTy) {
    const char *ExternalName = IDENTIFIER_POINTER(DECL_ASSEMBLER_NAME(subr));
    llvm_value *GlobalVal = llvm_get_global_alias(ExternalName);
    if (!GlobalVal || GlobalVal->Ty != PFnTy) {
      const char *PName = (*lang_hooks.decl_printable_name)(subr, 2);
      
      Fn = llvm_function_new(FnTy, ExternalName);
      if (PName && strcmp(PName, G2V(Fn)->Name))
        Fn->PrettyFunctionName = xstrdup(PName);
      
      /* Add the LLVM Function to the program */
      llvm_ilist_push_back(llvm_function, TheProgram.Functions, Fn);
      
      GlobalVal = G2V(Fn);
    }

    /* Associate this LLVM function with the tree function. */
    SET_DECL_LLVM(subr, GlobalVal);
  }

  Fn = (llvm_function*)DECL_LLVM(subr);

  /* No more processing for external functions. */
  if (isExternal) return Fn;

  if (!TREE_PUBLIC(subr))
    Fn->Linkage = L_Internal;
  else if (DECL_DECLARED_INLINE_P(subr)) {
#if 0
    Fn->Linkage = L_LinkOnce;
#else
    /* FIXME: this breaks explicitly instantiated templates! */
    Fn->Linkage = L_Weak;
#endif
  } else if (DECL_WEAK(subr))
    Fn->Linkage = L_Weak;

  /* Scan the list of functions already processed, to see if there is already
   * one of this type.  If so, make the old function forward to its new body.
   * This can occur for code like this:
   * 
   * static void foo();      // declares foo as void(...)
   * int main() { foo(); }
   * static void foo() {}    // changes foo to be void()
   */
  {
    llvm_function *I = llvm_ilist_begin(TheProgram.Functions);
    for (; I; I = llvm_ilist_next(I))
      if (I->ForwardedFunction == 0 && !strcmp(G2V(I)->Name, G2V(Fn)->Name) &&
          I != Fn) {
        /* We found a function with the same name.  Set up forwarding now! */
        I->ForwardedFunction = Fn;
        break;
      }
  }

  assert(llvm_ilist_empty(llvm_basicblock, Fn->BasicBlocks) &&
         "Function already has a body!");
  assert(llvm_ilist_empty(llvm_argument, Fn->Arguments) &&
         "Function already has arguments!");

  /* If the function returns a structure by value, we transform the function to
   * take a pointer to the result as the first argument of the function instead.
   */
  DeclResultTy = 0;
  if (DECL_RESULT(subr)) {
    DeclResultTy = llvm_type_get_from_tree(TREE_TYPE(DECL_RESULT(subr)));
    if (llvm_type_is_composite(DeclResultTy)) {
      llvm_argument *Arg =llvm_argument_new(llvm_type_get_pointer(DeclResultTy),
                                            "agg.result");
      llvm_ilist_push_back(llvm_argument, Fn->Arguments, Arg);
      SET_DECL_LLVM(DECL_RESULT(subr), D2V(Arg));
      ReturnsComposite = 1;
    }
  }
  
  /* Create a new basic block for expansion to add to... */
  llvm_ilist_push_back(llvm_basicblock, Fn->BasicBlocks,
                       llvm_basicblock_new("entry"));
    
  /* Loop over all of the arguments to the function, handling structures
     passed by value if they occur.  Because all decls may be treated as
     lvalues in the function, we copy these arguments into locally alloca'd
     values so that their address is exposed */
  {
    extern int isPassedByInvisibleReference(tree Type);
    unsigned ArgNo = ReturnsComposite ? 1 : 0;
    for (; Args; Args = TREE_CHAIN(Args)) {
      llvm_instruction *A = 0;
      const char *Name = "";
      llvm_type *Ty = llvm_type_get_from_tree(TREE_TYPE(Args));
      int isLValue = 0;

      if (isPassedByInvisibleReference(TREE_TYPE(Args))) {
        Ty = llvm_type_get_pointer(Ty);
        isLValue = 1;
      }

      if (DECL_NAME(Args)) Name = IDENTIFIER_POINTER(DECL_NAME(Args));
      if (Name[0] && !isLValue) {   /* Only create values for named arguments */
        A = create_alloca_inst(Name, Ty, llvm_constant_uint_1);
        insert_alloca_into_entry_block(Fn, A);
        SET_DECL_LLVM(Args, D2V(A));  /* Remember lvalue address */
      } else {
        Name = "unnamed_arg";  /* we want llvm_value's to have names! */
      }
      AddArguments(Fn, Ty, Name, D2V(A), &ArgNo);

      /* If the value is passed by "invisible reference", the l-value for the
       * argument IS the argument itself.
       */
      if (isLValue) {
        SET_DECL_LLVM(Args, D2V(llvm_ilist_back(llvm_argument, Fn->Arguments)));
      }
    }
  }

  /* Allocate a new ExpandInfo object for the function */
  Fn->ExpandInfo = (llvm_expand_info*)xcalloc(sizeof(llvm_expand_info), 1);

  /* If the parameters of this function need cleaning up, get a label
     for the beginning of the code which executes those cleanups.
     This must be done before doing anything with ReturnBlock.  */
  if (parms_have_cleanups) {
    LLVM_TODO_TREE(subr);
    Fn->ExpandInfo->CleanupBlock = llvm_basicblock_new("param_cleanup");
  }

  /* Make the block for return statements to jump to. */
  Fn->ExpandInfo->ReturnBlock = llvm_basicblock_new("return");

  /* If the function doesn't return void, initialize the "RESULT_DECL" */
  if (DeclResultTy && DeclResultTy != VoidTy &&
      !DECL_LLVM_SET_P(DECL_RESULT(subr)))
    llvm_expand_decl(Fn, DECL_RESULT(subr));

  /*assert(!current_function_needs_context && "Case not handled!");*/
  TREE_ASM_WRITTEN(subr) = 1;

  return Fn;
}

/* Expand a call to __main at the beginning of a possible main function.  */
void llvm_expand_main_function(llvm_function *Fn) {
  llvm_value *F = G2V(CreateIntrinsicFunction("__main",
                        build_function_type(void_type_node, void_list_node)));
  llvm_instruction *I = llvm_instruction_new(VoidTy, "", O_Call, 1);
  I->Operands[0] = F;
  append_inst(Fn, I);
}

void llvm_emit_call_to_llvmunwind(llvm_function *Fn) {
  append_inst(Fn, llvm_instruction_new(VoidTy, "", O_Unwind, 0));

  /* Start a new block so that if statements are emitted after the unwind, that
   * they will have the correct "current block".
   */
  llvm_emit_label(Fn, llvm_basicblock_new("dead_block"));
}


void llvm_expand_function_end(llvm_function *Fn, tree subr, int end_bindings) {
  llvm_type *RetTy;
  /*assert(trampoline_list == 0);*/

  /* Warn about unused parms if extra warnings were specified.  */
  /* Either ``-Wextra -Wunused'' or ``-Wunused-parameter'' enables this
     warning.  WARN_UNUSED_PARAMETER is negative when set by
     -Wunused.  Note that -Wall implies -Wunused, so ``-Wall -Wextra'' will
     also give these warnings.  */
  if (warn_unused_parameter > 0)
    {
      tree decl;

      for (decl = DECL_ARGUMENTS (current_function_decl);
	   decl; decl = TREE_CHAIN (decl))
	if (! TREE_USED (decl) && TREE_CODE (decl) == PARM_DECL
	    && DECL_NAME (decl) && ! DECL_ARTIFICIAL (decl))
          warning ("%Hunused parameter '%D'",
                   &DECL_SOURCE_LOCATION (decl), decl);
    }

  /* If there is no terminator on the last block emitted, emit a jump to the
     return block now. */
  if (!EndOfFunctionUnreachable(Fn))
    append_inst(Fn, create_uncond_branch(Fn->ExpandInfo->ReturnBlock));

  /* Output the label for the actual return from the function. */
  llvm_ilist_push_back(llvm_basicblock, Fn->BasicBlocks,
                       Fn->ExpandInfo->ReturnBlock);

  /* If the function returns a value, get it into a register and return it
     now. */
  RetTy = GET_FUNCTION_TYPE_RETURN(GET_POINTER_TYPE_ELEMENT(G2V(Fn)->Ty));
  if (RetTy != VoidTy){
    llvm_instruction *Ret = llvm_instruction_new(VoidTy, "", O_Ret, 1);
    llvm_value *RetValLoc = DECL_LLVM(DECL_RESULT(subr));
    Ret->Operands[0] = append_inst(Fn, create_load_inst("tmp", RetValLoc, 0));
    Ret->Operands[0] = cast_if_type_not_equal(Fn, Ret->Operands[0], RetTy);
    append_inst(Fn, Ret);
  } else {
    /* Otherwise, just return */
    append_inst(Fn, llvm_instruction_new(VoidTy, "", O_Ret, 0));
  }

  assert(!Fn->ExpandInfo->CleanupBlock && "Cleanupblock not handled yet!");

  /* C++ uses this.  */
  if (end_bindings) {
    LLVM_TODO();
    expand_end_bindings (0, 0, 0);
  }

#if 0
  /* If this is an implementation of throw, do what's necessary to
     communicate between __builtin_eh_return and the epilogue.  */
  expand_eh_return ();
#endif

  if (Fn->ExpandInfo->RethrowBlock) {
    llvm_ilist_push_back(llvm_basicblock, Fn->BasicBlocks, 
                         Fn->ExpandInfo->RethrowBlock);
    llvm_emit_call_to_llvmunwind(Fn);
    llvm_expand_dummy_return(Fn, 1);
  }
  if (Fn->ExpandInfo->TerminateBlock) {
    llvm_instruction *Call;
    llvm_ilist_push_back(llvm_basicblock, Fn->BasicBlocks, 
                         Fn->ExpandInfo->TerminateBlock);
    Call = llvm_instruction_new(VoidTy, "", O_Call, 1);
    Call->Operands[0] =
      G2V(CreateIntrinsicFunction("__llvm_cxxeh_call_terminate",
                          build_function_type(void_type_node, void_list_node)));
                                                    
    append_inst(Fn, Call);
    llvm_expand_dummy_return(Fn, 1);
  }

  /* Expand any fixups due to gotos to the return label */
  llvm_fixup_gotos(Fn, 0);
  assert(Fn->ExpandInfo->GotoFixupList == 0 && "Goto fixups remain?");

  /* Reset the identifier rename table now that we are out of function scope */
  ResetIdentifierTableForEndOfFunction();

  assert(Fn->ExpandInfo->GotoFixupList == 0 &&
         Fn->ExpandInfo->InnermostScope == 0);         
  free(Fn->ExpandInfo);
  Fn->ExpandInfo = 0;
}


/* llvm_make_decl_llvm - The LLVM equivalent of make_decl_rtl:

   Create the DECL_LLVM for a VAR_DECL or FUNCTION_DECL.  DECL should have
   static storage duration.  In other words, it should not be an automatic
   variable, including PARM_DECLs.

   There is, however, one exception: this function handles variables explicitly
   placed in a particular register by the user.

   ASMSPEC, if not 0, is the string which the user specified as the
   assembler symbol name. */
extern int decode_reg_name(const char *);
void llvm_make_decl_llvm(tree decl, const char *asmspec) {
  int top_level = (DECL_CONTEXT (decl) == NULL_TREE);
  const char *name = 0, *new_name = 0;
  int reg_number;

  /* Check that we are not being given an automatic variable.  */
  /* A weak alias has TREE_PUBLIC set but not the other bits.  */
  if (TREE_CODE (decl) == PARM_DECL
      || TREE_CODE (decl) == RESULT_DECL
      || (TREE_CODE (decl) == VAR_DECL
          && !TREE_STATIC (decl)
          && !TREE_PUBLIC (decl)
          && !DECL_EXTERNAL (decl)
          && !DECL_REGISTER (decl)))
    abort ();
  /* And that we were not given a type or a label.  */
  else if (TREE_CODE (decl) == TYPE_DECL
           || TREE_CODE (decl) == LABEL_DECL)
    abort ();

  /* For a duplicate declaration, we can be called twice on the
     same DECL node.  Don't discard the LLVM already made.  */
  if (DECL_LLVM_SET_P(decl))
    return;

  new_name = name = IDENTIFIER_POINTER (DECL_ASSEMBLER_NAME (decl));

  reg_number = decode_reg_name (asmspec);
  if (reg_number == -2) {
    /* ASMSPEC is given, and not the name of a register.  Mark the
       name with a star so assemble_name won't munge it.  */
    char *starred = alloca (strlen (asmspec) + 2);
    starred[0] = '*';
    strcpy (starred + 1, asmspec);
    new_name = starred;
  }

  if (TREE_CODE(decl) != FUNCTION_DECL && DECL_REGISTER(decl)) {
    warning("%Hregister name on `%s' is ignored by LLVM '%D'",
            &DECL_SOURCE_LOCATION (decl), decl);
  }

  /* Specifying a section attribute on a variable forces it into a
     non-.bss section, and thus it cannot be common.  */
  if (TREE_CODE (decl) == VAR_DECL
      && DECL_SECTION_NAME (decl) != NULL_TREE
      && DECL_INITIAL (decl) == NULL_TREE
      && DECL_COMMON (decl))
    DECL_COMMON (decl) = 0;

  /* Variables can't be both common and weak.  */
  if (TREE_CODE (decl) == VAR_DECL && DECL_WEAK (decl))
    DECL_COMMON (decl) = 0;

  /* Can't use just the variable's own name for a variable whose scope is less
     than the whole file, unless it's a member of a local class (which will
     already be unambiguous).  Concatenate a distinguishing number.  */
  if (!top_level && !TREE_PUBLIC (decl)
      && !(DECL_CONTEXT (decl) && TYPE_P (DECL_CONTEXT (decl)))
      && name == IDENTIFIER_POINTER (DECL_NAME (decl))) {
    static int var_labelno = 0;
    char *label = (char*)alloca(strlen(name) + 32);
    sprintf(label, ".%s_%d", name, ++var_labelno);
    new_name = label;
  }

  if (name != new_name) {
    SET_DECL_ASSEMBLER_NAME (decl, get_identifier (new_name));
    name = IDENTIFIER_POINTER (DECL_ASSEMBLER_NAME (decl));
  }

  llvm_assemble_external(decl);
}

/* llvm_get_or_make_decl_llvm - This function is used by the DECL_LLVM macro to
 * get the LLVM code for the specified global if it is not defined.  This works
 * just like the RTL function make_decl_rtl, except that it also marks the
 * function/global variable as used, causing it's body to be emitted if it has
 * vague linkage.
 */
void llvm_get_or_make_decl_llvm(tree decl, const char *asmspec) {
  if (TREE_CODE(decl) == FIELD_DECL) {
    llvm_type_get_from_tree(DECL_CONTEXT(decl));
    llvm_type_get_from_tree(DECL_FIELD_CONTEXT(decl));
    assert(DECL_LLVM_SET_P(decl) && "field decl didn't get laid out!");
    return;
  }

  if (!DECL_LLVM_SET_P(decl))
    llvm_make_decl_llvm(decl, asmspec);

  if (DECL_LLVM_SET_P(decl)) {            /* Ignore builtin functions */
    /* This horrible code mirrors code found in varasm.c:assemble_name */
    if (!llvm_value_is_global(DECL_LLVM(decl))) abort();
    MarkNameAsUsed(DECL_LLVM(decl)->Name);
  }
}


/* llvm_assemble_external - This function is called once for each external
 *  function and variable as they are used.
 */
void llvm_assemble_external(tree decl) {
  assert(!DECL_LLVM_SET_P(decl) && "Declaration already has LLVM code?");

  if (errorcount || sorrycount)
    return;  /* Don't do anything if an error has occurred. */

  if (TREE_CODE(decl) == FUNCTION_DECL) {
    if (DECL_BUILT_IN_CLASS(decl) == NOT_BUILT_IN ||
        DECL_BUILT_IN_CLASS(decl) == BUILT_IN_NORMAL ||
        DECL_BUILT_IN_CLASS(decl) == BUILT_IN_FRONTEND) {
      /* Create a prototype for the specified function */
      tree OldBody = DECL_SAVED_TREE(decl);
      llvm_function *Fn;
      DECL_SAVED_TREE(decl) = 0;     /* Make sure to just build a prototype */
      Fn = llvm_expand_function_start(decl, 0);

      if (OldBody) {
        assert(llvm_ilist_empty(llvm_basicblock, Fn->BasicBlocks) &&
               "Function has a body!");
      }
      DECL_SAVED_TREE(decl) = OldBody;

      if (EMIT_CODE_INCREMENTALLY) llvm_function_print(Fn, llvm_out_file);
    } else {
      /*
        fprintf(llvm_out_file, ";; Ignoring builtin: %s\n",
                (*lang_hooks.decl_printable_name)(decl, 2));
      */
    }
  } else {
    const char *PName = (*lang_hooks.decl_printable_name)(decl, 2);
    llvm_type *Ty = llvm_type_get_from_tree(TREE_TYPE(decl));
    llvm_global *G;

    G = llvm_global_new(Ty, IDENTIFIER_POINTER(DECL_ASSEMBLER_NAME(decl)));
    if (PName && strcmp(PName, G2V(G)->Name))
      G->PrettyGlobalName = xstrdup(PName);
    
    if (DECL_WEAK(decl) || DECL_COMMON(decl) || DECL_VIRTUAL_P(decl))
      G->Linkage = L_Weak;
    else if (0)
      G->Linkage = L_LinkOnce;
    else if (!TREE_PUBLIC(decl))
       G->Linkage = L_Internal;
    if (TREE_READONLY(decl))
      G->isConstant = 1;
    
    /* Allociate the LLVM global with the tree global */
    SET_DECL_LLVM(decl, G2V(G));
    
    /* Add the global variable to the llvm program */
    llvm_ilist_push_back(llvm_global, TheProgram.Globals, G);
    if (EMIT_CODE_INCREMENTALLY)
      llvm_global_print(G, llvm_out_file);
  }
}

void llvm_assemble_variable(tree decl) {
  llvm_global *G;
  llvm_type *Ty, *BaseTy;
  if (errorcount || sorrycount) {
    TREE_ASM_WRITTEN(decl) = 1;
    return;  /* Don't do anything if an error has occurred. */
  }

  G = (llvm_global*)DECL_LLVM(decl);
  Ty = llvm_type_get_pointer(llvm_type_get_from_tree(TREE_TYPE(decl)));
  BaseTy = GET_POINTER_TYPE_ELEMENT(Ty);

  /* Check to see if there was a forward declaration of this global with a type
   * that doesn't agree.  If so, regenerate a new global, and allow the function
   * resolution pass to splice the two together.
   */
  if (G2V(G)->Ty != Ty) {
    SET_DECL_LLVM(decl, 0);
    G = (llvm_global*)DECL_LLVM(decl);
    assert(G2V(G)->Ty == Ty && "LLVM type not correctly set??");
  }

  if (DECL_INITIAL(decl) && DECL_INITIAL(decl) != error_mark_node) {
    /* An initializer was specified for the global */
    if (TREE_CODE(DECL_INITIAL(decl)) != STRING_CST) {
      G->Init = llvm_expand_constant_expr(DECL_INITIAL(decl), BaseTy);
    } else {
      /* Handle string initializers specially to allow zero padding the end. */
      llvm_type *BaseTy = GET_POINTER_TYPE_ELEMENT(G2V(G)->Ty);
      llvm_type *ElTy = GET_ARRAY_TYPE_ELEMENT(BaseTy);
      unsigned Len = GET_ARRAY_TYPE_SIZE(BaseTy);
      G->Init = llvm_decode_string_constant(DECL_INITIAL(decl), Len, ElTy);
    }
  } else {
    /* An initializer wasn't specified, give it a zero initializer */
    G->Init = V2C(llvm_constant_get_null(BaseTy));
  }

  TREE_ASM_WRITTEN(decl) = 1;
  if (EMIT_CODE_INCREMENTALLY) llvm_global_print(G, llvm_out_file);
}

void llvm_emit_global_ctor_dtor(int isConstructor, tree fndecl, int Priority) {
  llvm_function *Fn = V2F(DECL_LLVM(fndecl));
  llvm_global_ctordtor *I=llvm_global_ctordtor_new(isConstructor, Fn, Priority);
  llvm_ilist_push_back(llvm_global_ctordtor, TheProgram.GlobalCtorDtors, I);
}

/* llvm_mark_variable_volatile - This function implements the equivalent of
 * make_var_volatile.  We need to set the volatile flag on the LLVM value so
 * that loads and stores know they are volatile.
 */
void llvm_mark_variable_volatile(tree var) {
  DECL_LLVM(var)->isVolatile = 1;
}


/* llvm_get_empty_class_pointer - This implements EMPTY_CLASS_EXPR's for the C++
 * front-end.
 */
llvm_value *llvm_get_empty_class_pointer(llvm_function *Fn, tree ty) {
  llvm_type *ClassTy = llvm_type_get_from_tree(ty);
  llvm_value *V = D2V(make_temporary_alloca(Fn, ClassTy));
  
  /* add a getelementptr to get to the zero'th element (guaranteed to be a
   * ubyte for an empty class)
   */
  llvm_value *EP = append_inst(Fn, create_gep3(V, llvm_constant_long_0,
                                               llvm_constant_ubyte_0));

  /* emit a store ubyte 0 into the result pointer... */
  append_inst(Fn, create_store_inst(llvm_constant_ubyte_0, EP, 0));
  return V;
}
