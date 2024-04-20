/* Structures used to represent generated LLVM code
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

/* This file defines the structures used to represent code in LLVM
   form and the functions used to manipulate them.
*/

#ifndef GCC_LLVM_REPRESENTATION_H
#define GCC_LLVM_REPRESENTATION_H

#include "config.h"
#include "llvm-ilist.h"
#include <stdio.h>

struct llvm_type;
struct llvm_basicblock;
union tree_node;

/*===---------------------------------------------------------------------===*/

typedef struct llvm_value {
  enum ValueType {
    Constant, ConstantExpr, ConstantAggregate, 
    Argument, Instruction, BasicBlock, Function, GlobalVariable
  } VTy;
  struct llvm_type *Ty;
  char *Name;                   /* Null terminated name, or null */
  int isVolatile;               /* True if this is pointer to volatile memory */
} llvm_value;

/* llvm_value_construct make a copy of the name string argument */
void llvm_value_construct(llvm_value *Val, struct llvm_type *Type,
			  const char *Name, enum ValueType VT);
void llvm_value_destruct(llvm_value *Val);

/* llvm_value_print_operand - Print the specified value formatted as
   an operand.  If PrintType is true, the type is printed as a
   prefix. */
void llvm_value_print_operand(llvm_value *V, int PrintType, FILE *F);
void llvm_value_dump_operand(llvm_value *V);

/* D2V - Convert a subclass of llvm_value to a llvm_value */
#define D2V(P) (&(P)->ValBase)

#define llvm_value_is_global(V) \
  ((V)->VTy == Function || (V)->VTy == GlobalVariable)

/* llvm_get_global_alias - If there is a global with the specified name, return
   it now. */
llvm_value *llvm_get_global_alias(const char *ExternalName);


/*===---------------------------------------------------------------------===*/

typedef struct llvm_constant {
  struct llvm_value ValBase;
  char *Repr;                        /* Null terminated string representation */
} llvm_constant;

#define llvm_value_is_constant(VAL) \
  ((VAL)->VTy == Constant ||        \
   (VAL)->VTy == ConstantExpr || (VAL)->VTy == ConstantAggregate || \
   (VAL)->VTy == GlobalVariable || (VAL)->VTy == Function)
#define V2C(VAL) \
  (assert(llvm_value_is_constant(VAL) &&  \
          "Operand to V2C is not a constant"), \
   (llvm_constant*)(VAL))

llvm_value *llvm_constant_new(struct llvm_type *Ty, const char *Rep);
llvm_value *llvm_constant_new_integral(struct llvm_type *Ty, long long X);
llvm_value *llvm_constant_get_null(struct llvm_type *Ty);
void llvm_constant_construct(llvm_constant *C, struct llvm_type *Ty,
                             const char *Name, enum ValueType VT,
                             const char *Rep);
void llvm_constant_destruct(llvm_constant *C);

/* llvm_constant_get_integer_val - Return the constant value represented by C.
 */
int llvm_constant_get_integer_val(llvm_constant *C);

/* Well known constants */
extern llvm_value *llvm_constant_VoidPtr_null;
extern llvm_value *llvm_constant_uint_1;
extern llvm_value *llvm_constant_ubyte_0;
extern llvm_value *llvm_constant_int_0;
extern llvm_value *llvm_constant_uint_0;
extern llvm_value *llvm_constant_long_0;
extern llvm_value *llvm_constant_bool_true;
extern llvm_value *llvm_constant_bool_false;

/*===---------------------------------------------------------------------===*/

typedef struct llvm_constant_expr {
  llvm_constant ConstantBase;
  struct llvm_instruction *Inst;      /* Instruction that is constant */
} llvm_constant_expr;

llvm_constant_expr *llvm_constant_expr_new(struct llvm_instruction *I);

void llvm_constant_expr_print(llvm_constant_expr *CE, FILE *F);
void llvm_constant_expr_dump(llvm_constant_expr *CE);

/*===---------------------------------------------------------------------===*/

typedef struct llvm_constant_aggregate {
  llvm_constant ConstantBase;
  llvm_value **Initializers;
} llvm_constant_aggregate;

llvm_constant_aggregate *llvm_constant_aggregate_new(struct llvm_type *Ty,
                                                     llvm_value **Inits);

void llvm_constant_aggregate_print(llvm_constant_aggregate *CA, FILE *F);
void llvm_constant_aggregate_dump(llvm_constant_aggregate *CA);

/*===---------------------------------------------------------------------===*/

typedef struct llvm_argument {
  struct llvm_value ValBase;
  llvm_ilist_node(struct llvm_argument, Arguments);
} llvm_argument;

llvm_argument *llvm_argument_new(struct llvm_type *Ty, const char *Nm);
void llvm_argument_delete(llvm_argument*);


/*===---------------------------------------------------------------------===*/

typedef struct llvm_switch_case {
  struct llvm_switch_case *Next;
  unsigned Value;
  struct llvm_basicblock *Dest;
} llvm_switch_case;

typedef struct llvm_instruction {
  llvm_value ValBase;
  llvm_ilist_node(struct llvm_instruction, Instructions);

  enum InstOpcode {
    O_Ret, O_Br, O_Switch, O_Invoke, O_Unwind,
    O_Add, O_Sub, O_Mul, O_Div, O_Rem,
    O_And, O_Or, O_Xor,
    O_SetEQ, O_SetNE, O_SetLE, O_SetGE, O_SetLT, O_SetGT,
    O_Alloca, O_Malloc, O_Load, O_Store, O_GetElementPtr,
    O_PHINode, O_Cast, O_Call, O_Shl, O_Shr, O_VAArg, O_VANext
  } Opcode;

  union {
    struct {   /* Valid for O_Load/O_Store instructions */
      char isVolatile;
    } LoadStore;
    struct {   /* Valid for the O_Switch instruction */
      llvm_switch_case *Cases;
    } Switch;
    struct {   /* Valid for the O_VANext instruction */
      struct llvm_type *ArgTy;
    } VANext;
  } x;

  unsigned NumOperands;
  llvm_value *Operands[1];  /* Variable sized array */
  /* Do not put anything here */
} llvm_instruction;

llvm_instruction *llvm_instruction_new(struct llvm_type *Ty,
				       const char *Name,
				       enum InstOpcode Opc,
				       unsigned NumOperands);
void llvm_instruction_delete(llvm_instruction*);
void llvm_instruction_print(llvm_instruction *I, FILE *F);
void llvm_instruction_dump(llvm_instruction *I);

#define llvm_instruction_is_terminator(INST) ((INST)->Opcode <= O_Invoke)

/* Helper functions */
llvm_instruction *create_alloca_inst(const char *Name,
                                     struct llvm_type *AllocadType,
                                     llvm_value *Size);
llvm_instruction *create_load_inst(const char *Name, llvm_value *Ptr,int isVol);
llvm_instruction *create_store_inst(llvm_value *Val, llvm_value *Ptr,int isVol);
llvm_instruction *create_binary_inst(const char *Name, enum InstOpcode Opc,
                                     llvm_value *Op1, llvm_value *Op2);
llvm_instruction *create_uncond_branch(struct llvm_basicblock *Dest);
llvm_instruction *create_cond_branch(llvm_value *Val,
                                     struct llvm_basicblock *TrueBlock,
                                     struct llvm_basicblock *FalseBlock);
llvm_instruction *create_gep3(llvm_value *Op0, llvm_value *Op1,llvm_value *Op2);

/*===---------------------------------------------------------------------===*/

typedef struct llvm_basicblock {
  llvm_value ValBase;
  llvm_ilist_node(struct llvm_basicblock, BasicBlocks); /* Part of BB list */
  llvm_ilist(llvm_instruction, Instructions);     /* List of instructions */
} llvm_basicblock;

llvm_basicblock *llvm_basicblock_new(const char *);
void llvm_basicblock_delete(llvm_basicblock*);

void llvm_basicblock_print(llvm_basicblock *BB, FILE *F);
void llvm_basicblock_dump(llvm_basicblock *BB);

#define V2BB(VAL) \
  (assert((VAL)->VTy == BasicBlock && "Operand to V2BB is not a basicblock!"), \
   (llvm_basicblock*)(VAL))


/*===---------------------------------------------------------------------===*/

enum llvm_linkage {
  L_External = 0,                           /* Normal externally visible */
  L_Concatenating,                          /* Static init list */
  L_LinkOnce,                               /* Inline function? */
  L_Weak,                                   /* Weak reference? */
  L_Internal                                /* Static function? */
};

struct llvm_expand_info;
typedef struct llvm_function {
  llvm_constant ConstantBase;
  llvm_ilist_node(struct llvm_function, Functions); /* Part of Function list */
  llvm_ilist(llvm_argument  , Arguments);     /* List of arguments */
  llvm_ilist(llvm_basicblock, BasicBlocks);   /* List of basic blocks */
  struct llvm_expand_info *ExpandInfo;

  int FunctionUsesVarArgs;      /* True if function accesses variable args */

  /* ForwardedFunction - This member is here only because we don't have a
   * replaceAllUsesWith equivalent in the C frontend.  In C, we can create a
   * prototype for a function which is inaccurate (ie, it has (...) as the
   * argument list type), then later find the body for the function.  We want to
   * replace all uses of the first prototype with the new body, but of course we
   * can't do this.  Instead, we just mark the prototype as forwarding to the
   * new body, and then the printer handles this as a magical, special, gross,
   * case.
   */
  struct llvm_function *ForwardedFunction;

  enum llvm_linkage Linkage;
  char *PrettyFunctionName;
} llvm_function;

llvm_function *llvm_function_new(struct llvm_type *Ty, const char *);
void llvm_function_delete(llvm_function*);

void llvm_function_print(llvm_function *Func, FILE *F);
void llvm_function_dump(llvm_function *Func);

#define V2F(VAL) \
  (assert((VAL)->VTy == Function && "Operand to V2F is not a function!"), \
   (llvm_function*)(VAL))

/*===---------------------------------------------------------------------===*/

typedef struct llvm_global {
  llvm_constant ConstantBase;
  llvm_ilist_node(struct llvm_global, Globals); /* Part of Global list */
  int isConstant;                       /* Is the global immutable? */
  llvm_constant *Init;                  /* Initializer or null for external */

  enum llvm_linkage Linkage;

  char *PrettyGlobalName;
} llvm_global;

llvm_global *llvm_global_new(struct llvm_type *Ty, const char *Name);
void llvm_global_delete(llvm_global*);

void llvm_global_print(llvm_global *Func, FILE *F);
void llvm_global_dump(llvm_global *Func);

#define G2C(GLOBAL) (&(GLOBAL)->ConstantBase)
#define G2V(GLOBAL) (D2V(G2C(GLOBAL)))

/*===---------------------------------------------------------------------===*/

typedef struct llvm_global_ctordtor {
  int isCtor;
  llvm_function *Fn;
  int Priority;
  llvm_ilist_node(struct llvm_global_ctordtor, GlobalCtorDtors);
} llvm_global_ctordtor;

llvm_global_ctordtor *llvm_global_ctordtor_new(int isCtor, llvm_function *Fn,
                                               int Priority);
void llvm_global_ctordtor_delete(llvm_global_ctordtor *I);

/*===---------------------------------------------------------------------===*/

typedef struct llvm_program {
  llvm_ilist(llvm_function, Functions);              /* List of functions */
  llvm_ilist(llvm_global, Globals);                  /* List of global vars */
  llvm_ilist(llvm_global_ctordtor, GlobalCtorDtors); /* List of global ctors */
} llvm_program;

extern llvm_program TheProgram;

void llvm_program_construct(llvm_program *Program);
void llvm_program_destruct(llvm_program *Program);
void llvm_program_print(FILE *F);
void llvm_dump(void);   /* Dump the entire program to stderr */


/*===---------------------------------------------------------------------===*/

typedef struct llvm_type {
  enum TypeID {
    VoidTyID = 0  , BoolTyID,           /* Basics... */
    UByteTyID     , SByteTyID,          /* 8 bit types... */
    UShortTyID    , ShortTyID,          /* 16 bit types... */
    UIntTyID      , IntTyID,            /* 32 bit types... */
    ULongTyID     , LongTyID,           /* 64 bit types... */

    FloatTyID     , DoubleTyID,         /* Floating point types... */
    LabelTyID     ,                     /* Labels... */
    
    FunctionTyID  , StructTyID,         /* Functions... Structs... */
    ArrayTyID     , PointerTyID,        /* Array... pointer... */
    OpaqueTyID                          /* Opaque type instances... */
  } ID;
  
  /* All created types are kept on a linked list */
  struct llvm_type *NextTypeLink;

  union {
    struct {
      int isVarArg;            /* True if function takes variable arguments */
    } Function;
    struct {
      char *TypeName;          /* Name given to the type */
      unsigned Size;           /* The size (in bytes) of the structure */

      /* MemberOffsets - If non-null, contains an entry for each type element
       * with its offset from start of the structure.
       */
      unsigned *MemberOffsets;
    } Struct;
    struct {
      unsigned Size;           /* Number of elements in the array */
    } Array;
    struct {
      char *TypeName;          /* Name given to opaque struct type */
    } Opaque;
  } x;

  unsigned NumElements;
  struct llvm_type *Elements[1];  /* Variable sized array */
  /* Do not put anything here */
} llvm_type;

extern llvm_type *VoidTy, *BoolTy, *UByteTy, *SByteTy, *UShortTy, *ShortTy;
extern llvm_type *UIntTy, *IntTy, *ULongTy, *LongTy, *FloatTy, *DoubleTy;
extern llvm_type *LabelTy, *VoidPtrTy;

void llvm_type_print(llvm_type *Ty, FILE *F);
void llvm_type_dump(llvm_type *Ty);
#define llvm_type_is_primitive(TY) (TY->ID < FunctionTyID)
#define llvm_type_is_fp(TY) (((TY)->ID == FloatTyID) || ((TY)->ID==DoubleTyID))
#define llvm_type_is_integral(TY) ((TY)->ID >= BoolTyID && (TY)->ID <= LongTyID)
#define llvm_type_is_scalar(TY)                          \
  ((TY)->ID == PointerTyID ||                            \
   (llvm_type_is_primitive(TY) && (TY)->ID != VoidTyID))
#define llvm_type_is_composite(TY) \
  (((TY)->ID == StructTyID) || ((TY)->ID == ArrayTyID))
#define llvm_type_is_signed(TY) \
  ((TY) == SByteTy || (TY) == ShortTy || (TY) == IntTy || (TY) == LongTy)
#define llvm_type_is_unsigned(TY) \
  ((TY) == UByteTy || (TY) == UShortTy || (TY) == UIntTy || (TY) == ULongTy)

unsigned llvm_type_get_size(llvm_type *Ty);

unsigned llvm_type_get_composite_num_elements(llvm_type *Ty);
llvm_type *llvm_type_get_composite_element(llvm_type *Ty, unsigned N);
llvm_type *llvm_type_get_integer(unsigned NumBits, int isUnsigned);

/* get_num_recursive_elements - Walk the value type recursively, counting the
   number of values that would need to be passed if this is passed as a
   structure argument by value. */
unsigned llvm_type_get_num_recursive_elements(llvm_type *Ty);

/* llvm_type_get_tree_type - Return the LLVM type that corresponds to
   the specified tree type.
*/
llvm_type *llvm_type_get_from_tree(union tree_node *);

/* llvm_type_get_promoted_type - Perform C style argument promotion on the
 * specified LLVM type.  For example sbyte->int and float->double.  Return the
 * promoted type.
 */
llvm_type *llvm_type_get_promoted_type(llvm_type *Ty);

/* Creation methods for types */
llvm_type *llvm_type_get_array(llvm_type *Ty, unsigned NumElements);
llvm_type *llvm_type_get_pointer(llvm_type *Ty);

/* Creation methods: For type which have more than one element type,
 * you must use a sequence of 'create', 'set', then 'get_cann_version'.  This
 * allows types to be kept unique.
 */
llvm_type *llvm_type_create_function(unsigned NumParam, llvm_type *RetTy);
llvm_type *llvm_type_create_struct(unsigned NumElements, unsigned Size);
llvm_type *llvm_type_get_cannonical_version(llvm_type *T);

#define GET_POINTER_TYPE_ELEMENT(PTRTY) \
 (assert((PTRTY)->ID == PointerTyID && "Not a pointer type!"), \
  (PTRTY)->Elements[0])

#define GET_ARRAY_TYPE_ELEMENT(ARRAYTY) \
 (assert((ARRAYTY)->ID == ArrayTyID && "Not an array type!"), \
  (ARRAYTY)->Elements[0])

#define GET_ARRAY_TYPE_SIZE(ARRAYTY) \
 (assert((ARRAYTY)->ID == ArrayTyID && "Not an array type!"), \
  (ARRAYTY)->x.Array.Size)

#define GET_STRUCT_TYPE_ELEMENT(STRUCTTY,ELNO) \
 (assert((STRUCTTY)->ID == StructTyID && "Not an struct type!"), \
  assert((STRUCTTY)->NumElements > (ELNO) && "Struct element out-of-range!"), \
  (STRUCTTY)->Elements[(ELNO)])

#define GET_FUNCTION_TYPE_RETURN(FNTY) \
 (assert((FNTY)->ID == FunctionTyID && "Not a function type!"), \
  (FNTY)->Elements[0])

#define GET_FUNCTION_TYPE_NUMARGS(FNTY) \
 (assert((FNTY)->ID == FunctionTyID && "Not a function type!"), \
  (FNTY)->NumElements-1)

#define GET_FUNCTION_TYPE_ARGUMENT(FNTY, ARGNO) \
 (assert((FNTY)->ID == FunctionTyID && "Not a function type!"), \
  assert(ARGNO+1 < (FNTY)->NumElements && "Invalid function type arg #!"), \
  (FNTY)->Elements[ARGNO+1])

void llvm_type_print_all_named(FILE *F);

unsigned SetFunctionArgs(llvm_type *FuncTy, unsigned ArgNo, llvm_type *ArgTy);

/*===---------------------------------------------------------------------===*/

/* Functions for making it easy to use a pointer to pointer hash table */
struct htab;

/* phset_new - Create a new hash table as a pointer set */
struct htab *phset_new(unsigned InitialSize);
void pph_delete(struct htab *HT);

/* phset_contains - Return true if the specified value is in the set */
int phset_contains(struct htab *HT, void *Key);

/* pphtab_lookup - Return the value if the specified key is in the table, else
   return null.
*/
void *pphtab_lookup(struct htab *HT, void *Key);

/* pphtab_lookup_slot - Find (and create if not in the table) the place in the
   table a pointer should exist.  This returns a pointer to the pointer so a new
   entry may be inserted if desired.
*/
void **pphtab_lookup_slot(struct htab *HT, void *Key);

/* pphtab_insert - Insert the specified value for the specified key, replacing
   an entry if it already exists.
*/
void pphtab_insert(struct htab *HT, void *Key, void *Value);

/* phset_insert - Insert a value into the set.
*/
void phset_insert(struct htab *HT, void *Key);

#endif /* GCC_LLVM_REPRESENTATION_H */
