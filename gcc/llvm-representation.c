/* Implement LLVM data structures
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

#include "llvm-representation.h"
#include "llvm-internals.h"
#include "hashtab.h"
#include <assert.h>
#include <string.h>

/* The one true program we are compiling */
llvm_program TheProgram;

/* Identifier Rename Table Implementation - Keep names unique! **************
 */

static htab_t IdentifierTable;    /* hash<const char*, IdentifierTableEntry> */

typedef struct IdentifierTableEntry {
  char *NameBase;          /* The base name for this identifier */
  unsigned Counter;        /* The number of values with this prefix */
  llvm_value *GlobalIdent; /* Is NameBase a global with this prefix? */
} IdentifierTableEntry;


/* IdentifierTableEntry Equality checker.  This just does a simple string
   comparison, but has a small twist.  We may have renamed the value IN the hash
   table, so we must ignore any ".0" suffix on it.
*/
static int IT_eq(const void *p1, const void *p2) {
  const IdentifierTableEntry *Old = (const IdentifierTableEntry*)p1;
  int Len;
  Len = strlen(Old->NameBase);
  if (Len > 2 && Old->NameBase[Len-2] == '.') {
    assert(Old->NameBase[Len-1] == '0' && "Not a .0 suffix?");
    if (memcmp(Old->NameBase, (const char*)p2, Len-2) || 
        ((const char*)p2)[Len-2] != 0)  /* check for null terminator */
      return 0;
    return 1;
  } else {
    return !memcmp(Old->NameBase, (const char*)p2, Len+1);
  }
}

/* IdentifierTableEntry Hash Function - Normal string hash, unless there is a
   suffix */
static hashval_t IT_hash(const void *P) {
  const IdentifierTableEntry *Entry = (const IdentifierTableEntry*)P;
  int Len = strlen(Entry->NameBase);

  if (Len > 2 && Entry->NameBase[Len-2] == '.') {
    hashval_t Hash;
    assert(Entry->NameBase[Len-1] == '0' && "Not a .0 suffix?");
    Entry->NameBase[Len-2] = 0;    /* Temporarily remove the suffix */
    Hash = htab_hash_string(Entry->NameBase);
    Entry->NameBase[Len-2] = '.';  /* Restore the suffix */
    return Hash;
  }
  return htab_hash_string(Entry->NameBase);
}

static void IT_delete(void *P) {
  free(P);
}

static char *IdentifierTableGetName(const char *NameBase,
                                    llvm_value *GlobalVal) {
  /* Get the existing entry, or create a new one for this identifier root */
  IdentifierTableEntry *ITE, **ITEP;
  char *Name, *StrToFree = 0;
  char Suffix[10];
  
  /* If the incoming name ends with ".x", add a suffix so that we don't confuse
   * our internal renamer...
   */
  unsigned NameLen = strlen(NameBase);
  if (NameLen > 2 && NameBase[NameLen-2] == '.') {
    StrToFree = xmalloc(NameLen+3);
    memcpy(StrToFree, NameBase, NameLen);
    memcpy(StrToFree+NameLen, "__", 3);
    NameBase = StrToFree;
  }

  ITEP = (IdentifierTableEntry**)
    htab_find_slot_with_hash(IdentifierTable, NameBase,
                             htab_hash_string(NameBase), INSERT);

  /* If there was no entry before, create one */
  if (*ITEP == 0) {
    /* Allocate extra space for the potential ".0" suffix */
    Name = xmalloc(strlen(NameBase)+3);
    /* Initialize new Name string with the basename */
    strcpy(Name, NameBase);
    ITE = *ITEP = xmalloc(sizeof(IdentifierTableEntry));
    ITE->NameBase = Name;
    ITE->Counter = 0;
    ITE->GlobalIdent = GlobalVal;    /* NameBase points to a global's name */
    if (StrToFree) free(StrToFree);
    return Name;
  }

  /* If there is an entry before, we must rename things */
  ITE = *ITEP;

  /* If this is the first conflict with an existing name, rename the original
     unless it was at global scope.  The space for this suffix was
     preallocated. */
  if (ITE->Counter++ == 0 && !ITE->GlobalIdent)
    strcat(ITE->NameBase, ".0");

  /* Rename the allocated string unless this object is a global */
  if (GlobalVal) {
    /* Mark that there is now a global with this name */
    ITE->GlobalIdent = GlobalVal;
    Name = xstrdup(NameBase);
    ITE->NameBase = Name;
    if (StrToFree) free(StrToFree);
    return Name;
  }

  sprintf(Suffix, ".%d", ITE->Counter);

  Name = xmalloc(strlen(NameBase)+strlen(Suffix)+1);
  strcat(strcpy(Name, NameBase), Suffix);

  if (StrToFree) free(StrToFree);
  return Name;
}

llvm_value *llvm_get_global_alias(const char *ExternalName) {
  IdentifierTableEntry *ITE = (IdentifierTableEntry*)
    htab_find_with_hash(IdentifierTable, ExternalName,
                        htab_hash_string(ExternalName));
  return ITE ? ITE->GlobalIdent : 0;
}


static int DeleteFunctionOnlyEntries(void **X, void *info ATTRIBUTE_UNUSED) {
  IdentifierTableEntry *ITE = (IdentifierTableEntry*)*X;
  if (ITE->GlobalIdent) {
    ITE->Counter = 0;        /* Reset the rename counter */
  } else {                   /* If this is a completely dead entry, remove it */
    htab_clear_slot(IdentifierTable, X);
  }
  return 1;  /* Continue scanning */
}

/* Reset the identifier rename table now that we are out of function scope */
void ResetIdentifierTableForEndOfFunction() {
  htab_traverse(IdentifierTable, DeleteFunctionOnlyEntries, 0);
}

void llvm_InitializeProgram() {
  llvm_program_construct(&TheProgram);
  IdentifierTable = htab_create(256, IT_hash, IT_eq, IT_delete);
}


/* llvm_value implementation ************************************************
 */

/* llvm_value_construct - In addition to simple creation of a new LLVM value,
   this performs renaming to make sure that two values names don't conflict.  To
   do this, a hash table of identifiers is kept around.  The first time a name
   is requested, it gets the requested name with a little extra space allocated
   to later add a "0".  If a name is requested additional times, the original
   name has a "0" suffix added to it (whos space was preallocated), and
   subsequent values get increasing identifiers.  The name and type of a value
   should not be changed after they are constructed.
 */
void llvm_value_construct(llvm_value *Val, struct llvm_type *Type,
			  const char *Name, enum ValueType VT) {
  llvm_value *GlobalVal;
  Val->VTy = VT;
  GlobalVal = llvm_value_is_global(Val) ? Val : 0;
  Val->Ty = Type;
  if (Name[0] == '*') ++Name;
  Val->Name = Name[0] ? IdentifierTableGetName(Name, GlobalVal) : xstrdup(Name);
}

void llvm_value_destruct(llvm_value *Val ATTRIBUTE_UNUSED) {
#if 0
  /* FIXME: We currently cannot free the name string because it might be used by
   * the identifier hash!  In practice, this is not a huge problem, because most
   * of the program isn't free'd until the end of execution anyways.  Just
   * things like basic block speculatively created are a problem.
   */
  free(Val->Name);
#endif
}

void llvm_value_dump_operand(llvm_value *V) {
  llvm_value_print_operand(V, 1, stderr);
  fprintf(stderr, "\n");
}

/* llvm_value_print_operand - Print the specified value formatted as
   an operand.  If PrintType is true, the type is printed as a
   prefix. */
void llvm_value_print_operand(llvm_value *V, int PrintType, FILE *F) {
  if (V == 0) {
    fprintf(F, "<null operand>");
    return;
  }

  if (PrintType) {
    llvm_type_print(V->Ty, F);
    fprintf(F, " ");
  }

  if (V->VTy == ConstantExpr) {
    llvm_constant_expr_print((llvm_constant_expr*)V, F);
  } else if (V->VTy == ConstantAggregate) {
    llvm_constant_aggregate_print((llvm_constant_aggregate*)V, F);
  } else if (V->VTy == Constant) {
    fprintf(F, "%s", V2C(V)->Repr);
  } else if (V->VTy == Function && V2F(V)->ForwardedFunction) {
    /* Print out a constant expr cast of the forwarding to function. */
    llvm_function *Fn = V2F(V);
    assert(!Fn->ForwardedFunction->ForwardedFunction&&"Cannot double forward!");
    fprintf(F, "cast (");
    llvm_value_print_operand(G2V(Fn->ForwardedFunction), 1, F);
    fprintf(F, " to ");
    llvm_type_print(G2V(Fn)->Ty, F);
    fprintf(F, ")");

  } else if (V->Name[0]) {
    fprintf(F, "%%%s", V->Name);
  } else if (!PrintType) {
    fprintf(stderr, "ERROR, didn't print ANYTHING for operand!");
    abort();
  }
}

/* llvm_constant implementation ********************************************
 */
void llvm_constant_construct(llvm_constant *C, struct llvm_type *Ty,
                             const char *Name, enum ValueType VT,
                             const char *Rep) {
  llvm_value_construct(D2V(C), Ty, Name, VT);
  C->Repr = xstrdup(Rep);
}

void llvm_constant_destruct(llvm_constant *C) {
  free(C->Repr);
  llvm_value_destruct(D2V(C));
}

llvm_value *llvm_constant_new(struct llvm_type *Ty, const char *Rep) {
  llvm_constant *C = (llvm_constant*)xcalloc(sizeof(llvm_constant), 1);
  llvm_constant_construct(C, Ty, "", Constant, Rep);
  return D2V(C);
}

llvm_value *llvm_constant_new_integral(struct llvm_type *Ty, long long X) {
  char Buffer[40];
  switch (Ty->ID) {
  case BoolTyID:
    return X ? llvm_constant_bool_true : llvm_constant_bool_false;
  case UByteTyID:  sprintf(Buffer, "%u", (unsigned char)X); break;
  case SByteTyID:  sprintf(Buffer, "%d", (signed   char)X); break;
  case UShortTyID: sprintf(Buffer, "%u", (unsigned short)X); break;
  case ShortTyID:  sprintf(Buffer, "%d", (signed   short)X); break;
  case UIntTyID:   sprintf(Buffer, "%u", (unsigned int)X); break;
  case IntTyID:    sprintf(Buffer, "%d", (signed   int)X); break;
  case ULongTyID:  sprintf(Buffer, "%llu", (unsigned long long)X); break;
  case LongTyID:   sprintf(Buffer, "%lld", (signed long long)X); break;
  default: assert(0 && "Illegal type for constant_new_integral!");
  }
  return llvm_constant_new(Ty, Buffer);
}


/* llvm_constant_get_integer_val - Return the constant value represented by C.
 */
int llvm_constant_get_integer_val(llvm_constant *C) {
  char *EndPtr;
  int Result = strtol(C->Repr, &EndPtr, 10);
  assert(C->Repr[0] && *EndPtr == 0 && "Invalid integer constant!");
  return Result;
}



llvm_value *llvm_constant_uint_1, *llvm_constant_ubyte_0;
llvm_value *llvm_constant_long_0;
llvm_value *llvm_constant_int_0;
llvm_value *llvm_constant_uint_0;
llvm_value *llvm_constant_VoidPtr_null;
llvm_value *llvm_constant_bool_true;
llvm_value *llvm_constant_bool_false;

void llvm_InitializeConstants(void) {
  llvm_constant_bool_true    = llvm_constant_new(BoolTy,    "true");
  llvm_constant_bool_false   = llvm_constant_new(BoolTy,    "false");
  llvm_constant_ubyte_0      = llvm_constant_new(UByteTy,   "0");
  llvm_constant_long_0       = llvm_constant_new(LongTy,    "0");
  llvm_constant_int_0        = llvm_constant_new(IntTy,     "0");
  llvm_constant_uint_0       = llvm_constant_new(UIntTy,    "0");
  llvm_constant_uint_1       = llvm_constant_new(UIntTy,    "1");
  llvm_constant_VoidPtr_null = llvm_constant_new(VoidPtrTy, "null");
}

llvm_value *llvm_constant_get_null(llvm_type *Ty) {
  if (Ty == UByteTy) return llvm_constant_ubyte_0;
  if (Ty == IntTy)   return llvm_constant_int_0;
  if (Ty == UIntTy)  return llvm_constant_uint_0;
  if (Ty == LongTy)  return llvm_constant_long_0;
  if (Ty == BoolTy)  return llvm_constant_bool_false;
  if (Ty->ID == PointerTyID)
    return llvm_constant_new(Ty, "null");  /* new null pointer */
  else if (llvm_type_is_fp(Ty))
    return llvm_constant_new(Ty, "0.0");   /* new null fp value */
  else if (Ty->ID == StructTyID) {
    llvm_value **Vals =
      (llvm_value**)xmalloc(sizeof(llvm_value*) * Ty->NumElements);
    unsigned i;
    for (i = 0; i != Ty->NumElements; ++i)
      Vals[i] = llvm_constant_get_null(Ty->Elements[i]);
    return G2V(llvm_constant_aggregate_new(Ty, Vals));
  } else if (Ty->ID == ArrayTyID) {
    llvm_value **Vals =
      (llvm_value**)xmalloc(sizeof(llvm_value*) * Ty->x.Array.Size);
    unsigned i;
    llvm_value *El = llvm_constant_get_null(Ty->Elements[0]);
    for (i = 0; i != Ty->x.Array.Size; ++i)
      Vals[i] = El;
    return G2V(llvm_constant_aggregate_new(Ty, Vals));
  } else
    return llvm_constant_new(Ty, "0");     /* New zero integral or FP */
}

/* llvm_constant_expr implementation ******************************************
 */
llvm_constant_expr *llvm_constant_expr_new(llvm_instruction *I) {
  llvm_constant_expr *CE =
    (llvm_constant_expr*)xcalloc(sizeof(llvm_constant_expr), 1);
  llvm_constant_construct(G2C(CE), D2V(I)->Ty, "", ConstantExpr, "");
  CE->Inst = I;
  return CE;
}

void llvm_constant_expr_dump(llvm_constant_expr *CE) {
  llvm_constant_expr_print(CE, stderr);
}

static void print_opcode_name(enum InstOpcode Opcode, FILE *F) {
  switch (Opcode) {
  case O_Ret:           fprintf(F, "ret"); break;
  case O_Br:            fprintf(F, "br"); break;
  case O_Switch:        fprintf(F, "switch"); break;
  case O_Invoke:        fprintf(F, "invoke"); break;
  case O_Unwind:        fprintf(F, "unwind"); break;
  case O_Add:           fprintf(F, "add"); break;
  case O_Sub:           fprintf(F, "sub"); break;
  case O_Mul:           fprintf(F, "mul"); break;
  case O_Div:           fprintf(F, "div"); break;
  case O_Rem:           fprintf(F, "rem"); break;
  case O_And:           fprintf(F, "and"); break;
  case O_Or:            fprintf(F, "or"); break;
  case O_Xor:           fprintf(F, "xor"); break;
  case O_SetEQ:         fprintf(F, "seteq"); break;
  case O_SetNE:         fprintf(F, "setne"); break;
  case O_SetLE:         fprintf(F, "setle"); break;
  case O_SetGE:         fprintf(F, "setge"); break;
  case O_SetLT:         fprintf(F, "setlt"); break;
  case O_SetGT:         fprintf(F, "setgt"); break;
  case O_Alloca:        fprintf(F, "alloca"); break;
  case O_Malloc:        fprintf(F, "malloc"); break;
  case O_Load:          fprintf(F, "load"); break;
  case O_Store:         fprintf(F, "store"); break;
  case O_GetElementPtr: fprintf(F, "getelementptr"); break;
  case O_PHINode:       fprintf(F, "phi"); break;
  case O_Cast:          fprintf(F, "cast"); break;
  case O_Call:          fprintf(F, "call"); break;
  case O_Shl:           fprintf(F, "shl"); break;
  case O_Shr:           fprintf(F, "shr"); break;
  case O_VAArg:         fprintf(F, "vaarg"); break;
  case O_VANext:        fprintf(F, "vanext"); break;
  default:              fprintf(F, "<unknown instruction opcode>"); break;
  }
}

void llvm_constant_expr_print(llvm_constant_expr *CE, FILE *F) {
  llvm_instruction *I = CE->Inst;
  unsigned i;

  print_opcode_name(I->Opcode, F);
  fprintf(F, " (");

  for (i = 0; i != I->NumOperands; ++i) {
    if (i) fprintf(F, ", ");
    llvm_value_print_operand(I->Operands[i], 1, F);
  }
  
  if (I->Opcode == O_Cast) {
    fprintf(F, " to ");
    llvm_type_print(G2V(CE)->Ty, F);
  }

  fprintf(F, ")");
}

/* llvm_constant_aggregate implementation **************************************
 */
llvm_constant_aggregate *llvm_constant_aggregate_new(llvm_type *Ty,
                                                     llvm_value **Init) {
  llvm_constant_aggregate *CA =
    (llvm_constant_aggregate*)xcalloc(sizeof(llvm_constant_aggregate), 1);
  llvm_constant_construct(G2C(CA), Ty, "", ConstantAggregate, "");
  CA->Initializers = Init;
  return CA;
}

void llvm_constant_aggregate_dump(llvm_constant_aggregate *CA) {
  llvm_constant_aggregate_print(CA, stderr);
}


void llvm_constant_aggregate_print(llvm_constant_aggregate *CE, FILE *F) {
  unsigned i;
  llvm_type *Ty = G2V(CE)->Ty;
  llvm_value **Elements = CE->Initializers;
  if (Ty->ID == StructTyID) {
    fprintf(F, "{ ");
    for (i = 0; i != Ty->NumElements; ++i) {
      if (i) fprintf(F, ", ");
      llvm_value_print_operand(Elements[i], 1, F);
    }
    fprintf(F, " }");
  } else {
    assert(Ty->ID == ArrayTyID && "Invalid composite type!");
    fprintf(F, "[ ");
    for (i = 0; i != Ty->x.Array.Size; ++i) {
      if (i) fprintf(F, ", ");
      llvm_value_print_operand(Elements[i], 1, F);
    }
    fprintf(F, " ]");
  }
}

/* llvm_argument implementation ********************************************
 */
llvm_argument *llvm_argument_new (llvm_type *Ty, const char *Name) {
  llvm_argument *Arg = (llvm_argument*)xcalloc(sizeof(llvm_argument), 1);
  llvm_value_construct(D2V(Arg), Ty, Name, Argument);
  return Arg;
}

void llvm_argument_delete (llvm_argument *Arg) {
  llvm_value_destruct(D2V(Arg));
  free(Arg);
}

/* llvm_instruction implementation ********************************************
 */

llvm_instruction *llvm_instruction_new(struct llvm_type *Ty,
                                       const char *Name,
                                       enum InstOpcode Opc,
				       unsigned NumOperands) {
  unsigned Size = sizeof(llvm_instruction) +(NumOperands-1)*sizeof(llvm_value*);
  llvm_instruction *I = (llvm_instruction*)xcalloc(Size, 1);
  llvm_value_construct(D2V(I), Ty, Name, Instruction);
  I->Opcode = Opc;
  I->NumOperands = NumOperands;
  return I;
}

void llvm_instruction_delete(llvm_instruction *I) {
  llvm_value_destruct(D2V(I));
  free(I);
}

llvm_instruction *create_alloca_inst(const char *Name, llvm_type *AllocadType,
                                     llvm_value *Size) {
  /* get the type of the instruction itself */
  llvm_type *Ty = llvm_type_get_pointer(AllocadType);
  llvm_instruction *I = llvm_instruction_new(Ty, Name, O_Alloca, 1);
  I->Operands[0] = Size;
  return I;
}

llvm_instruction *create_load_inst(const char *Name, llvm_value *Ptr,
                                   int isVol) {
  llvm_type *ResTy = Ptr ? GET_POINTER_TYPE_ELEMENT(Ptr->Ty) : IntTy;
  llvm_instruction *New = llvm_instruction_new(ResTy, Name, O_Load, 1);
  New->Operands[0] = Ptr;
  New->x.LoadStore.isVolatile = isVol;
  return New;
}

llvm_instruction *create_store_inst(llvm_value *Val, llvm_value *Ptr,
                                    int isVol) {
  llvm_instruction *New = llvm_instruction_new(VoidTy, "", O_Store, 2);
  New->Operands[0] = Val;
  New->Operands[1] = Ptr;
  New->x.LoadStore.isVolatile = isVol;
  return New;
}

llvm_instruction *create_binary_inst(const char *Name, enum InstOpcode Opc,
                                     llvm_value *Op1, llvm_value *Op2) {
  /* Comparisons always return bool, otherwise, return typeof first arg */
  llvm_type *Ty = (Opc >= O_SetEQ && Opc <= O_SetGT) ? BoolTy : Op1->Ty;
  llvm_instruction *New = llvm_instruction_new(Ty, Name, Opc, 2);
  New->Operands[0] = Op1;
  New->Operands[1] = Op2;

  if (Opc != O_Shr && Opc != O_Shl)
    assert(Op1->Ty == Op2->Ty &&
           "Binary operator operands must have compatible types!");
  return New;
}

llvm_instruction *create_uncond_branch(llvm_basicblock *Dest) {
  llvm_instruction *New = llvm_instruction_new(VoidTy, "", O_Br, 1);
  New->Operands[0] = D2V(Dest);
  return New;
}

llvm_instruction *create_cond_branch(llvm_value *Cond,
                                     llvm_basicblock *TrueBlock,
                                     llvm_basicblock *FalseBlock) {
  llvm_instruction *New = llvm_instruction_new(VoidTy, "", O_Br, 3);
  New->Operands[0] = Cond;
  New->Operands[1] = D2V(TrueBlock);
  New->Operands[2] = D2V(FalseBlock);
  return New;
}

llvm_instruction *create_gep3(llvm_value *Op0, llvm_value *Op1,llvm_value *Op2){
  llvm_instruction *I;
  llvm_type *ResultTy = GET_POINTER_TYPE_ELEMENT(Op0->Ty);
  assert(Op1->Ty == LongTy && "First GEP index must be long type!");
  assert(llvm_type_is_composite(ResultTy) && "Cannot index into noncomposite!");
  if (ResultTy->ID == StructTyID) {
    unsigned Idx = llvm_constant_get_integer_val(V2C(Op2));
    ResultTy = GET_STRUCT_TYPE_ELEMENT(ResultTy, Idx);
  } else
    ResultTy = GET_ARRAY_TYPE_ELEMENT(ResultTy);

  ResultTy = llvm_type_get_pointer(ResultTy);
  I = llvm_instruction_new(ResultTy, "tmp", O_GetElementPtr, 3);
  I->Operands[0] = Op0;
  I->Operands[1] = Op1;
  I->Operands[2] = Op2;
  return I;
}



void llvm_instruction_dump(llvm_instruction *I) {
  llvm_instruction_print(I, stderr);
}

void llvm_instruction_print(llvm_instruction *I, FILE *F) {
  unsigned i;
  llvm_value *Operand;
  fprintf(F, "\t");
  if (I == 0) { fprintf(F, "<null instruction>\n"); return; }

  /* if it has a name... print it */
  if (D2V(I)->Name && D2V(I)->Name[0]) {
    fprintf(F, "%%%s = ", D2V(I)->Name);
  }

  if ((I->Opcode == O_Load || I->Opcode == O_Store) &&
      I->x.LoadStore.isVolatile)
    fprintf(F, "volatile ");

  print_opcode_name(I->Opcode, F);

  Operand = I->NumOperands ? I->Operands[0] : 0;
  fprintf(F, " ");

#if 1  /* This block is useful for debugging cases where instructions are not
          inserted into the program correctly (they are floating). */
  if (Operand && Operand->VTy == Instruction)
    assert(llvm_ilist_inlist((llvm_instruction*)Operand));
#endif

  if (I->Opcode == O_Switch) {
    llvm_switch_case *C = I->x.Switch.Cases;
    /* Special case switch statement to get formatting nice and correct... */
    llvm_value_print_operand(Operand, 1, F);
    fprintf(F, ", ");
    llvm_value_print_operand(I->Operands[1], 1, F);
    fprintf(F, " [");

    for (; C; C = C->Next) {
      fprintf(F, "\n\t\tuint %u, ", C->Value);
      llvm_value_print_operand(D2V(C->Dest), 1, F);
    }
    fprintf(F, "\n\t]");
  } else if (I->Opcode == O_PHINode) {
    llvm_type_print(D2V(I)->Ty, F);
    fprintf(F, " ");

    for (i = 0; i != I->NumOperands; i += 2) {
      if (i) fprintf(F, ", ");
      fprintf(F, "[ ");
      llvm_value_print_operand(I->Operands[i  ], 0, F); fprintf(F, ", ");
      llvm_value_print_operand(I->Operands[i+1], 0, F);
      fprintf(F, " ]");
    }
  } else if (I->Opcode == O_Call) {
    llvm_value_print_operand(Operand, 1, F);
    fprintf(F, "(");
    for (i = 1; i != I->NumOperands; ++i) {
      if (i != 1) fprintf(F, ", ");
      llvm_value_print_operand(I->Operands[i], 1, F);
    }
    fprintf(F, ")");

  } else if (I->Opcode == O_Ret && !Operand) {
    fprintf(F, "void");

  } else if (I->Opcode == O_Invoke) {
    /* TODO: Should try to print out short form of the Invoke instruction */
    llvm_value_print_operand(Operand, 1, F);
    fprintf(F, "(");
    if (I->NumOperands > 3) llvm_value_print_operand(I->Operands[3], 1, F);
    for (i = 4; i < I->NumOperands; ++i) {
      fprintf(F, ", ");
      llvm_value_print_operand(I->Operands[i], 1, F);
    }

    fprintf(F, ")\n\t\t\tto ");
    llvm_value_print_operand(I->Operands[1], 1, F);
    fprintf(F, " except ");
    llvm_value_print_operand(I->Operands[2], 1, F);

  } else if (I->Opcode == O_Alloca || I->Opcode == O_Malloc) {
    llvm_type *Ty = D2V(I)->Ty;
    assert(Ty->ID == PointerTyID && "Allocation instruction must return ptr!");
    Ty = Ty->Elements[0];
    llvm_type_print(Ty, F);
    if (!Operand || Operand->VTy != Constant ||
        ((llvm_constant*)Operand)->Repr[0] != '1' ||
        ((llvm_constant*)Operand)->Repr[1] != 0) {
      fprintf(F, ", ");
      llvm_value_print_operand(Operand, 1, F);
    }

  } else if (I->Opcode == O_Cast) {
    llvm_value_print_operand(Operand, 1, F);
    fprintf(F, " to ");
    llvm_type_print(D2V(I)->Ty, F);
  } else if (I->Opcode == O_VAArg) {
    llvm_value_print_operand(Operand, 1, F);
    fprintf(F, ", ");
    llvm_type_print(D2V(I)->Ty, F);
  } else if (I->Opcode == O_VANext) {
    llvm_value_print_operand(Operand, 1, F);
    fprintf(F, ", ");
    llvm_type_print(I->x.VANext.ArgTy, F);
  } else if (I->NumOperands) {
    /* PrintAllTypes - Instructions who have operands of all the same type omit
     * the type from all but the first operand.  If the instruction has
     * different type operands (for example br), then they are all printed.
     */
    int PrintAllTypes = I->Opcode == O_Shr || I->Opcode == O_Shl || !Operand;
    llvm_type *TheType = Operand ? Operand->Ty : VoidTy;
    
    if (!PrintAllTypes)
      for (i = 1; i != I->NumOperands; ++i)
        if (I->Operands[i] && I->Operands[i]->Ty != TheType) {
          PrintAllTypes = 1;
          break;
        }

    if (!PrintAllTypes) {
      llvm_type_print(TheType, F);
      fprintf(F, " ");
    }

    for (i = 0; i != I->NumOperands; ++i) {
      if (i) fprintf(F, ", ");
      llvm_value_print_operand(I->Operands[i], PrintAllTypes, F);
    }
  }

  if (D2V(I)->Ty != VoidTy) {
    fprintf(F, "\t\t ; ty=");
    llvm_type_print(D2V(I)->Ty, F);
  }
  fprintf(F, "\n");
}


/* llvm_basicblock implementation ********************************************
 */

llvm_basicblock *llvm_basicblock_new(const char *Name) {
  llvm_basicblock *BB = (llvm_basicblock*)xcalloc(sizeof(llvm_basicblock), 1);
  llvm_value_construct(D2V(BB), LabelTy, Name, BasicBlock);
  llvm_ilist_construct(llvm_instruction, BB->Instructions);
  return BB;
}

void llvm_basicblock_delete(llvm_basicblock *BB) {
  llvm_value_destruct(D2V(BB));
  llvm_ilist_destruct(llvm_instruction, BB->Instructions);
  free(BB);
}

void llvm_basicblock_dump(llvm_basicblock *BB) {
  llvm_basicblock_print(BB, stderr);
}

void llvm_basicblock_print(llvm_basicblock *BB, FILE *F) {
  fprintf(F, "%s:\n", D2V(BB)->Name);
  llvm_ilist_foreach1(llvm_instruction, BB->Instructions,
		      llvm_instruction_print, F);
}


/* llvm_function implementation ********************************************
 */
llvm_function *llvm_function_new(llvm_type *Ty, const char *Name) {
  llvm_function *Fn = (llvm_function*)xcalloc(sizeof(llvm_function), 1);
  llvm_constant_construct(G2C(Fn), llvm_type_get_pointer(Ty), Name,Function,"");
  llvm_ilist_construct(llvm_argument  , Fn->Arguments  );
  llvm_ilist_construct(llvm_basicblock, Fn->BasicBlocks);
  return Fn;
}

void llvm_function_delete(llvm_function *Fn) {
  llvm_ilist_destruct(llvm_argument  , Fn->Arguments  );
  llvm_ilist_destruct(llvm_basicblock, Fn->BasicBlocks);
  llvm_constant_destruct(G2C(Fn));
  if (Fn->PrettyFunctionName) free(Fn->PrettyFunctionName);
  free(Fn);
}

void llvm_function_dump(llvm_function *Func) {
  llvm_function_print(Func, stderr);
}

/* Print the specified function to the output file */
void llvm_function_print(llvm_function *Fn, FILE *F) {
  int isPrototype = llvm_ilist_empty(llvm_basicblock, Fn->BasicBlocks);
  llvm_type *Ty = GET_POINTER_TYPE_ELEMENT(G2V(Fn)->Ty);

  assert(Ty->ID == FunctionTyID && "Function isn't a function type?");

  /* If this function got forwarded away, don't print it! */
  if (Fn->ForwardedFunction) {
    assert(isPrototype &&"Cannot forward away from a function implementation!");
    return;
  }

  if (isPrototype)
    fprintf(F, "declare ");   /* Function prototype? */
  else {
    fprintf(F, "\n");
    switch (Fn->Linkage) {
    default: abort();
    case L_External: /* Default */ break;
    case L_LinkOnce: fprintf(F, "linkonce "); break;
    case L_Weak:     fprintf(F, "weak "); break;
    case L_Internal: fprintf(F, "internal "); break;
    }
  }

  llvm_type_print(Ty->Elements[0], F);
  fprintf(F, " %%%s(", G2V(Fn)->Name);

  /* Print out all of the arguments */
  if (!isPrototype) {
    llvm_argument *ArgIt;
    for (ArgIt = llvm_ilist_begin(Fn->Arguments);
         ArgIt != llvm_ilist_end(Fn->Arguments);
         ArgIt = ArgIt->Next) {
      if (ArgIt != llvm_ilist_begin(Fn->Arguments))
        fprintf(F, ", ");
      llvm_value_print_operand(D2V(ArgIt), 1, F);
    }
  } else {
    unsigned i;
    for (i = 1; i != Ty->NumElements; ++i) {
      if (i != 1) fprintf(F, ",");
      llvm_type_print(Ty->Elements[i], F);
    }
  }
  if (Ty->x.Function.isVarArg)
    fprintf(F, "%s...", (Ty->NumElements > 1) ? ", " : "");

  fprintf(F, ")");
  if (!llvm_ilist_empty(llvm_basicblock, Fn->BasicBlocks)) {
    fprintf(F, " {  ");

    if (Fn->PrettyFunctionName)
      fprintf(F, ";; %s", Fn->PrettyFunctionName);
    fprintf(F, "\n");
    llvm_ilist_foreach1(llvm_basicblock, Fn->BasicBlocks,
                        llvm_basicblock_print, F);
    fprintf(F, "}\n");
  } else {
    if (Fn->PrettyFunctionName)
      fprintf(F, "  ;; %s", Fn->PrettyFunctionName);
  }
  fprintf(F, "\n");
}


/* llvm_global implementation ********************************************
 */
llvm_global *llvm_global_new(llvm_type *Ty, const char *Name) {
  llvm_global *G = (llvm_global*)xcalloc(sizeof(llvm_global), 1);
  llvm_constant_construct(G2C(G), llvm_type_get_pointer(Ty), Name, 
                          GlobalVariable, "");
  return G;
}

void llvm_global_delete(llvm_global *G) {
  if (G->PrettyGlobalName) free(G->PrettyGlobalName);
  llvm_constant_destruct(G2C(G));
  free(G);
}

void llvm_global_dump(llvm_global *G) {
  llvm_global_print(G, stderr);
}

/* Print the specified global to the output file */
void llvm_global_print(llvm_global *G, FILE *F) {
  if (G2V(G)->Name)
    fprintf(F, "%%%s = ", G2V(G)->Name);
  
  if (G->Init == 0)
    fprintf(F, "external ");
  else if (G->Linkage == L_Internal)
    fprintf(F, "internal ");
  else if (G->Linkage == L_LinkOnce)
    fprintf(F, "linkonce ");
  else if (G->Linkage == L_Weak)
    fprintf(F, "weak ");
  fprintf(F, G->isConstant ? "constant " : "global ");
  llvm_type_print(GET_POINTER_TYPE_ELEMENT(G2V(G)->Ty), F);

  if (G->Init) {
    fprintf(F, " ");
    llvm_value_print_operand(D2V(G->Init), 0, F);
  }

  if (G->PrettyGlobalName)
    fprintf(F, "  ;; %s", G->PrettyGlobalName);
  fprintf(F, "\n\n");
}

/* llvm_global_ctordtor implementation ****************************************
 */

llvm_global_ctordtor *llvm_global_ctordtor_new(int isCtor, llvm_function *Fn,
                                               int Priority) {
  llvm_global_ctordtor *I =
    (llvm_global_ctordtor*)xcalloc(sizeof(llvm_global_ctordtor), 1);
  I->isCtor = isCtor;
  I->Fn = Fn;
  I->Priority = Priority;
  return I;
}
void llvm_global_ctordtor_delete(llvm_global_ctordtor *I) {
  free(I);
}



/* llvm_program implementation ********************************************
 */
void llvm_program_construct(llvm_program *Program) {
  llvm_ilist_construct(llvm_function, Program->Functions);
  llvm_ilist_construct(llvm_global, Program->Globals);
  llvm_ilist_construct(llvm_global_ctordtor, Program->GlobalCtorDtors);
}

void llvm_program_destruct(llvm_program *Program) {
  llvm_ilist_destruct(llvm_global_ctordtor, Program->GlobalCtorDtors);
  llvm_ilist_destruct(llvm_global, Program->Globals);
  llvm_ilist_destruct(llvm_function, Program->Functions);
}

void llvm_dump() {
  llvm_program_print(stderr);
}

static inline void count_ctor_dtors(llvm_global_ctordtor *I, int *NumCtors,
                                    int *NumDtors) {
  (*(I->isCtor ? NumCtors : NumDtors))++;
}

static inline void print_ctor_dtors(llvm_global_ctordtor *I, int printCtors,
                                    int *NumObjects, FILE *F) {
  if (I->isCtor == printCtors) {
    if ((*NumObjects)++)
      fprintf(F, ",\n");
    fprintf(F, "       { int, void()* } { int %d, ", I->Priority);
    llvm_value_print_operand(G2V(I->Fn), 1, F);
    fprintf(F, " }");
  }
}

/* Print the specified program to the output file */
void llvm_program_print(FILE *F) {
  llvm_type_print_all_named(F);

  /* Output global ctors and dtors if there are any */
  if (!llvm_ilist_empty(llvm_global_ctordtor, TheProgram.GlobalCtorDtors)) {
    int NumCtors = 0, NumDtors = 0;
    llvm_ilist_foreach2(llvm_global_ctordtor, TheProgram.GlobalCtorDtors,
                        count_ctor_dtors, &NumCtors, &NumDtors);
    if (NumCtors) {
      fprintf(F, "; Static constructor initialization\n");
      fprintf(F,"%%llvm.global_ctors = appending global [%d x { int, void()* }]"
              " [\n", NumCtors);
      NumCtors = 0;
      llvm_ilist_foreach3(llvm_global_ctordtor, TheProgram.GlobalCtorDtors,
                          print_ctor_dtors, 1, &NumCtors, F);
      fprintf(F, "\n    ]\n\n");
    }
    if (NumDtors) {
      fprintf(F, "; Static destructor initialization\n");
      fprintf(F,"%%llvm.global_dtors = appending global [%d x { int, void()* }]"
              " [\n", NumDtors);
      NumDtors = 0;
      llvm_ilist_foreach3(llvm_global_ctordtor, TheProgram.GlobalCtorDtors,
                          print_ctor_dtors, 0, &NumDtors, F);
      fprintf(F, "\n    ]\n\n");
    }
  }

  /* Output the rest of the global variables... */
  llvm_ilist_foreach1(llvm_global, TheProgram.Globals, llvm_global_print, F);

  fprintf(F, "\nimplementation\n");

  /* Output the function bodies */
  llvm_ilist_foreach1(llvm_function, TheProgram.Functions,
		      llvm_function_print, F);
}

/* pphtab implementation ********************************************
 */

htab_t phset_new(unsigned InitialSize) {
  return htab_create(InitialSize, htab_hash_pointer, htab_eq_pointer, 0);
}

void pph_delete(htab_t HT) {
  htab_delete(HT);
}

/* pphtab_contains - Return true if the specified value is in the table */
int phset_contains(htab_t HT, void *Key) {
  return htab_find(HT, Key) != 0;
}

#if 0 /* FIXME */
/* pphtab_lookup - Return the value if the specified key is in the table, else
   return null.
*/
void *pphtab_lookup(htab_t HT, void *Key) {
  return htab_find(HT, Key);
}

/* pphtab_lookup_slot - Find (and create if not in the table) the place in the
   table a pointer should exist.  This returns a pointer to the pointer so a new
   entry may be inserted if desired.
*/
void **pphtab_lookup_slot(htab_t HT, void *Key) {
  return htab_find_slot(HT, Key, INSERT);
}
#endif

/* phset_insert - Insert a value into the set.
*/
void phset_insert(htab_t HT, void *Key) {
  *htab_find_slot(HT, Key, INSERT) = Key;
}
