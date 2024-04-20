/* Implement the LLVM type system
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
#include "tree.h"
#include "llvm-representation.h"
#include "llvm-internals.h"
#include "hashtab.h"
#include <assert.h>
#include <string.h>

static int llvm_type_is_deep_equal(llvm_type *T1, llvm_type *T2);

unsigned llvm_type_get_composite_num_elements(llvm_type *Ty) {
  if (Ty->ID == StructTyID)
    return Ty->NumElements;
  assert(Ty->ID == ArrayTyID && "Bad composite type!");
  return Ty->x.Array.Size;
}

llvm_type *llvm_type_get_composite_element(llvm_type *Ty, unsigned N) {
  if (Ty->ID == StructTyID)
    return Ty->Elements[N];
  assert(Ty->ID == ArrayTyID && "Bad composite type!");
  return Ty->Elements[0];
}

unsigned llvm_type_get_size(llvm_type *Ty) {
  switch (Ty->ID) {
  case BoolTyID:   
  case SByteTyID:  
  case UByteTyID:  return 1;
  case ShortTyID:  
  case UShortTyID: return 2;
  case UIntTyID:   
  case FloatTyID:  
  case IntTyID:    return 4;
  case ULongTyID:  
  case LongTyID:   
  case DoubleTyID: return 8;
  case ArrayTyID: return llvm_type_get_size(Ty->Elements[0])*Ty->x.Array.Size;
  case StructTyID: return Ty->x.Struct.Size;
  case PointerTyID: /* Target dependant pointer size */
    return (TREE_INT_CST_LOW(TYPE_SIZE(ptr_type_node))+7)/8;
  default: 
    fprintf(stderr, "ERROR: Type doesn't have size: ");
    llvm_type_dump(Ty);
    fprintf(stderr, "\n");
    abort();
  }
}

/* All of the primitive types... */
static llvm_type TheVoidTy   = { VoidTyID };
static llvm_type TheBoolTy   = { BoolTyID };
static llvm_type TheUByteTy  = { UByteTyID };
static llvm_type TheSByteTy  = { SByteTyID };
static llvm_type TheUShortTy = { UShortTyID };
static llvm_type TheShortTy  = { ShortTyID };
static llvm_type TheUIntTy   = { UIntTyID };
static llvm_type TheIntTy    = { IntTyID };
static llvm_type TheULongTy  = { ULongTyID };
static llvm_type TheLongTy   = { LongTyID };
static llvm_type TheFloatTy  = { FloatTyID };
static llvm_type TheDoubleTy = { DoubleTyID };
static llvm_type TheLabelTy  = { LabelTyID };
llvm_type *VoidTy   = &TheVoidTy;
llvm_type *BoolTy   = &TheBoolTy;
llvm_type *UByteTy  = &TheUByteTy;
llvm_type *SByteTy  = &TheSByteTy;
llvm_type *UShortTy = &TheUShortTy;
llvm_type *ShortTy  = &TheShortTy;
llvm_type *UIntTy   = &TheUIntTy;
llvm_type *IntTy    = &TheIntTy;
llvm_type *ULongTy  = &TheULongTy;
llvm_type *LongTy   = &TheLongTy;
llvm_type *FloatTy  = &TheFloatTy;
llvm_type *DoubleTy = &TheDoubleTy;
llvm_type *LabelTy  = &TheLabelTy;
llvm_type *VoidPtrTy = 0;

/*===---------------------------------------------------------------------===*\
 * More complex type functions built on primitives
 *===---------------------------------------------------------------------===*/

static htab_t StructTable;         /* hash<tree,llvm_type*> */

typedef struct StructTableEntry {
  tree TreeDecl;
  llvm_type *LLVMTy;
} StructTableEntry;

static int STE_eq(const void *p1, const void *p2) {
  const StructTableEntry *old = (const StructTableEntry*)p1;
  return old->TreeDecl == (tree)p2;
}
static hashval_t STE_hash(const void *P) {
  return htab_hash_pointer(((const StructTableEntry*)P)->TreeDecl);
}


/* llvm_InitializeTypeSystem - Initialize the type system before any
   requests are made */
void llvm_InitializeTypeSystem(void) {
  /* Initalize the hashtable of all of the structure types. */
  StructTable = htab_create(256, STE_hash, STE_eq, 0);

  /* Commonly used derived types... */
  VoidPtrTy = llvm_type_get_pointer(VoidTy);
}

/* List of all the derived types so that only one of a particular shape is
 * created.
 *
 * TODO: This is horribly inefficient.  At the very least, we could do
 * something like the LLVM sources do to speed this up, but right now
 * I don't care.
 */
static llvm_type *DerivedTypesList = 0;

llvm_type *llvm_type_get_cannonical_version(llvm_type *Ty) {
  llvm_type *TyList = DerivedTypesList;
  while (TyList) {
    if (llvm_type_is_deep_equal(TyList, Ty)) {  /* Found a match! */
      if (Ty != TyList) free(Ty);
      return TyList;
    }
    TyList = TyList->NextTypeLink;
  }

  /* Didn't find a match, the passed value is the cannonical form.  Add to list
   * and return it.
   */
  Ty->NextTypeLink = DerivedTypesList;
  DerivedTypesList = Ty;

  /*printf("Created new type: "); DebugType(Ty); printf("\n"); */
  return Ty;
}

llvm_type *llvm_type_get_array(llvm_type *Ty, unsigned NumElements) {
  llvm_type *Result = (llvm_type*)xcalloc(1, sizeof(llvm_type));
  Result->ID = ArrayTyID;
  Result->NumElements = 1;
  Result->Elements[0] = Ty;
  Result->x.Array.Size = NumElements;
  return llvm_type_get_cannonical_version(Result);
}

llvm_type *llvm_type_get_pointer(llvm_type *Ty) {
  llvm_type *Result = (llvm_type*)xcalloc(1, sizeof(llvm_type));
  Result->ID = PointerTyID;
  Result->NumElements = 1;
#if 1
  /* Don't create void pointers!  Create sbyte pointers instead! */
  if (Ty == VoidTy) Ty = SByteTy;
#endif

  Result->Elements[0] = Ty;
  return llvm_type_get_cannonical_version(Result);
}

llvm_type *llvm_type_create_function(unsigned NumParams,llvm_type *RetTy){
  llvm_type *Result = (llvm_type*)xcalloc(1, sizeof(llvm_type) +
					  NumParams*sizeof(llvm_type*));
  Result->ID = FunctionTyID;
  Result->NumElements = 1+NumParams;
  Result->Elements[0] = RetTy;
  return Result;
}

llvm_type *llvm_type_create_struct(unsigned NumElements, unsigned Size) {
  llvm_type *Result = (llvm_type*)xcalloc(1, sizeof(llvm_type) +
					  (NumElements-1)*sizeof(llvm_type*));
  Result->ID = StructTyID;
  Result->NumElements = NumElements;
  Result->x.Struct.Size = Size;

  /* Allocate space for member offset information. */
  Result->x.Struct.MemberOffsets =
    (unsigned*)xmalloc(sizeof(unsigned)*NumElements);
  return Result;
}

static llvm_type *llvm_type_create_opaque(const char *Prefix,
                                          const char *StructName) {
  unsigned PrefLen = strlen(Prefix);
  char *NewName = xmalloc(strlen(StructName)+PrefLen+1);
  llvm_type *Result = (llvm_type*)xcalloc(1, sizeof(llvm_type) -
					  sizeof(llvm_type*));
  assert(StructName && StructName[0] && "No null name for opaque type!");
  strcat(strcpy(NewName, Prefix), StructName);

  Result->ID = OpaqueTyID;
  Result->x.Opaque.TypeName = NewName;
  return llvm_type_get_cannonical_version(Result);
}

/* TypeEqual - This is used to maintain a list of types that are each unique
 * singletons for each type.  Because only one object of each type is ever
 * created, users can always do pointer comparisons between types to check for
 * exact equality.
 */
static int llvm_type_is_deep_equal(llvm_type *T1, llvm_type *T2) {
  unsigned i;
  if (T1 == T2) return 1;
  /* Both types must have equal IDs */
  if (T2 == 0 || T1->ID != T2->ID) return 0;
  if (llvm_type_is_primitive(T1)) return 1;

  if (T1->NumElements != T2->NumElements) return 0;

  switch (T1->ID) {
  case FunctionTyID:
    if (T1->x.Function.isVarArg != T2->x.Function.isVarArg) return 0;
    break;
  case ArrayTyID:
    if (T1->x.Array.Size != T2->x.Array.Size) return 0;
    break;
  case OpaqueTyID:
    return !strcmp(T1->x.Opaque.TypeName, T2->x.Opaque.TypeName);
  case StructTyID:
    /* One is null and the other isn't? */
    if (!T1->x.Struct.TypeName != !T2->x.Struct.TypeName) return 0;
    if (T1->x.Struct.TypeName && 
	strcmp(T1->x.Struct.TypeName, T2->x.Struct.TypeName))
      return 0;   /* Name mismatch. */
    break;

  case PointerTyID:
    break;
  default:
    assert(0 && "Unknown type!");
    abort();
  }
  
  for (i = 0; i != T1->NumElements; ++i)
    if (!llvm_type_is_deep_equal(T1->Elements[i], T2->Elements[i]))
      return 0;
  return 1;
}

static void llvm_type_print_struct_expand(llvm_type *Ty, FILE *F) {
  if (Ty->ID == StructTyID) {
    unsigned i;
    fprintf(F, "{ ");
    for (i = 0; i < Ty->NumElements; ++i) {
      if (i != 0) fprintf(F, ", ");
      llvm_type_print(Ty->Elements[i], F);
    }
    fprintf(F, " }");
  } else {
    llvm_type_print(Ty, F);
  }
}

static void print_struct_typename(const char *Name, FILE *F) {
  int isSimple = 1, i;

  /* Scan all of the characters in the type name.  If any of them are not
   *  "simple", print out the type name in double quotes.
   */
  for (i = 0; Name[i]; ++i) {
    char C = Name[i];

    assert(C != '"' && "Single quote in type name is illegal!");
    if ((C < 'a' || C > 'z') && (C < 'A' || C > 'Z') && (C < '0' || C > '9') &&
        C != '-' && C != '.' && C != '_') {
      isSimple = 0;
      break;
    }
  }

  if (isSimple)
    fprintf(F, "%%%s", Name);
  else
    fprintf(F, "\"%s\"", Name);
}

void llvm_type_dump(llvm_type *Ty) {
  if (Ty->ID == StructTyID && Ty->x.Struct.TypeName) {
    print_struct_typename(Ty->x.Struct.TypeName, stderr);
    fprintf(stderr, " = type ");
    llvm_type_print_struct_expand(Ty, stderr);
  } else {
    llvm_type_print(Ty, stderr);
  }
  fprintf(stderr, "\n");
}


void llvm_type_print(llvm_type *Ty, FILE *F) {
  if (Ty == 0) {
    fprintf(F, "<null type>");
    return;
  }
  switch (Ty->ID) {
  case VoidTyID:   fprintf(F, "void"); break;
  case BoolTyID:   fprintf(F, "bool"); break;
  case SByteTyID:  fprintf(F, "sbyte"); break;
  case UByteTyID:  fprintf(F, "ubyte"); break;
  case ShortTyID:  fprintf(F, "short"); break;
  case UShortTyID: fprintf(F, "ushort"); break;
  case UIntTyID:   fprintf(F, "uint"); break;
  case IntTyID:    fprintf(F, "int"); break;
  case ULongTyID:  fprintf(F, "ulong"); break;
  case LongTyID:   fprintf(F, "long"); break;
  case DoubleTyID: fprintf(F, "double"); break;
  case FloatTyID:  fprintf(F, "float"); break;
  case LabelTyID:  fprintf(F, "label"); break;
  case FunctionTyID: {
    unsigned i;
    llvm_type_print(Ty->Elements[0], F);  /* return value */
    fprintf(F, " (");
    for (i = 1; i < Ty->NumElements; ++i) {
      if (i != 1) fprintf(F, ", ");
      llvm_type_print(Ty->Elements[i], F);
    }
    if (Ty->x.Function.isVarArg) {
      if (Ty->NumElements > 1) fprintf(F, ", ");
      fprintf(F, "...");
    }
    fprintf(F, ")");
    break;
  }

  case StructTyID:
    if (Ty->x.Struct.TypeName)
      print_struct_typename(Ty->x.Struct.TypeName, F);
    else
      llvm_type_print_struct_expand(Ty, F);
    break;

  case OpaqueTyID:
    print_struct_typename(Ty->x.Opaque.TypeName, F);
    break;

  case ArrayTyID:
    fprintf(F, "[%d x ", Ty->x.Array.Size);
    llvm_type_print(Ty->Elements[0], F);
    fprintf(F, "]"); break;
  case PointerTyID:
    llvm_type_print(Ty->Elements[0], F);
    fprintf(F, "*");
    break;
  default:
    fprintf(F, "<Unknown Type: %d>", Ty->ID);
    break;
  }
}

/* llvm_type_get_promoted_type - Perform C style argument promotion on the
 * specified LLVM type.  For example sbyte->int and float->double.  Return the
 * promoted type.
 */
llvm_type *llvm_type_get_promoted_type(llvm_type *Ty) {
  switch (Ty->ID) {
  case SByteTyID:
  case ShortTyID:
    return IntTy;
  case UByteTyID:
  case UShortTyID:
    return UIntTy;
  case FloatTyID:
    return DoubleTy;
  default:
    return Ty;
  }
}


/* This function prints the type list in reverse order.  If this causes a
   problem due to stack depth at some point, we should change construction of
   types to add them to the end of the list, not the start */
static void llvm_type_print_all_named_types_recursively(llvm_type *T, FILE *F) {
  if (T == 0) return;
  llvm_type_print_all_named_types_recursively(T->NextTypeLink, F);

  if (T->ID == StructTyID && T->x.Struct.TypeName) {
    print_struct_typename(T->x.Struct.TypeName, F);
    fprintf(F, " = type ");
    llvm_type_print_struct_expand(T, F);
    fprintf(F, "\n");
  } else if (T->ID == OpaqueTyID && T->x.Struct.TypeName) {
    print_struct_typename(T->x.Struct.TypeName, F);
    fprintf(F, " = type opaque\n");
  }
}

void llvm_type_print_all_named(FILE *F) {
  llvm_type_print_all_named_types_recursively(DerivedTypesList, F);
#if 0  /* Iterative printer, prints types out backwards */
  llvm_type *T = DerivedTypesList;
  for (; T; T = T->NextTypeLink)
    if (T->ID == StructTyID) {
      print_struct_typename(Ty->x.Struct.TypeName, F);
      fprintf(F, " = type ");
      llvm_type_print_struct_expand(T, F);
      fprintf(F, "\n");
    } else if (T->ID == OpaqueTyID) {
      print_struct_typename(Ty->x.Struct.TypeName, F);
      fprintf(F, " = type opaque\n");
    }
#endif
}

/* get_num_recursive_elements - Walk the value type recursively, counting the
   number of values that would need to be passed if this is passed as a
   structure argument by value. */
unsigned llvm_type_get_num_recursive_elements(llvm_type *Ty) {
  if (llvm_type_is_composite(Ty)) {
    unsigned i, Result = 0;
    for (i = 0; i < llvm_type_get_composite_num_elements(Ty); ++i) {
      llvm_type *ElTy = llvm_type_get_composite_element(Ty, i);
      Result += llvm_type_get_num_recursive_elements(ElTy);
    }
    return Result;
  }
  return 1;
}

/* SetFunctionArgs - Add ArgTy to the list of arguments in MethTy.  This could
 * be a composite type, expanding into many actual LLVM arguments.  Insert them
 * into the method type at location ArgNo, and return the actual number of
 * arguments inserted.
 */
unsigned SetFunctionArgs(llvm_type *FuncTy, unsigned ArgNo, llvm_type *ArgTy) {
  if (llvm_type_is_composite(ArgTy)) {
    unsigned NumInserted = 0, i;
    for (i = 0; i < llvm_type_get_composite_num_elements(ArgTy); ++i) {
      unsigned NI = SetFunctionArgs(FuncTy, ArgNo,
                                    llvm_type_get_composite_element(ArgTy, i));
      ArgNo += NI;
      NumInserted += NI;
    }
    return NumInserted;
  } else {
    FuncTy->Elements[ArgNo] = ArgTy;
    return 1;
  }
}

llvm_type *llvm_type_get_integer(unsigned NumBits, int isUnsigned) {
  switch (NumBits*2+!isUnsigned) {
  case 8*2+0 : return UByteTy;
  case 8*2+1 : return SByteTy;
  case 16*2+0: return UShortTy;
  case 16*2+1: return ShortTy;
  case 32*2+0: return UIntTy;
  case 32*2+1: return IntTy;
  case 64*2+0: return ULongTy;
  case 64*2+1: return LongTy;
    
  case 128*2+0: {
    static int Warned = 0;
    if (!Warned) fprintf(stderr, "WARNING: 128 bit integers used, but broken in LLVM!\n");
    Warned = 1;
    return ULongTy;
  }
  case 128*2+1: {
    static int Warned = 0;
    if (!Warned) fprintf(stderr, "WARNING: 128 bit integers used, but broken in LLVM!\n");
    Warned = 1;
    return LongTy;
  }
  default: 
    fprintf(stderr, "UNKNOWN INTEGRAL TYPE SIZE: %d\n", NumBits);
    abort();
  }
}

static tree GetNextFieldDecl(tree Field) {
  do Field = TREE_CHAIN(Field);
  while (Field && TREE_CODE(Field) != FIELD_DECL);
  return Field;
}

/* GetFieldAlignmentInBits - This returns the desired alignment of the
 * specified fields, which may not be the DECL_ALIGN value.  :(
 */
static unsigned GetFieldAlignmentInBits(tree field) {
  unsigned Align = /*DECL_ALIGN(field);*/
    TYPE_ALIGN(TREE_TYPE(field));
  if (DECL_USER_ALIGN(field))
    Align = DECL_USER_ALIGN(field);

  /* Some targets (i.e. i386, VMS) limit struct field alignment
     to a lower boundary than alignment of variables unless
     it was overridden by attribute aligned.  */
#ifdef BIGGEST_FIELD_ALIGNMENT
  Align = MIN (Align, (unsigned) BIGGEST_FIELD_ALIGNMENT);
#endif
  
#ifdef ADJUST_FIELD_ALIGN
  Align = ADJUST_FIELD_ALIGN (field, Align);
#endif

  if (Align == 0) return 1;  /* Do not return an alignment of 0 bytes */

  return Align;
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

#define DEBUG_STRUCT_LAYOUT 0

static void PrintFieldInfo(tree field ATTRIBUTE_UNUSED) {
#if DEBUG_STRUCT_LAYOUT
  llvm_type *FieldTy = llvm_type_get_from_tree(TREE_TYPE(field));
  fprintf(stderr, "FIELD: off=%d size=%d ",
          GetFieldOffset(field), GetDeclSize(field));
  llvm_type_print(FieldTy, stderr);
  fprintf(stderr, " name='%s' talign=%d dalign=%d\n", DECL_NAME(field) ? 
          IDENTIFIER_POINTER(DECL_NAME(field)) : "<empty>",
          GetFieldAlignmentInBits(field), TYPE_ALIGN(TREE_TYPE(field))/8);
#endif
}


/* For bit-field layout, "integral" types are treated differently than other
 * types.  In particular, bitfields can share space with these "integral" types,
 * which are more general than the LLVM integral types.  In particular, arrays
 * of integral types and structures of integral types can be merged into
 * bitfields, like this:
 *
 *     struct istruct { unsigned char C; };
 *     struct foo { unsigned int I:1; struct istruct J;
 *                  unsigned char L[1]; unsigned int K:1; };
 *
 * ... gets turned into the LLVM type { int }.
 */
static int TypeIsRecursivelyIntegral(llvm_type *Ty) {
  if (Ty == 0) return 0;
  if (llvm_type_is_integral(Ty))
    return 1;
  else if (Ty->ID == ArrayTyID)
    return TypeIsRecursivelyIntegral(GET_ARRAY_TYPE_ELEMENT(Ty));
  else if (Ty->ID == StructTyID) {
    unsigned i;
    for (i = 0; i < Ty->NumElements; ++i)
      if (!TypeIsRecursivelyIntegral(GET_STRUCT_TYPE_ELEMENT(Ty, i)))
        return 0;
    return 1;
  }
  return 0;
}


/* DecodeFieldDecl - This function is used to lay out structure fields according
 * to the Itanium C ABI.  Given a FIELD_DECL list, it figures out how many field
 * decls fit together into a single llvm type element, and (if ResultTy is not
 * null) fills in the element for the type.  It indexes the *Idx variable to
 * account for how many LLVM type elements it needs to insert.
 */
static void DecodeFieldDecl(tree field, llvm_type **ElementTys,
                            unsigned *ElementOffsets,
                            unsigned *ElementAlignments,
                            unsigned *Idx,
                            unsigned *Size) {
  llvm_type *Ty = llvm_type_get_from_tree(TREE_TYPE(field));
  /* Get the starting offset in the record... */
  unsigned StartOffset = GetFieldOffset(field);               /* In bits */
  unsigned BitAlignment = GetFieldAlignmentInBits(field);    /* In bits */
  unsigned ByteAlignment = (BitAlignment+7)/8;
  
  if (!TypeIsRecursivelyIntegral(Ty)) {             /* Not an integral field? */
    /* If this field is not an integral type, just include it directly. */
    assert((StartOffset & 7) == 0 && "Member not byte aligned??");

    /* Round *Size up to take into consideration alignment of this field */
    *Size = (*Size + ByteAlignment - 1) & ~(ByteAlignment-1);

    /* Check to see if there is "magic padding" that got inserted into the
     * structure.  This can happen, for example, when the C++ ABI declares that
     * two types to not exist at the same offset.  For this reason, a byte of
     * padding is inserted, and then the layout of the next element occurs at
     * whatever alignment is reasonable for it.
     */
    if (*Size < StartOffset/8)
      /* Only fix things if it is because of this "magic padding" */
      if (*Size + ByteAlignment == StartOffset/8) {
        ElementTys[*Idx] = UByteTy;    /* Random pad element */
        ElementOffsets[*Idx] = *Size;
        ElementAlignments[*Idx] = 1;
        ++*Idx;
        *Size = StartOffset/8;
      }

#if 0  /* FIXME: This assertion should be kept!!! */
    assert(*Size == StartOffset/8 &&
           "Member does not start where we think it does?");
#endif
    ElementTys[*Idx] = Ty;
    ElementOffsets[*Idx] = StartOffset/8;
    ElementAlignments[*Idx] = ByteAlignment;
    *Size = StartOffset/8 + llvm_type_get_size(Ty);
    ++*Idx;
  } else if (DECL_NAME(field) == 0) {       /* Is this an anonymous bitfield? */
    unsigned NumPads;
    /* Is it attempting to align the current offset to some value? */
    if (GetDeclSize(field) == 0) {
      NumPads = ByteAlignment - (*Size % ByteAlignment);
      if (NumPads == ByteAlignment) NumPads = 0;
      assert((*Size+NumPads) % ByteAlignment == 0 &&"Incorrect padding calc?");
#if DEBUG_STRUCT_LAYOUT
      fprintf(stderr, "Anon field: align=%db pads = %d ",
              BitAlignment, NumPads);
      PrintFieldInfo(field);
#endif
    } else {
      /* Otherwise we are just padding out for an unnamed bitfield.  This does
       * not affect alignment, so we just insert the appropriate number of
       * ubytes.  EndByte is the byte that the last bit of the unnamed bitfield
       * falls into.
       */
      unsigned EndByte = (StartOffset+GetDeclSize(field)+7)/8;
      NumPads = EndByte - *Size;
    }

    /* Add "NumPads" ubyte elements to the structure. */
    for (; NumPads; --NumPads) {
      ElementTys[*Idx] = UByteTy;
      ElementOffsets[*Idx] = *Size;
      ElementAlignments[*Idx] = 1;
      ++*Size;
      ++*Idx;
    }
  } else {
    /* Otherwise, this is a normal, named, integer bitfield. Figure out the size
     * of the element to emit.  It appears that the element size can be shrunk
     * if the alignment allows for it.  Thus, we start out with the element
     * size, and round up to the alignment as necessary.
     */
    unsigned ElSize = GetDeclSize(field);  /* In bits */
    int HasSignedField;
    unsigned StartByte;
    if (BitAlignment > ElSize) ElSize = BitAlignment;

    HasSignedField = !TREE_UNSIGNED(TREE_TYPE(field));

    /* Calculate the first byte occupied by this field */
    StartByte = StartOffset/8 - (StartOffset/8) % ByteAlignment;

    /* Check to see if we have emitted any structure elements that overlap with
     * the current bitfield.
     */
    if (StartByte < *Size) {/* Some bits of field have already been emitted. */
      /* Check to see if we have already emitted a structure field which totally
       * encompasses this type.  If so, we just have to update the signedness if
       * the field is not yet signed.
       */
      if (StartByte*8+ElSize <= *Size * 8) {
        assert(ElementOffsets[*Idx-1] <= StartByte &&
               ElementAlignments[*Idx-1] >= ByteAlignment &&
               "Less aligned field overlaps with later, more aligned, field?");
        /* If the last field is a bool, expand it to be a uchar */
        if (ElementTys[*Idx-1] == BoolTy)
          ElementTys[*Idx-1] = UByteTy;
        /* If the field becomes signed, rewrite it. */
        if (HasSignedField && !llvm_type_is_signed(ElementTys[*Idx-1])) {
          ElementTys[*Idx-1] =
            llvm_type_get_integer(llvm_type_get_size(ElementTys[*Idx-1])*8, 0);
        }
        return;
      }

      /* Peel all overlapping existing elements off, keeping track of whether
       * any were signed.
       */
      do {
        --*Idx;  /* Remove an element. */
        HasSignedField |= llvm_type_is_signed(ElementTys[*Idx]);
        if (*Idx)
          *Size = ElementOffsets[*Idx-1]+llvm_type_get_size(ElementTys[*Idx-1]);
        else
          *Size = 0;
      } while (*Idx && *Size > StartByte);

      Ty = llvm_type_get_integer(ElSize, !HasSignedField);
    }

    /* Check to see if there is "magic padding" that got inserted into the
     * structure.  This can happen, for example, when the C++ ABI declares that
     * two types to not exist at the same offset.  For this reason, a byte of
     * padding is inserted, and then the layout of the next element occurs at
     * whatever alignment is reasonable for it.
     */
    if (*Size < StartByte)
      /* Only fix things if it is because of this "magic padding" */
      if (*Size + ByteAlignment == StartByte) {
        ElementTys[*Idx] = UByteTy;    /* Random pad element */
        ElementOffsets[*Idx] = *Size;
        ElementAlignments[*Idx] = 1;
        ++*Idx;
        *Size = StartByte;
      }

    /* Add the new element... */
    ElementTys[*Idx] = Ty;
    ElementOffsets[*Idx] = StartByte;
    ElementAlignments[*Idx] = ByteAlignment;
    *Size = StartByte + llvm_type_get_size(Ty);
    ++*Idx;
  }
}

static char *get_type_name(const char *Name, const char *Prefix, tree Context) {
  unsigned NameLen = strlen(Name), Size = NameLen + strlen(Prefix)+1;
  unsigned UsedLen = Size;
  char *Buffer = (char*)xmalloc(Size);
  strcpy(Buffer, Name);

  /* Loop through all of the context information for this type to build up the
   * name.  This includes things like namespaces.  If the type is anything other
   * than namespaces and a file, we assign a unique ID to it.
   */
  while (Context) {
    switch (TREE_CODE(Context)) {
    case TRANSLATION_UNIT_DECL: Context = 0; break;   /* Got to the file */
    case NAMESPACE_DECL:
    case RECORD_TYPE:
      if (TREE_CODE(Context) == RECORD_TYPE) {
        if (TYPE_NAME(Context)) {
          const char *NameFrag = 0;
          if (TREE_CODE(TYPE_NAME(Context)) == IDENTIFIER_NODE) {
            NameFrag = IDENTIFIER_POINTER(TYPE_NAME(Context));
          } else {
            NameFrag = IDENTIFIER_POINTER(DECL_NAME(TYPE_NAME(Context)));
          }

          UsedLen += strlen(NameFrag)+2;
          if (UsedLen > Size)
            Buffer = xrealloc(Buffer, UsedLen);
          
          memmove(Buffer+strlen(NameFrag)+2, Buffer, strlen(Buffer)+1);
          strcpy(Buffer, NameFrag);
          memcpy(Buffer+strlen(NameFrag), "::", 2);
          Context = TYPE_CONTEXT(Context);
          break;
        }
      } else if (DECL_NAME(Context)
          /*&& DECL_NAME(Context) != anonymous_namespace_name*/){
        const char *NamespaceName;
        assert(TREE_CODE(DECL_NAME(Context)) == IDENTIFIER_NODE);
        NamespaceName = IDENTIFIER_POINTER(DECL_NAME(Context));
        UsedLen += strlen(NamespaceName)+2;
        if (UsedLen > Size)
          Buffer = xrealloc(Buffer, UsedLen);

        memmove(Buffer+strlen(NamespaceName)+2, Buffer, strlen(Buffer)+1);
        strcpy(Buffer, NamespaceName);
        memcpy(Buffer+strlen(NamespaceName), "::", 2);
        Context = DECL_CONTEXT(Context);
        break;
      }
      /* FALL THROUGH for anonymous namespaces! */

    default: {
      /* If this is a structure type defined inside of a function or other block
       * scope, make sure to make the type name unique by putting a unique ID
       * in it.
       */
      static int UniqueID = 0;
      UsedLen += 7;
      if (UsedLen > Size) {
        Buffer = xrealloc(Buffer, UsedLen);
        sprintf(Buffer+strlen(Buffer), "%d.", UniqueID++);
        Context = 0;   /* Stop looking at context */
        break;
      }
    }
    }
  }

  memmove(Buffer+strlen(Prefix), Buffer, strlen(Buffer)+1);
  return memcpy(Buffer, Prefix, strlen(Prefix));
}

/* isPassedByInvisibleReference - Return true if an argument of the specified
 * type should be passed in by invisible reference.
 */
int isPassedByInvisibleReference(tree Type) {
  /* FIXME: Search for TREE_ADDRESSABLE in calls.c, and see if there are other
   * cases that make arguments automatically passed in by reference.
   */
  return TREE_ADDRESSABLE(Type);
}

/* llvm_type_get_tree_type - Return the LLVM type that corresponds to the
 * specified tree type.  If this is the first time we have seen a structure
 * type, we assign indexes to all of the FIELD_DECLs in it.
 */
llvm_type *llvm_type_get_from_tree(tree orig_type) {
  llvm_type *Result = 0;
  tree type;
  if (orig_type == error_mark_node) return IntTy;

  /* LLVM doesn't care about variants such as const, volatile, or restrict
   */
  type = TYPE_MAIN_VARIANT(orig_type);

  switch (TREE_CODE(type)) {
  case ERROR_MARK: printf("<ERRORMARK FOUND!>\n"); abort();
  case METHOD_TYPE:
  case FUNCTION_TYPE: {
    llvm_type *RetType = llvm_type_get_from_tree(TREE_TYPE(type));
    llvm_type *FirstArgTy = 0;  /* Non-null if returning a struct */
    unsigned NumArgs = 0, i;

    /* Loop over all of the args, counting how many there are */
    tree Args = TYPE_ARG_TYPES(type);
    for (; Args && TREE_VALUE(Args) != void_type_node; Args = TREE_CHAIN(Args)){
      llvm_type *ArgTy = llvm_type_get_from_tree(TREE_VALUE(Args));
      if (isPassedByInvisibleReference(TREE_VALUE(Args)))
        ArgTy = llvm_type_get_pointer(ArgTy);
          
      NumArgs += llvm_type_get_num_recursive_elements(ArgTy);
    }

    /* If the function returns a struct, then it REALLY will be
     * returning void and taking struct argument as it's first
     * parameter.
     */
    if (RetType->ID == StructTyID) {
      FirstArgTy = llvm_type_get_pointer(RetType);
      NumArgs++;
      RetType = VoidTy;
    }

    Result = llvm_type_create_function(NumArgs, RetType);
    if (!Args) Result->x.Function.isVarArg = 1;
    if (FirstArgTy) Result->Elements[1] = FirstArgTy;

    Args = TYPE_ARG_TYPES(type);
    for (i = (FirstArgTy != 0)+1; i < NumArgs+1; Args = TREE_CHAIN(Args)) {
      /*fprintf(stderr, "FUNCTION DECL TREE_TYPE %d:\n", i);
	debug_tree(Args); */
      llvm_type *Ty = llvm_type_get_from_tree(TREE_VALUE(Args));
      if (isPassedByInvisibleReference(TREE_VALUE(Args)))
        Ty = llvm_type_get_pointer(Ty);

      i += SetFunctionArgs(Result, i, Ty);
    }
    return llvm_type_get_cannonical_version(Result);
  }

  case POINTER_TYPE:
  case REFERENCE_TYPE:
    return llvm_type_get_pointer(llvm_type_get_from_tree(TREE_TYPE(type)));

  case ARRAY_TYPE: {
    unsigned NumElements;
    if (TYPE_DOMAIN(type) && TYPE_MAX_VALUE(TYPE_DOMAIN(type)) &&
        TREE_CODE(TYPE_MAX_VALUE(TYPE_DOMAIN(type))) == INTEGER_CST) {
      NumElements = TREE_INT_CST_LOW(TYPE_MAX_VALUE(TYPE_DOMAIN(type)))+1;
    } else {
      /* Otherwise the reasons we could get here is if they have something that
       * is globally declared as an array with no dimension, this becomes just a
       * zero size array of the element type so that: int X[] becomes *'%X =
       * external global [0 x int]'
       *
       * Note that this also affects new expressions, which return a pointer to
       * an unsized array of elements.  This also effects things like "int A[n]"
       * which has an runtime constant number of elements, but is a compile-time
       * variable.
       */
      NumElements = 0;
    }

    return llvm_type_get_array(llvm_type_get_from_tree(TREE_TYPE(type)),
			       NumElements);
  }

  case OFFSET_TYPE:
    /* Handle OFFSET_TYPE specially.  This is used for pointers to members,
     * which are really just integer offsets.  As such, return the appropriate
     * integer directly.
     */
    switch (llvm_type_get_size(VoidPtrTy)) {
    case 4: return IntTy;
    case 8: return LongTy;
    default:
      assert(0 && "Unknown pointer size!");
    }

  case UNION_TYPE: {
    tree Field = TYPE_FIELDS(type);
    StructTableEntry **HTEP;
    unsigned MaxSize = 0, MaxAlign = 0;
    llvm_type *ElementType = 0;

    /* Is it a forward declaration? */
    if (TYPE_SIZE(type) == 0) { /* Yes, handle this. */
      const char *Name;
      if (TREE_CODE(TYPE_NAME(type)) == IDENTIFIER_NODE)
        Name = IDENTIFIER_POINTER(TYPE_NAME(type));
      else 
        Name = IDENTIFIER_POINTER(DECL_NAME(TYPE_NAME(type)));
      return llvm_type_create_opaque("union.", Name);
    }

    /* If this is a union with the transparent_union attribute set, it is
     * treated as if it were just the same as its first type.  Transparent
     * unions do not turn into LLVM records.
     */
    if (TYPE_TRANSPARENT_UNION(orig_type)) {
      assert(Field && "Transparent union must have some elements!");
      if (TREE_CODE(Field) != FIELD_DECL) Field = GetNextFieldDecl(Field);
      assert(Field && "Transparent union must have some elements!");

      return llvm_type_get_from_tree(TREE_TYPE(Field));
    }

    /* Prevent infinite recursion in cases where this is a recursive type.
     */
    HTEP = (StructTableEntry**)htab_find_slot_with_hash(StructTable, type,
						       htab_hash_pointer(type),
							INSERT);
    if (*HTEP) {
      /* Found a recursive type: Look up the cannonical version in the hash
       * table that we keep of all of the types... later, before we process
       * elements of the structure, we add the proto-struct type to the table.
       */
      return (*HTEP)->LLVMTy;  /* Complete the recursion */
    }

    /* Create the struct type... which always has one field in it, the largest
     * of the subelements...
     */
    Result = llvm_type_create_struct(2,(TREE_INT_CST_LOW(TYPE_SIZE(type))+7)/8);
    /* Allocate space for member offset information. */
    Result->x.Struct.MemberOffsets[0] = 0;

    if (TYPE_NAME(type)) { /* Set the name of the structure. */
      const char *Name;
      if (TREE_CODE(TYPE_NAME(type)) == IDENTIFIER_NODE)
        Name = IDENTIFIER_POINTER(TYPE_NAME(type));
      else 
        Name = IDENTIFIER_POINTER(DECL_NAME(TYPE_NAME(type)));

      Result->x.Struct.TypeName = get_type_name(Name, "union.",
                                                TYPE_CONTEXT(type));
    } else
      Result->x.Struct.TypeName = 0;

    /* Add the new structure type to the hash table of created structure types.
     */
    *HTEP = xmalloc(sizeof(StructTableEntry));      /* Fill in the entry... */
    (*HTEP)->TreeDecl = type;
    (*HTEP)->LLVMTy = Result;

    while (Field) {
      switch (TREE_CODE(Field)) {
      case FIELD_DECL: {        /* non-static data member */
        llvm_type *ElTy = llvm_type_get_from_tree(TREE_TYPE(Field));

        unsigned Offset = GetFieldOffset(Field);
        unsigned Size = TYPE_SIZE(TREE_TYPE(Field)) == 0 ? 0 :
                        TREE_INT_CST_LOW(TYPE_SIZE(TREE_TYPE(Field)));
        unsigned Align = TYPE_ALIGN(TREE_TYPE(Field));
        assert(Offset == 0 && "Offset always thought to be zero in union!");
        SET_DECL_LLVM(Field, llvm_constant_new_integral(UByteTy, 0));
        
        if (Align > MaxAlign) {
          MaxAlign = Align;
          MaxSize = Size;
          ElementType = ElTy;
        } else if (Align == MaxAlign) {
          if (Size > MaxSize ||
              (Size == MaxSize && (ElTy->ID != StructTyID ||
                                   llvm_type_is_fp(ElementType)))) {
            MaxSize = Size;
            ElementType = ElTy;
          }
        }
      }
	break;
      case VAR_DECL:            /* static data member */
      case CONST_DECL:          /* Enumeration in a class */
      case TYPE_DECL:           /* Typedef */
	break;
      default:
	printf("Unknown Union Field member! ID#%d\n", TREE_CODE(Field));
	break;
      }      
      Field = TREE_CHAIN(Field);
    }
    
    /* If there are no elements in the union, put a ubyte in there to make it
       have a size. */
    if (ElementType == 0) ElementType = UByteTy;

    if (MaxSize == llvm_type_get_size(Result)*8) {
      Result->NumElements = 1;   /* Trim off extra space. */
    } else {
      /* Make sure the union knows it is the right size. This can be because the
       * guiding member of the union was chosen because it has bigger alignment
       * than the other members of the union, but the other members have a
       * larger size.
       */
      unsigned NumPad = llvm_type_get_size(Result) - MaxSize/8;
      Result->x.Struct.MemberOffsets[1] = MaxSize;
      Result->Elements[1] = llvm_type_get_array(UByteTy, NumPad);
    }

    /* We have to be really careful here to avoid really wierd bugs.  The
     * problem occurs when we have chosen a structure type to act as the
     * "guiding member" of the structure.  In this case the structure could have
     * padding in places that overlaps with real data for other elements of the
     * enum.  Because we will not copy the padding around (because it's a
     * structure type), we will not copy the aliased data's values either,
     * causing obscure bugs.
     *
     * My sledgehammer to fixing this problem is looking to see if the chosen
     * element type is a structure and if so, convert it into a dense array of
     * char.  That should guarantee that all data is copied, even if it
     * absolutely kills any chance at all of typesafety.  There is only so much
     * you can do.  It would be better, of course, to only do this if the
     * selected structure type has padding, and if that padding overlaps with
     * other data.
     *
     * FIXME: Couldn't there be arrays that have structure types in them?
     * What about alignment?  This preserves size but not necessarily alignment!
     */
    if (ElementType->ID == StructTyID) {
      assert((MaxSize & 7) == 0 &&
              "Only unions that are multiple of byte size expected!");
      if (MaxSize & 0xF)
        ElementType = llvm_type_get_array(UByteTy, MaxSize >> 3);
      else if (MaxSize & 0x1F)
        ElementType = llvm_type_get_array(UShortTy, MaxSize >> 4);
      else if (MaxSize & 0x3F)
        ElementType = llvm_type_get_array(UIntTy, MaxSize >> 5);
      else
        ElementType = llvm_type_get_array(ULongTy, MaxSize >> 6);

      /* Don't make an array of one element... */
      if (GET_ARRAY_TYPE_SIZE(ElementType) == 1)
        ElementType = GET_ARRAY_TYPE_ELEMENT(ElementType);
    }

    Result->Elements[0] = ElementType;
    return ((*HTEP)->LLVMTy = llvm_type_get_cannonical_version(Result));
  }

  case RECORD_TYPE: {
    tree BaseTypes = TYPE_BINFO(type) ? BINFO_BASETYPES(TYPE_BINFO(type)) : 0;
    tree Field = TYPE_FIELDS(type);
    unsigned Idx, Size;
    StructTableEntry **HTEP;
    llvm_type *StructElements[200];  /* FIXME: Fixed size buffers are bad. */
    unsigned ElementOffsets[200];
    unsigned ElementAlignments[200];

    /* Is it a forward declaration? */
    if (TYPE_SIZE(type) == 0) { /* Yes, handle this. */
      const char *Name;
      if (TREE_CODE(TYPE_NAME(type)) == IDENTIFIER_NODE)
        Name = IDENTIFIER_POINTER(TYPE_NAME(type));
      else 
        Name = IDENTIFIER_POINTER(DECL_NAME(TYPE_NAME(type)));
      return llvm_type_create_opaque("struct.", Name);
    }

    /* Prevent infinite recursion in cases where this is a recursive type.
     */
    HTEP = (StructTableEntry**)htab_find_slot_with_hash(StructTable, type,
                                                        htab_hash_pointer(type),
							INSERT);
    if (*HTEP) {
      /* Found a recursive type: Look up the cannonical version in the hash
       * table that we keep of all of the types... later, before we process
       * elements of the structure, we add the proto-struct type to the table.
       */
      return (*HTEP)->LLVMTy;  /* Complete the recursion */
    }

    /* Construct LLVM types for the base types... in order to get names for
     * base classes.
     */
    if (BaseTypes)
      for (Idx = 0; Idx < (unsigned)TREE_VEC_LENGTH(BaseTypes); ++Idx)
        llvm_type_get_from_tree(BINFO_TYPE(TREE_VEC_ELT(BaseTypes, Idx)));

    /* Check to see if construction of base types involved conversion of this
     * structure type.
     */
    if (*HTEP && (*HTEP)->LLVMTy)
      return (*HTEP)->LLVMTy;


    /* Create the struct type.  This is a gross hack, because we don't know how
     * many elements there will be in the struct, but we must allocate the type
     * before calling llvm_type_get_from_tree, so we just allocate "enough"
     * space.
     */
    Result = llvm_type_create_struct(300,
                                     (TREE_INT_CST_LOW(TYPE_SIZE(type))+7)/8);
    /* Add the new structure type to the hash table of created structure types.
     */
    *HTEP = xmalloc(sizeof(StructTableEntry));      /* Fill in the entry... */
    (*HTEP)->TreeDecl = type;
    (*HTEP)->LLVMTy = Result;

    if (TYPE_NAME(type)) { /* Set the name of the structure. */
      const char *Name;
      if (TREE_CODE(TYPE_NAME(type)) == IDENTIFIER_NODE)
        Name = IDENTIFIER_POINTER(TYPE_NAME(type));
      else 
        Name = IDENTIFIER_POINTER(DECL_NAME(TYPE_NAME(type)));

      Result->x.Struct.TypeName = get_type_name(Name, "struct.",
                                                TYPE_CONTEXT(type));
    } else
      Result->x.Struct.TypeName = 0;
    
    Idx = 0; Size = 0;

#if DEBUG_STRUCT_LAYOUT
    fprintf(stderr, "\nLAYING OUT FIELDS: \n");
#endif

    /* Process all of the fields. */
    if (Field && TREE_CODE(Field) != FIELD_DECL)
      Field = GetNextFieldDecl(Field);
    for (; Field; Field = GetNextFieldDecl(Field)) {
      DecodeFieldDecl(Field, StructElements, ElementOffsets, ElementAlignments,
                      &Idx, &Size);

#if DEBUG_STRUCT_LAYOUT
      {
        unsigned i;
        fprintf(stderr, "After processessing field, structure is: { ");
        for (i = 0; i != Idx; ++i) {
          llvm_type_print(StructElements[i], stderr);
          fprintf(stderr, "[%d][%d], ", ElementOffsets[i],ElementAlignments[i]);
        }
        fprintf(stderr, "}\n");
      }
#endif
    }

    /* Empty C++ structures == { ubyte } in LLVM so that sizes are correct. */
    if (Idx == 0 && (int)TREE_INT_CST_LOW(TYPE_SIZE(type)) == 8) {
      StructElements[0] = UByteTy;
      ElementOffsets[0] = 0;
      ++Idx;
    }

    /* End of the hack, set the real number of elements. */
    Result->NumElements = Idx;

    Idx = 0; Size = 0;

    /* Fill in the fields of the structure type. */
    for (Idx = 0; Idx != Result->NumElements; ++Idx) {
      Result->Elements[Idx] = StructElements[Idx];
      Result->x.Struct.MemberOffsets[Idx] = ElementOffsets[Idx];
    }

    Field = TYPE_FIELDS(type);
    if (Field && TREE_CODE(Field) != FIELD_DECL)
      Field = GetNextFieldDecl(Field);

#if DEBUG_STRUCT_LAYOUT
    fprintf(stderr, "Setting field indexes to: { ");
#endif
    
    for (; Field; Field = GetNextFieldDecl(Field)) {
      unsigned FieldByteOffset = GetFieldOffset(Field)/8;
      for (Idx = 0; Idx+1 < Result->NumElements &&
             ElementOffsets[Idx+1] <= FieldByteOffset; ++Idx)
        /*empty*/;
#if DEBUG_STRUCT_LAYOUT
      fprintf(stderr, "%d, ", Idx);
#endif
      SET_DECL_LLVM(Field, llvm_constant_new_integral(UByteTy, Idx));
    }

#if DEBUG_STRUCT_LAYOUT
    fprintf(stderr, "}\nFINISHED TYPE: ");
    llvm_type_print_struct_expand(Result, stderr);
    fprintf(stderr, "  SIZE=%d ALIGN=%d\n\n",
            (int)TREE_INT_CST_LOW(TYPE_SIZE(type))/8,
            (int)TYPE_ALIGN(type)/8);
#endif
    return ((*HTEP)->LLVMTy = llvm_type_get_cannonical_version(Result));
  }
  case VOID_TYPE:        return VoidTy;
  case BOOLEAN_TYPE:     return BoolTy;

  case ENUMERAL_TYPE:    /* Treat the same as integral type, but round up */
  case INTEGER_TYPE: {
    unsigned Size = TYPE_PRECISION(type);
    if (Size == 0)
      Size = TREE_INT_CST_LOW(TYPE_SIZE(type));

    if (TREE_CODE(type) == ENUMERAL_TYPE) {
      /* Round enumeration size to a specified type */
      if (Size > 0 && Size < 8) Size = 8;
      if (Size > 8 && Size < 16) Size = 16;
      if (Size > 16 && Size < 32) Size = 32;
      if (Size > 32 && Size < 64) Size = 64;
    }

    return llvm_type_get_integer(Size, TREE_UNSIGNED(type));
  }
  case REAL_TYPE:
    switch(TYPE_PRECISION(type)) {
    case 32: return FloatTy;

    case 96:  /* Map long doubles to doubles */
    case 128: /* Map long doubles to doubles */
    case 64: return DoubleTy;
    default: 
      fprintf(stderr, "UNKNOWN FLOATING POINT TYPE SIZE: %d\n", 
              TYPE_PRECISION(type));
      abort();
    }
    break;
  case COMPLEX_TYPE: {
    llvm_type *ElTy = llvm_type_get_from_tree(TREE_TYPE(type));
    Result = llvm_type_create_struct(2, 2*llvm_type_get_size(ElTy));
    Result->x.Struct.MemberOffsets[0] = 0;
    Result->x.Struct.MemberOffsets[1] = llvm_type_get_size(ElTy);
    Result->Elements[0] = Result->Elements[1] = ElTy;

    if (TYPE_NAME(type))  /* Set the name of the structure. */
      if (TREE_CODE(TYPE_NAME(type)) == IDENTIFIER_NODE)
        Result->x.Struct.TypeName =xstrdup(IDENTIFIER_POINTER(TYPE_NAME(type)));
      else 
        Result->x.Struct.TypeName =
          xstrdup(IDENTIFIER_POINTER(DECL_NAME(TYPE_NAME(type))));
    else
      Result->x.Struct.TypeName = 0;

    return llvm_type_get_cannonical_version(Result);
  }
  default:
    printf("<Unknown Type %d>", TREE_CODE(type));
    debug_tree(type);
    break;
  }
  abort();
}
