/* The main tree to LLVM conversion interface
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
#include "cpplib.h"
#include "target.h"
#include "debug.h"
#include "timevar.h"
#include "c-common.h"
#include "c-pragma.h"
#include "cgraph.h"

#include "diagnostic.h"
#include "llvm-internals.h"
#include <assert.h>

extern const char *asm_file_name;
FILE *llvm_out_file;

void print_version(FILE *, const char *);
void print_switch_values(FILE *, int, int, const char *,
                         const char *, const char *);

void llvm_init_codegen() {
  flag_inline_functions = 0;
  flag_really_no_inline = 1;
  warn_inline = 0;

  llvm_InitializeProgram();
  llvm_InitializeTypeSystem();
  llvm_InitializeConstants();
}


/* Open assembly code output file.  Do this even if -fsyntax-only is
   on, because then the driver will have provided the name of a
   temporary file or bit bucket for us.  NAME is the file specified on
   the command line, possibly NULL.  */
void llvm_init_asm_output(const char *name) {
  if (name == NULL && asm_file_name == 0)
    llvm_out_file = stdout;
  else
    {
      if (asm_file_name == 0)
	{
	  int len = strlen (dump_base_name);
	  char *dumpname = (char *) xmalloc (len + 6);
	  memcpy (dumpname, dump_base_name, len + 1);
	  strip_off_ending (dumpname, len);
	  strcat (dumpname, ".s");
	  asm_file_name = dumpname;
	}
      if (!strcmp (asm_file_name, "-"))
	llvm_out_file = stdout;
      else
	llvm_out_file = fopen (asm_file_name, "w+");
      if (llvm_out_file == 0)
	fatal_error ("can't open %s for writing: %m", asm_file_name);
    }

#ifdef IO_BUFFER_SIZE
  setvbuf (llvm_out_file, (char *) xmalloc (IO_BUFFER_SIZE),
	   _IOFBF, IO_BUFFER_SIZE);
#endif

  if (!flag_syntax_only)
    {
      /* Print the list of options in effect.  */
      print_version (llvm_out_file, ";");
      print_switch_values (llvm_out_file, 0, 75, ";", " ", "\n");
      
      /* Add a blank line here so it appears in assembler output but not
	 screen output.  */
      fprintf (llvm_out_file, "\n");

      fprintf(llvm_out_file, "target pointersize = %d\n", POINTER_SIZE);
      fprintf(llvm_out_file, "target endian = %s\n",
              (BYTES_BIG_ENDIAN) ? "big" : "little");
    }
}



/* llvm_c_expand_body_1 - Corresponds to c_expand_body_1 */
static void llvm_c_expand_body_1(tree fndecl, int nested_p) {
  struct llvm_function *Func;
  if (errorcount) return;
  timevar_push (TV_LLVM_EXPAND);

  assert(nested_p == 0 && "Does not handle nested functions yet!");

  current_function_decl = fndecl;
  input_location = DECL_SOURCE_LOCATION (fndecl);

  /* Warn if this value is an aggregate type,
     regardless of which calling convention we are using for it.  */
  if (warn_aggregate_return
      && AGGREGATE_TYPE_P (TREE_TYPE (DECL_RESULT (fndecl))))
    warning ("function returns an aggregate");


  /* Even though we're inside a function body, we still don't want to
     call expand_expr to calculate the size of a variable-sized array.
     We haven't necessarily assigned RTL to all variables yet, so it's
     not safe to try to expand expressions involving them.  */
  immediate_size_expand = 0;

  /* Initialize the function, adding arguments to the function as
     appropriate.  Set up parameters and prepare for return, for the
     function.  */
  Func = llvm_expand_function_start (fndecl, 0);

  /* If this function is `main', emit a call to `__main'
     to run global initializers, etc.  */
  if (DECL_NAME (fndecl)
      && MAIN_NAME_P (DECL_NAME (fndecl))
      && C_DECL_FILE_SCOPE (fndecl))
    llvm_expand_main_function (Func);

  /* Generate LLVM for this function body.  */
  llvm_expand_stmt (Func, DECL_SAVED_TREE (fndecl));

  assert(lang_expand_function_end == 0 &&"Cannot handle lang spec expansion!");

  /* Generate LLVM for function exit.  */
  llvm_expand_function_end(Func, fndecl, 0);
  
  /* Output LLVM code for debugging the compiler */
  if (EMIT_CODE_INCREMENTALLY) llvm_function_print(Func, llvm_out_file);

  /* With just -Wextra, complain only if function returns both with
     and without a value.  */
#if 0 /* FIXME */
  if (extra_warnings
      && current_function_returns_value
      && current_function_returns_null)
    warning ("this function may return with or without a value");
#endif
  /* If requested, warn about function definitions where the function will
     return a value (usually of some struct or union type) which itself will
     take up a lot of stack space.  */

  if (warn_larger_than && !DECL_EXTERNAL (fndecl) && TREE_TYPE (fndecl))
    {
      tree ret_type = TREE_TYPE (TREE_TYPE (fndecl));

      if (ret_type && TYPE_SIZE_UNIT (ret_type)
	  && TREE_CODE (TYPE_SIZE_UNIT (ret_type)) == INTEGER_CST
	  && 0 < compare_tree_int (TYPE_SIZE_UNIT (ret_type),
				   larger_than_size))
	{
          const location_t *locus = &DECL_SOURCE_LOCATION (fndecl);
	  unsigned int size_as_int
	    = TREE_INT_CST_LOW (TYPE_SIZE_UNIT (ret_type));

	  if (compare_tree_int (TYPE_SIZE_UNIT (ret_type), size_as_int) == 0)
	    warning ("%Hsize of return value of '%D' is %u bytes",
                     locus, fndecl, size_as_int);
	  else
	    warning ("%Hsize of return value of '%D' is larger than %wd bytes",
                     locus, fndecl, larger_than_size);
	}
    }

  if (DECL_SAVED_INSNS (fndecl) == 0 && ! nested_p
      && ! flag_inline_trees)
    {
      /* Stop pointing to the local nodes about to be freed.
	 But DECL_INITIAL must remain nonzero so we know this
	 was an actual function definition.
	 For a nested function, this is done in c_pop_function_context.
	 If rest_of_compilation set this to 0, leave it 0.  */
      if (DECL_INITIAL (fndecl) != 0)
	DECL_INITIAL (fndecl) = error_mark_node;

      DECL_ARGUMENTS (fndecl) = 0;
    }

  if (DECL_STATIC_CONSTRUCTOR (fndecl))
    llvm_emit_global_ctor_dtor(1, fndecl, DEFAULT_INIT_PRIORITY);

  if (DECL_STATIC_DESTRUCTOR (fndecl))
    llvm_emit_global_ctor_dtor(0, fndecl, DEFAULT_INIT_PRIORITY);

  timevar_pop (TV_LLVM_EXPAND);
}

/* llvm_c_expand_body - Expand the specified function into LLVM,
   corresponds to c_expand_body */
void llvm_c_expand_body(tree Fn) {
  llvm_c_expand_body_1(Fn, 0);
}

/* This horrible code mirrors code found in varasm.c:assemble_name.  It
   basically marks all external names that are used by the program as
   REFERENCED, which, if the name corresponds to an inline function, causes the
   inline function to be code generated for this translation unit. */
void MarkNameAsUsed(const char *Name) {
  tree id = maybe_get_identifier(Name);
  if (id) TREE_SYMBOL_REFERENCED(id) = 1;
}


void llvm_emit_final_program(const char *version) {
  if (EMIT_CODE_INCREMENTALLY)
    fprintf(llvm_out_file, "*** EMIT_CODE_INCREMENTALLY defined\n");
  else
    llvm_program_print(llvm_out_file);
  fprintf(llvm_out_file, ";; Created by \"GCC: (GNU) %s\"\n", version);
  fclose(llvm_out_file);

  if (errorcount)
    unlink(asm_file_name);
  
}
