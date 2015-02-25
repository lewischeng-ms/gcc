/* Functions related to building and playing with classes.
   Copyright (C) 1987 Free Software Foundation, Inc.
   Contributed by Michael Tiemann (tiemann@mcc.com)

   This file is part of GNU CC.
   
   GNU CC is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY.  No author or distributor
   accepts responsibility to anyone for the consequences of using it
   or for whether it serves any particular purpose or works at all,
   unless he says so in writing.  Refer to the GNU CC General Public
   License for full details.
   
   Everyone is granted permission to copy, modify and redistribute
   GNU CC, but only under the conditions described in the
   GNU CC General Public License.   A copy of this license is
   supposed to have been given to you along with GNU CC so you
   can know your rights and responsibilities.  It should be in a
   file named COPYING.  Among other things, the copyright notice
   and this notice must be preserved on all copies.  */


/* High-level class interface. */

#include "config.h"
#include "tree.h"
#include "c-tree.h"
#include "overload.h"
#include "flags.h"
#include "rtl.h"

#define NULL 0
#define MIN(X,Y) ((X) < (Y) ? (X) : (Y))
#define MAX(X,Y) ((X) > (Y) ? (X) : (Y))

/* in decl.c.  */
extern tree lookup_tag_current_binding_level ();

/* in method.c.  */
extern void do_inline_method_hair ();

/* Way of stacking class names */
static tree *current_class_base, *current_class_stack;
static int current_class_size;

tree current_class_decl, C_C_D;	/* PARM_DECL: the class instance variable */
tree current_vtable_decl;

/* The following two can be derived from the previous one */
tree current_class_name;	/* IDENTIFIER_NODE: name of current class */
tree current_class_type;	/* _TYPE: the type of the current class */

#if 0
/* Make sure that the tag NAME is defined *in the current binding level*
   at least as a forward reference.
   CODE says which kind of tag NAME ought to be.

   Not used for C++.  Not maintained.  */

tree
start_struct (code, name)
     enum tree_code code;
     tree name;
{
  /* If there is already a tag defined at this binding level
     (as a forward reference), just return it.  */
  register tree ref = 0;

  if (name != 0)
    ref = lookup_tag (code, name, current_binding_level, 1);
  if (ref && TREE_CODE (ref) == code)
    {
      if (TYPE_FIELDS (ref))
	error ((code == UNION_TYPE ? "redefinition of `union %s'"
		: "redefinition of `struct %s'"),
	       IDENTIFIER_POINTER (name));

      return ref;
    }

  /* Otherwise create a forward-reference just so the tag is in scope.  */

  ref = make_node (code);
  /* Must re-synch this with xref_tag if you are going to use it.  */
  abort ();
  pushtag (name, ref);
  return ref;
}
#endif

/* Create a RECORD_TYPE or UNION_TYPE node for a C struct or union declaration
   (or C++ class declaration).

   For C++, we must handle the building of derived classes.
   Also, C++ allows static class members.  The way that this is
   handled is to keep the field name where it is (as the DECL_NAME
   of the field), and place the overloaded decl in the DECL_OFFSET
   of the field.  layout_record and layout_union will know about this.

   More C++ hair: inline functions have text in their DECL_INITIAL nodes
   which must somehow be parsed into meaningful tree structure.  After the
   struct has been laid out, set things up so that this can happen.

   And still more: virtual functions.  The DECL_VINDEX field for the
   FIELD_DECL nodes contains the offset for the FUNCTION_DECL in the
   virtual function table.  The DECL_OFFSET field for the struct
   being built contains the total size of the table for the struct,
   so that classes being derived from this struct will know where
   their table can start.  The DECL_VOFFSET field for the struct
   contains the list of virtual functions, for initialization
   purposes.  Note that many things can derive from a base class,
   but that the virtual function table must be "flat",  i.e., we
   cannot use a link to base class as we can for normal functions.
   As a result, any new virtual which are added to the virtual function
   table must be added without changing the tail of the original list.
   We therefore use copy_list and work on the copy.

   LIST_OF_FIELDLISTS is just that.  The elements of the list are
   TREE_LIST elements, whose TREE_PURPOSE field tells what visibility
   the list has, and the TREE_VALUE slot gives the actual fields.

   EMPTY is non-zero if this structure has no declarations following it.  */

tree
finish_struct (t, list_of_fieldlists, empty)
     tree t;
     tree list_of_fieldlists;
     int empty;
{
  tree head;
  int old;
  int round_up_size = 1;

  enum tree_code code = TREE_TYPE (t) == class_type_node ? CLASS_TYPE : TREE_CODE (t);
  register tree x, y, tail;
  int needs_ctor = 0, needs_dtor = 0, needs_wrapper = 0;
  tree name = DECL_NAME (TYPE_NAME (t)), fields, fn_fields;
  enum visibility_type visibility;
  int all_virtual;
  int has_virtual = 0;
  tree pending_virtuals = NULL_TREE;
  tree vfield = NULL_TREE;
  int any_base_virtual_p = 0, i;
  int any_assigns_this = 0;

  /* If this was a CLASS_TYPE thing, get to the RECORD_TYPE variant.  */
  t = TYPE_MAIN_VARIANT (t);

  if (TREE_HAS_DESTRUCTOR (t) & ! TREE_HAS_CONSTRUCTOR (t))
    {
      error ("`%s' has destructor but no constructors",
	     IDENTIFIER_POINTER (name));
      TREE_HAS_DESTRUCTOR (t) = 0;
    }

  if (TYPE_FIELDS (t))
    {
      error ((TREE_CODE (t) == UNION_TYPE ? "redefinition of `union %s'"
	      : "redefinition of `struct %s'"),
	     IDENTIFIER_POINTER (name));
      popclass (0);
      return t;
    }

  all_virtual = flag_all_virtual
    && (TREE_HAS_METHOD_CALL_OVERLOADED (t) || TREE_NEEDS_WRAPPER (t));

  /* If this type was previously laid out as a forward reference,
     make sure we lay it out again.  */

  TYPE_SIZE (t) = 0;

  old = suspend_momentary ();

  /* Install struct as DECL_CONTEXT of each field decl.
     Also process specified field sizes.
     Set DECL_SIZE_UNIT to the specified size, or 0 if none specified.
     The specified size is found in the DECL_INITIAL.
     Store 0 there, except for ": 0" fields (so we can find them
     and delete them, below).  */

  for (i = 1; i <= CLASSTYPE_N_BASECLASSES (t); i++)
    {
      tree basetype = CLASSTYPE_BASECLASS (t, i);

      /* If the type of basetype is incomplete, then
	 we already complained about that fact.  */
      if (TYPE_SIZE (basetype))
	{
	  has_virtual += TREE_INT_CST_LOW ((tree)TYPE_VSIZE (basetype));
	  needs_ctor |= TREE_NEEDS_CONSTRUCTOR (basetype);
	  needs_dtor |= TREE_NEEDS_DESTRUCTOR (basetype);
	  needs_wrapper |= TREE_NEEDS_WRAPPER (basetype);
	  any_assigns_this |= TREE_ANY_ASSIGNS_THIS (basetype);

	  TREE_HAS_CALL_OVERLOADED (t) |= TREE_HAS_CALL_OVERLOADED (basetype);
	  TREE_HAS_ARRAY_REF_OVERLOADED (t) |= TREE_HAS_ARRAY_REF_OVERLOADED (basetype);
	}
      else
	{
	  int j;

	  /* The base type is of incomplete type.  It is
	     probably best to pretend that it does not
	     exist.  */
	  error ("base class `%s' has incomplete type", TYPE_NAME_STRING (basetype));
	  if (i == CLASSTYPE_N_BASECLASSES (t))
	    CLASSTYPE_BASECLASS (t, i) = NULL_TREE;
	  CLASSTYPE_N_BASECLASSES (t) -= 1;
	  for (j = i; j < CLASSTYPE_N_BASECLASSES (t); j++)
	    CLASSTYPE_BASECLASS (t, j) = CLASSTYPE_BASECLASS (t, j+1);
	  continue;
	}
    }

  fields = NULL_TREE;
  fn_fields = NULL_TREE;
  tail = NULL_TREE;
  y = NULL_TREE;

  if (list_of_fieldlists)
    {
      if (TREE_PURPOSE (list_of_fieldlists) == (tree)visibility_default)
	TREE_PURPOSE (list_of_fieldlists) =
	  (tree)(code == CLASS_TYPE ? visibility_private : visibility_public);

      while (list_of_fieldlists)
	{
	  visibility = (enum visibility_type)TREE_PURPOSE (list_of_fieldlists);

	  for (x = TREE_VALUE (list_of_fieldlists); x; x = TREE_CHAIN (x))
	    {
	      TREE_PRIVATE (x) = visibility == visibility_private;
	      TREE_PROTECTED (x) = visibility == visibility_protected;
	      if (TREE_CODE (TREE_TYPE (x)) == FUNCTION_DECL)
		{
		  /* The name of the field is the original field name
		     Save this in auxilliary field for later overloading */
		  if (TREE_VIRTUAL (x)
		      || (all_virtual && DECL_NAME (x) != name))
		    {
		      if (DECL_VINDEX (x))
			{
			  /* This definition supersedes one from base class.  */
			}
		      else
			{
#ifdef VTABLE_USES_MASK
			  SET_DECL_VINDEX (x, build_int_2 (has_virtual++, 0));
#else
			  SET_DECL_VINDEX (x, build_int_2 (((1 << (BITS_PER_WORD - 1)) | has_virtual++), -1));
#endif
			}
		      pending_virtuals = tree_cons (DECL_VINDEX (x), TREE_TYPE (x),
						    pending_virtuals);
		    }
		  if (y) TREE_CHAIN (y) = TREE_CHAIN (x);
		  if (! fn_fields) fn_fields = x;
		  else TREE_CHAIN (tail) = x;
		  tail = x;
		  DECL_CONTEXT (x) = t;
		  DECL_SIZE_UNIT (x) = 0;
		  continue;
		}

	      /* When this goes into scope, it will be a non-local reference.  */
	      TREE_NONLOCAL (x) = 1;

	      /* If any field is const, the structure type is pseudo-const.  */
	      if (TREE_READONLY (x))
		C_TYPE_FIELDS_READONLY (t) = 1;
	      else
		{
		  /* A field that is pseudo-const makes the structure likewise.  */
		  tree t1 = TREE_TYPE (x);
		  while (TREE_CODE (t1) == ARRAY_TYPE)
		    t1 = TREE_TYPE (t1);
		  if ((TREE_CODE (t1) == RECORD_TYPE || TREE_CODE (t1) == UNION_TYPE)
		      && C_TYPE_FIELDS_READONLY (t1))
		    C_TYPE_FIELDS_READONLY (t) = 1;
		}

	      if (DECL_NAME (x) && TREE_CODE (DECL_NAME (x)) == SCOPE_REF)
		{
		  tree type = TREE_OPERAND (DECL_NAME (x), 0);
		  tree fdecl = TREE_OPERAND (DECL_NAME (x), 1);
		  tree elem;

		  /* Make type T see field decl FDECL with
		     the visibility VISIBILITY.  */
		  if (y) TREE_CHAIN (y) = TREE_CHAIN (x);
		  if (TREE_CODE (fdecl) == TREE_LIST)
		    {
		      fdecl = TREE_VALUE (fdecl);
		      while (fdecl)
			{
			  elem = purpose_member (t, DECL_VISIBILITY (fdecl));
			  if (elem && TREE_VALUE (elem) != (tree)visibility)
			    {
			      error_with_decl (TREE_TYPE (fdecl), "conflicting visibility specifications for method `%s', ignored");
			    }
			  else if (elem == NULL_TREE)
			    DECL_VISIBILITY (fdecl) = tree_cons (t, visibility,
								 DECL_VISIBILITY (fdecl));
			  fdecl = TREE_CHAIN (fdecl);
			}
		    }
		  else
		    {
		      elem = purpose_member (t, DECL_VISIBILITY (fdecl));
		      if (elem && TREE_VALUE (elem) != (tree)visibility)
			{
			  if (TREE_CODE (TREE_TYPE (fdecl)) == FUNCTION_DECL)
			    {
			      error_with_decl (TREE_TYPE (fdecl), "conflicting visibility specifications for method `%s', ignored");
			    }
			  else error ("conflicting visibility specifications for field `%s', ignored", IDENTIFIER_POINTER (DECL_NAME (fdecl)));
			}
		      else
			DECL_VISIBILITY (fdecl) = tree_cons (t, visibility,
							     DECL_VISIBILITY (fdecl));
		    }
		  continue;
		}
	      if (! fields) fields = x;
	      DECL_CONTEXT (x) = t;
	      DECL_SIZE_UNIT (x) = 0;

	      if (TREE_PACKED (x))
		{
		  /* Invalid bit-field size done by grokfield.  */
		  /* Detect invalid bit-field type.  */
		  if (DECL_INITIAL (x)
		      && TREE_CODE (TREE_TYPE (x)) != INTEGER_TYPE
		      && TREE_CODE (TREE_TYPE (x)) != ENUMERAL_TYPE)
		    {
		      error_with_decl (x, "bit-field `%s' has invalid type");
		      DECL_INITIAL (x) = NULL;
		    }
		  if (DECL_INITIAL (x) && pedantic
		      && TREE_TYPE (x) != integer_type_node
		      && TREE_TYPE (x) != unsigned_type_node)
		    warning_with_decl (x, "bit-field `%s' type invalid in ANSI C");

		  /* Detect and ignore out of range field width.  */
		  if (DECL_INITIAL (x))
		    {
		      register int width = TREE_INT_CST_LOW (DECL_INITIAL (x));

		      if (width < 0)
			{
			  DECL_INITIAL (x) = NULL;
			  warning_with_decl (x, "negative width in bit-field `%s'");
			}
		      else if (width > TYPE_PRECISION (TREE_TYPE (x)))
			{
			  DECL_INITIAL (x) = NULL;
			  warning_with_decl (x, "width of `%s' exceeds its type");
			}
		    }

		  /* Process valid field width.  */
		  if (DECL_INITIAL (x))
		    {
		      register int width = TREE_INT_CST_LOW (DECL_INITIAL (x));

		      if (width == 0)
			{
			  /* field size 0 => mark following field as "aligned" */
			  if (TREE_CHAIN (x))
			    DECL_ALIGN (TREE_CHAIN (x))
			      = MAX (DECL_ALIGN (TREE_CHAIN (x)), EMPTY_FIELD_BOUNDARY);
			  /* field of size 0 at the end => round up the size.  */
			  else
			    round_up_size = EMPTY_FIELD_BOUNDARY;
			}
		      else
			{
			  DECL_INITIAL (x) = NULL;
			  DECL_SIZE_UNIT (x) = width;
			  TREE_PACKED (x) = 1;
			  /* Traditionally a bit field is unsigned
			     even if declared signed.  */
			  if (flag_traditional
			      && TREE_CODE (TREE_TYPE (x)) == INTEGER_TYPE)
			    TREE_TYPE (x) = unsigned_type_node;
			}
		    }
		  else
		    /* Non-bit-fields are aligned for their type.  */
		    DECL_ALIGN (x) = MAX (DECL_ALIGN (x), TYPE_ALIGN (TREE_TYPE (x)));
		}
	      else if (IS_AGGR_TYPE (TREE_TYPE (x))
		       || (TREE_CODE (TREE_TYPE (x)) == ARRAY_TYPE
			   && IS_AGGR_TYPE (TREE_TYPE (TREE_TYPE (x)))))
		{
		  tree type = TREE_TYPE (x);
		  if (TREE_CODE (type) == ARRAY_TYPE)
		    type = TREE_TYPE (type);

		  if (code == UNION_TYPE)
		    {
		      if (TREE_NEEDS_CONSTRUCTOR (type))
			error ("member %s::%s with constructor not allowed in union",
			       IDENTIFIER_POINTER (name), IDENTIFIER_POINTER (DECL_NAME (x)));
		      if (TREE_NEEDS_DESTRUCTOR (type))
			error ("member %s::%s with destructor (also) not allowed in union",
			       IDENTIFIER_POINTER (name), IDENTIFIER_POINTER (DECL_NAME (x)));
		    }
		  else
		    {
		      needs_ctor |= TREE_NEEDS_CONSTRUCTOR (type);
		      needs_dtor |= TREE_NEEDS_DESTRUCTOR (type);
		      needs_wrapper |= TREE_NEEDS_WRAPPER (type);
		    }
		}
	      y = x;
	    }
	  list_of_fieldlists = TREE_CHAIN (list_of_fieldlists);
	  /* link the tail while we have it! */
	  if (y)
	    TREE_CHAIN (y) = list_of_fieldlists ? TREE_VALUE (list_of_fieldlists) : NULL_TREE;
	}
    }

  if (tail) TREE_CHAIN (tail) = NULL_TREE;

  for (i = CLASSTYPE_N_BASECLASSES (t); i > 0; i--)
    if (TREE_VIRTUAL (CLASSTYPE_BASECLASS (t, i)))
      {
	any_base_virtual_p = 1;
	break;
      }

  if (pending_virtuals)
    {
      tree vsize = NULL_TREE;
      tree atype = NULL_TREE;
      tree decl, init;

      pending_virtuals = nreverse (pending_virtuals);
      /* We must enter these virtuals into the table.  */
      if (! any_base_virtual_p)
	{
	  /* We must create a pointer to this table because
	     the one inherited from base class does not exist.
	     We will fill in the type when we know what it
	     should really be.  */
	  vsize = build_int_2 (has_virtual - 1, 0);
	  atype = build_array_type (ptr_type_node, make_index_type (vsize));
	  layout_type (atype);
	  vfield = build_decl (FIELD_DECL, get_vfield_name (t),
			       build_pointer_type (atype));
	  DECL_CONTEXT (vfield) = t;
	  DECL_SIZE_UNIT (vfield) = 0;
	  if (y)
	    {
	      if (TREE_CHAIN (t)) abort ();
	      TREE_CHAIN (y) = vfield;
	      y = vfield;
	    }
	  else fields = vfield;
	}
      else
	{
	  /* Now, some of the new virtuals may supersede some of the old...
	     HEAD and TAIL are the ends of the new list for the vtbl.
	     TMP is a pointer iterating across old vtbl elements.
	     T is a pointer iterating across new vtbl elements.
	     PREV allows T to be unlinked from new vtbl elements.  */
	  tree head = NULL_TREE, tail = NULL_TREE, tmp;
	  int base_vsize = 0;

	  vfield = lookup_field (t, get_vfield_name (t), 0);
	  if (vfield == NULL_TREE) abort ();

	  for (i = CLASSTYPE_N_BASECLASSES (t); i > 0; i--)
	    {
	      tree basetype = CLASSTYPE_BASECLASS (t, i);

	      tmp = TYPE_VIRTUALS (basetype);
	      while (tmp)
		{
		  tree t = pending_virtuals;
		  tree prev = NULL_TREE;
		  while (t)
		    {
		      if (TREE_PURPOSE (tmp) == TREE_PURPOSE (t))
			{
			  if (tail)
			    {
			      TREE_CHAIN (tail) = t;
			      tail = t;
			    }
			  else
			    {
			      head = t;
			      tail = t;
			    }
			  if (prev)
			    TREE_CHAIN (prev) = TREE_CHAIN (t);
			  else
			    pending_virtuals = TREE_CHAIN (t);
			  TREE_CHAIN (t) = NULL_TREE;
			  goto next;
			}
		      prev = t;
		      t = TREE_CHAIN (t);
		    }
		  if (tail)
		    {
		      TREE_CHAIN (tail) = copy_node (tmp);
		      tail = TREE_CHAIN (tail);
		    }
		  else
		    {
		      head = copy_node (tmp);
		      tail = head;
		    }
		next:
		  tmp = TREE_CHAIN (tmp);
		}
	    }
	  if (!tail) abort ();	/* @@ */
	  TREE_CHAIN (tail) = pending_virtuals;
	  pending_virtuals = head;
	  atype = TREE_TYPE (TREE_TYPE (vfield));

	  for (i = CLASSTYPE_N_BASECLASSES (t); i > 0; i--)
	    base_vsize += TYPE_VSIZE (CLASSTYPE_BASECLASS (t, i));

	  if (has_virtual != base_vsize)
	    {
	      /* We must extend (or create) the boundaries on this array.  */
	      vsize = build_int_2 (has_virtual - 1);
	      atype = build_array_type (ptr_type_node, make_index_type (vsize));
	      layout_type (atype);
	      /* Don't like overwriting this, but there isn't much choice
		 unless we want to do a lot of copying.  Skip lists
		 would come in real handy here.  */
	      TREE_TYPE (vfield) = build_pointer_type (atype);
	    }
	}
      decl = get_vtable_name (t);
      IDENTIFIER_GLOBAL_VALUE (decl) = pushdecl_top_level (build_decl (VAR_DECL, decl, atype));
      decl = IDENTIFIER_GLOBAL_VALUE (decl);
      TREE_STATIC (decl) = 1;
      /* We do not make this definition "PUBLIC".  */
      init = build_nt (CONSTRUCTOR, NULL_TREE, pending_virtuals);
      /* Declare and initialize virtual function table.  */
      DECL_INITIAL (decl) = init;
      TREE_VIRTUAL (decl) = 1;
      finish_decl (decl, init, NULL_TREE);
      /* Remember which class this vtable is really for.  */
      DECL_VPARENT (decl) = t;
    }
  else if (any_base_virtual_p)
    {
      tree decl, init;
      tree basetype;
      /* This class contributes nothing the the virtual function
	 machinery.  However, it must be able to point its
	 vtbl_ptr somewhere.  We create a declaration which is
	 the same as the one from the base class.  In fact,
	 it is the one from the (leftmost) base class.  */

      decl = get_vtable_name (t);
      for (i = 1; i <= CLASSTYPE_N_BASECLASSES (t); i++)
	if (TREE_VIRTUAL (CLASSTYPE_BASECLASS (t, i)))
	  break;
      basetype = CLASSTYPE_BASECLASS (t, i);
      init = get_vtable_name (basetype);
      IDENTIFIER_GLOBAL_VALUE (decl) = IDENTIFIER_GLOBAL_VALUE (init);
      pending_virtuals = TYPE_VIRTUALS (basetype);
      vfield = lookup_field (basetype, get_vfield_name (basetype), 0);
      if (vfield == NULL_TREE) abort ();
    }

  if (fields == 0 && pedantic)
    warning ((code == UNION_TYPE ? "union has no members"
	      : "structure has no members"));

  /* Now DECL_INITIAL is null on all members except for zero-width bit-fields.
     And they have already done their work.

     C++: maybe we will support default field initialization some day...  */

  /* Delete all zero-width bit-fields from the front of the fieldlist */
  while (fields && TREE_PACKED (fields)
	 && DECL_INITIAL (fields))
    fields = TREE_CHAIN (fields);
  /* Delete all such fields from the rest of the fields.  */
  for (x = fields; x;)
    {
      if (TREE_CHAIN (x) && TREE_PACKED (TREE_CHAIN (x))
	  && DECL_INITIAL (TREE_CHAIN (x)))
	TREE_CHAIN (x) = TREE_CHAIN (TREE_CHAIN (x));
      else x = TREE_CHAIN (x);
    }
  /* Delete all duplicate fields from the fields */
  for (x = fields; x && TREE_CHAIN (x); y = x)
    /* Anonymous fields aren't duplicates.  */
    if (DECL_NAME (TREE_CHAIN (x)) == 0)
      x = TREE_CHAIN (x);
    else
      {
	register tree y = fields;
	while (1)
	  {
	    if (DECL_NAME (y) == DECL_NAME (TREE_CHAIN (x)))
	      break;
	    if (y == x)
	      break;
	    y = TREE_CHAIN (y);
	  }
	if (DECL_NAME (y) == DECL_NAME (TREE_CHAIN (x)))
	  {
	    error_with_decl (TREE_CHAIN (x), "duplicate member `%s'");
	    TREE_CHAIN (x) = TREE_CHAIN (TREE_CHAIN (x));
	  }
	else x = TREE_CHAIN (x);
      }

  /* Now we have the final fieldlist for the data fields.  Record it,
     then lay out the structure or union (including the fields).  */

  TYPE_FIELDS (t) = fields;

  /* If there's a :0 field at the end, round the size to the
     EMPTY_FIELD_BOUNDARY.  */
  TYPE_ALIGN (t) = round_up_size;

  /* Warn about duplicate methods in fn_fields.  Also compact
     method lists so that lookup can be made faster.

     Algorithm:  Outer loop builds lists by method name.
     Inner loop checks for redundant method names within a list.

     Data Structure:  List of method lists.  The outer list
     is a TREE_LIST, whose TREE_PURPOSE field is the field name
     and the TREE_VALUE is the TREE_CHAIN of the FIELD_DECLs.
     Friends are chained in the same way as member functions, but
     they live in the TREE_TYPE field of the outer list.
     That allows them to be quicky deleted, and requires
     no extra storage.

     If there are any constructors/destructors, they are moved to
     the front of the list.  This makes pushclass more efficient.

     We also link each field which has shares a name with its
     baseclass to the head of the list of fields for that base class.
     This allows us to reduce search time in places like `build_classfn_ref'
     to consider only reasonably likely functions.  */

  head = NULL_TREE;
  tail = NULL_TREE;
  while (fn_fields)
    {
      /* NEXT Pointer, TEST Pointer, and BASE Pointer.  */
      tree nextp, testp, basep;

      nextp = TREE_CHAIN (fn_fields);
      TREE_CHAIN (fn_fields) = NULL_TREE;
      testp = head;
      while (testp && TREE_PURPOSE (testp) != DECL_NAME (fn_fields))
	testp = TREE_CHAIN (testp);
      if (testp)
	{
	  for (x = TREE_VALUE (testp), basep = x ? DECL_BASELINK (x) : 0; x;)
	    {
	      if (DECL_NAME (TREE_TYPE (fn_fields)) == DECL_NAME (TREE_TYPE (x)))
		{
		  char buf[OVERLOAD_MAX_LEN];
		  /* We complain about multiple destructors on sight,
		     so we do not repeat the warning here.  */
		  if (! DESTRUCTOR_NAME_P (DECL_NAME (TREE_TYPE (fn_fields))))
		    {
		      hack_function_decl (buf, t, TREE_TYPE (fn_fields), 1);
		      yylineerror (DECL_SOURCE_LINE (fn_fields),
				   "ambiguous method `%s' in structure", buf);
		    }
		  break;
		}
	      y = x;
	      x = TREE_CHAIN (x);
	    }
	  if (TREE_CODE (fn_fields) == FRIEND_DECL)
	    {
	      for (x = TREE_TYPE (testp); x;)
		{
		  if (DECL_NAME (TREE_TYPE (fn_fields)) == DECL_NAME (TREE_TYPE (x)))
		    {
		      char buf[OVERLOAD_MAX_LEN];
		      hack_function_decl (buf, t, TREE_TYPE (fn_fields), 1);
		      yylineerror (DECL_SOURCE_LINE (fn_fields),
				   "friend `%s' is ambiguous in structure", buf);
		      break;
		    }
		  y = x;
		  x = TREE_CHAIN (x);
		}
	      if (x == 0)
		{
		  if (y)
		    TREE_CHAIN (y) = fn_fields;
		  else
		    TREE_TYPE (testp) = fn_fields;
		  x = (tree)1;
		}
	    }
	  if (x == 0)
	    {
	      if (TREE_VALUE (testp))
		TREE_CHAIN (y) = fn_fields;
	      else
		TREE_VALUE (testp) = fn_fields;
	      /* Following statement harmless for FRIEND_DECL.  */
	      SET_DECL_BASELINK (fn_fields, basep);
	    }
	}
      else
	{
	  /* Constrcutors are handled easily in search routines.
	     Besides, we know we wont find any, so do not bother looking.  */
	  if (CLASSTYPE_N_BASECLASSES (t) > 0 && DECL_NAME (fn_fields) != name)
	    switch (get_n_fnfield_sources (t, DECL_NAME (fn_fields)))
	      {
	      case 0:
		basep = 0;
		break;
	      case 1:
		basep = lookup_fnfields (t, DECL_NAME (fn_fields));
		break;
	      default:
		basep = error_mark_node;
		break;
	      }
	  else
	    basep = NULL_TREE;

	  if (head)
	    {
	      if (DECL_NAME (fn_fields) == name)
		{
		  head = tree_cons (name, fn_fields, head);
		}
	      else
		{
		  if (TREE_CODE (fn_fields) == FIELD_DECL)
		    TREE_CHAIN (tail) = build_tree_list (DECL_NAME (fn_fields), fn_fields);
		  else
		    {
		      TREE_CHAIN (tail) = build_tree_list (DECL_NAME (fn_fields), NULL_TREE);
		      TREE_TYPE (TREE_CHAIN (tail)) = fn_fields;
		    }
		  tail = TREE_CHAIN (tail);
		}
	    }
	  else
	    {
	      if (TREE_CODE (fn_fields) == FIELD_DECL)
		head = build_tree_list (DECL_NAME (fn_fields), fn_fields);
	      else
		{
		  head = build_tree_list (DECL_NAME (fn_fields), NULL_TREE);
		  TREE_TYPE (head) = fn_fields;
		}
	      tail = head;
	    }
	  TREE_OVERLOADED (tail) = TREE_OVERLOADED (TREE_TYPE (fn_fields));
	  SET_DECL_BASELINK (fn_fields, basep);
	}
      fn_fields = nextp;
    }

  /* If there are constructors (and destructors), they are at the
     front.  Place destructors at very front.  */
  if (TREE_HAS_DESTRUCTOR (t))
    {
      tree dtor, prev;

      for (dtor = TREE_VALUE (head); dtor; prev = dtor, dtor = TREE_CHAIN (dtor))
	{
	  if (DESTRUCTOR_NAME_P (DECL_NAME (TREE_TYPE (dtor))))
	    break;
	}
      if (dtor != TREE_VALUE (head))
	{
	  TREE_CHAIN (prev) = TREE_CHAIN (dtor);
	  TREE_CHAIN (dtor) = TREE_VALUE (head);
	  TREE_VALUE (head) = dtor;
	}
    }
  /* Notice whether this class has type conversion functions defined.  */
  for (i = CLASSTYPE_N_BASECLASSES (t); i > 0; i--)
    {
      if (CLASSTYPE_BASECLASS (t, i) && TREE_HAS_TYPE_CONVERSION (CLASSTYPE_BASECLASS (t, i)))
	{
	  TREE_HAS_TYPE_CONVERSION (t) = 1;
	  TREE_HAS_INT_CONVERSION (t) |= TREE_HAS_INT_CONVERSION (CLASSTYPE_BASECLASS (t, i));
	  TREE_HAS_REAL_CONVERSION (t) |= TREE_HAS_REAL_CONVERSION (CLASSTYPE_BASECLASS (t, i));
	}
    }

  if (TREE_HAS_INT_CONVERSION (t) == 0 || TREE_HAS_REAL_CONVERSION (t) == 0)
    {
      tree tmp = head;
      int need_int = ! TREE_HAS_INT_CONVERSION (t);
      int need_real = ! TREE_HAS_REAL_CONVERSION (t);

      while (tmp)
	{
	  if (OPERATOR_TYPENAME_P (TREE_PURPOSE (tmp)))
	    {
	      tree return_type = TREE_TYPE (TREE_TYPE (TREE_TYPE (TREE_VALUE (tmp))));
	      TREE_HAS_TYPE_CONVERSION (t) = 1;
	      if (need_int && TREE_CODE (return_type) == INTEGER_TYPE)
		{
		  TREE_HAS_INT_CONVERSION (t) = 1;
		  need_int = 0;
		  if (need_real == 0)
		    break;
		}
	      else if (need_real && TREE_CODE (return_type) == REAL_TYPE)
		{
		  TREE_HAS_REAL_CONVERSION (t) = 1;
		  need_real = 0;
		  if (need_int == 0)
		    break;
		}
	    }
	  tmp = TREE_CHAIN (tmp);
	}
    }

  TYPE_FN_FIELDS (t) = head;

  if (code == UNION_TYPE)
    {
      TREE_NEEDS_CONSTRUCTOR (t) = 0;
      TREE_NEEDS_DESTRUCTOR (t) = 0;
      if (has_virtual)
	error ("virtual functions not allowed in unions");
      TYPE_VSIZE (t) = (int) integer_zero_node;
    }
  else
    {
      TREE_NEEDS_CONSTRUCTOR (t) |= needs_ctor || has_virtual || TREE_HAS_CONSTRUCTOR (t);
      TREE_NEEDS_DESTRUCTOR (t) |= needs_dtor || TREE_HAS_DESTRUCTOR (t);


      if (has_virtual)
	{
#ifdef VTABLE_USES_MASK
	  if (has_virtual >= VINDEX_MAX)
	    {
	      error ("too many virtual functions for class `%s'");
	    }
#endif
	  TREE_VIRTUAL (t) = 1;
	  TYPE_VSIZE (t) = (int) build_int_2 (has_virtual, 0);
	  TYPE_VIRTUALS (t) = pending_virtuals;
	}
      else
	{
	  TYPE_VSIZE (t) = (int) integer_zero_node;
	}
    }
  TREE_NEEDS_WRAPPER (t) |= needs_wrapper || TREE_HAS_WRAPPER (t);
  TREE_ANY_ASSIGNS_THIS (t) = any_assigns_this;

  /* We can't know this information until we have seen all of the
     constructors.  */
  TREE_NONE_ASSIGN_THIS (t) = 0;

  /* This must be laid out *after* we know about constructors, et. al.  */
  layout_type (t);

  /* Promote each bit-field's type to int if it is narrower than that.  */
  for (x = fields; x; x = TREE_CHAIN (x))
    if (TREE_PACKED (x)
	&& TREE_CODE (TREE_TYPE (x)) == INTEGER_TYPE
	&& (TREE_INT_CST_LOW (DECL_SIZE (x)) * DECL_SIZE_UNIT (x)
	    < TYPE_PRECISION (integer_type_node)))
      TREE_TYPE (x) = integer_type_node;

  embrace_waiting_friends (t);

  /* Write out inline function definitions.  */
  do_inline_method_hair (name, head);

  if (! flag_this_is_variable && TREE_VIRTUAL (t))
    {
      tree vtbl_ptr = build_decl (VAR_DECL, get_identifier (VPTR_NAME),
				  TREE_TYPE (vfield));
      TREE_REGDECL (vtbl_ptr) = 1;
      SET_DECL_VTBL_PTR (TYPE_NAME (t), vtbl_ptr);
    }
  else
    SET_DECL_VTBL_PTR (TYPE_NAME (t), NULL_TREE);

  /* Now out of this class's scope.  However, if this class defined
     any new typedefs, then we must export those to the outer
     binding level.  This is unpleasant.  */
  x = gettags ();

  popclass (0);

#if 0
  /* Remove aggregate types from the list of tags,
     since these appear at global scope.  */
  while (x && IS_AGGR_TYPE (TREE_VALUE (x)))
    x = TREE_CHAIN (x);
  TYPE_TAGS (t) = x;
  y = x;
  while (x)
    {
      if (IS_AGGR_TYPE (TREE_VALUE (x)))
	TREE_CHAIN (y) = TREE_CHAIN (x);
      x = TREE_CHAIN (x);
    }
#endif

  hack_incomplete_structures (t);

  resume_momentary (old);

  return t;
}

/* Ordering function for overload resolution.  */
int
rank_for_overload (x, y)
     struct candidate *x, *y;
{
  if (y->evil - x->evil)
    return y->evil - x->evil;
  if (y->user - x->user)
    return y->user - x->user;
  if (y->b_or_d - x->b_or_d)
    return y->b_or_d - x->b_or_d;
  return y->easy - x->easy;
}

/* TYPE is the type we wish to convert to.  PARM is the parameter
   we have to work with.  We use a somewhat arbitrary cost function
   to measure this conversion.  */
int
convert_harshness (type, parm)
     tree type, parm;
{
  register enum tree_code codel = TREE_CODE (type);
  register enum tree_code coder = TREE_CODE (TREE_TYPE (parm));

  if (TREE_TYPE (parm) == type)
    return 0;

  if (coder == ERROR_MARK)
    return 1;

  if (coder == FUNCTION_TYPE || coder == UNKNOWN_TYPE)
    {
      if (codel == FUNCTION_TYPE
	  || (codel == POINTER_TYPE
	      && TREE_CODE (TREE_TYPE (type)) == FUNCTION_TYPE))
	return 0;
      return 1;
    }

  if (coder == VOID_TYPE)
    return 1;

  /* Arithmetic types all interconvert, and enum is treated like int.
     But, since we did not get an exact match, favor `int'.  */
  if (codel == INTEGER_TYPE || codel == ENUMERAL_TYPE)
    if (coder == INTEGER_TYPE || coder == ENUMERAL_TYPE)
      {
	int easy = TREE_UNSIGNED (type) ^ TREE_UNSIGNED (TREE_TYPE (parm));
	if (TYPE_MODE (type) != TYPE_MODE (TREE_TYPE (parm)))
	  easy += 2;
	return (easy << 4);
      }
    else if (coder == REAL_TYPE)
      return (4<<4);

  if (codel == REAL_TYPE)
    if (coder == REAL_TYPE)
      /* Shun converting between float and double if a choice exists.  */
      {
	if (TYPE_MODE (type) != TYPE_MODE (TREE_TYPE (parm)))
	  return (4<<4);
	return 0;
      }
    else if (coder == INTEGER_TYPE || coder == ENUMERAL_TYPE)
      return (4<<4);

  /* convert arrays which have not previously been converted.  */
  if (codel == ARRAY_TYPE)
    codel = POINTER_TYPE;
  if (coder == ARRAY_TYPE)
    coder = POINTER_TYPE;

  /* Conversions among pointers */
  if (codel == POINTER_TYPE && coder == POINTER_TYPE)
    {
      register tree ttl = TREE_TYPE (type);
      register tree ttr = TREE_TYPE (TREE_TYPE (parm));
      int penalty = 4 * (ttl != ttr);
      int b_or_d = 0;
      /* Anything converts to void *.  void * converts to anything.
	 Since these may be `const void *' (etc.) use VOID_TYPE
	 instead of void_type_node.
	 Otherwise, the targets must be the same,
	 except that we do allow (at some cost) conversion
	 between signed and unsinged pointer types.  */

      if (!((TREE_CODE (ttl) == VOID_TYPE
	     && TREE_CODE (ttr) != FUNCTION_TYPE)
	    || (TREE_CODE (ttr) == VOID_TYPE
		&& TREE_CODE (ttl) != FUNCTION_TYPE)
	    || (TREE_UNSIGNED (ttl) ^ TREE_UNSIGNED (ttr)
		&& (ttl = unsigned_type (ttl),
		    ttr = unsigned_type (ttr),
		    penalty = 10, 0))
	    || (comp_target_types (ttl, ttr))))
	return 1;

      if (ttr == ttl)
	return (b_or_d<<3) | 4;

      if (IS_AGGR_TYPE (ttr))
	while (1)
	  {
	    if (CLASSTYPE_N_BASECLASSES (ttr) == 0)
	      break;
	    ttr = CLASSTYPE_BASECLASS (ttr, 1);
	    b_or_d = 1;
	    if (ttr == ttl)
	      return (b_or_d<<3) | 4;
	  }

      return (penalty<<4);
    }

  if (codel == POINTER_TYPE && coder == INTEGER_TYPE)
    {
      if (integer_zerop (parm))
	return 0;
    }

  /* C++: one of the types must be a reference type.  */
  {
    tree ttl, ttr;
    register tree intype = TREE_TYPE (parm);
    register enum tree_code form = TREE_CODE (intype);
    int penalty;

    if (codel == REFERENCE_TYPE || coder == REFERENCE_TYPE)
      {
	int b_or_d = 0;
	ttl = type;

	if (codel == REFERENCE_TYPE)
	  {
	    ttl = TREE_TYPE (ttl);
	    
	    if (form == REFERENCE_TYPE)
	      {
		intype = TREE_TYPE (intype);

		if (ttl == intype)
		  return 0;
		penalty = 2;
	      }
	    else
	      {
		/* Can reference be built up?  */
		if (ttl == intype)
		  {
		    return 0;
		  }
		else
		  penalty = 2;
	      }
	  }
	else if (form == REFERENCE_TYPE)
	  {
	    tree tmp = bash_reference_type (parm);

	    intype = TREE_TYPE (tmp);

	    if (ttl == intype)
	      return 0;
	    else
	      penalty = 2;
	  }

	if (TREE_UNSIGNED (ttl) ^ TREE_UNSIGNED (intype))
	  {
	    ttl = unsigned_type (ttl);
	    intype = unsigned_type (intype);
	    penalty += 2;
	  }

	ttr = intype;

	/* Pointers to voids always convert for pointers.  But
	   make them less natural than more specific matches.  */
	if (TREE_CODE (ttl) == POINTER_TYPE && TREE_CODE (ttr) == POINTER_TYPE)
	  if (TREE_TYPE (ttl) == void_type_node
	      || TREE_TYPE (ttr) == void_type_node)
	    return ((penalty+1)<<4);

	if (ttr == ttl)
	  return (b_or_d<<3) | 4;

	if (IS_AGGR_TYPE (ttr))
	  while (1)
	    {
	      b_or_d = 1;
	      if (CLASSTYPE_N_BASECLASSES (ttr) == 0)
		break;
	      ttr = CLASSTYPE_BASECLASS (ttr, 1);
	      if (ttr == ttl)
		return (b_or_d<<3) | 4;
	    }

	if (comp_target_types (ttl, intype))
	  return (penalty<<4);
      }
  }
  return 1;
}

/* Algorithm: Start out with no stikes against.  For each argument
   which requires a (subjective) hard conversion (such as between
   floating point and integer), issue a strike.  If there are the same
   number of formal and actual parameters in the list, there will be at
   least on strike, otherwise an exact match would have been found.  If
   there are not the same number of arguments in the type lists, we are
   not dead yet: a `...' means that we can have more parms then were
   declared, and if we wind up in the default argument section of the
   list those can be used as well.  If an exact match could be found for
   one of those cases, return it immediately.  Otherwise, Rank the fields
   so that fields with fewer strikes are tried first.

   Conversions between builtin and user-defined types are allowed, but
   no function involving such a conversion is prefered to one which
   does not require such a conversion.  Furthermore, such conversions
   must be unique.  */

void
compute_conversion_costs (function, tta_in, cp, arglen)
     tree function;
     tree tta_in;
     struct candidate *cp;
     int arglen;
{
  tree ttf = TYPE_ARG_TYPES (TREE_TYPE (function));
  tree tta = tta_in;

  /* Start out with no strikes against.  */
  int evil_strikes = 0;
  int user_strikes = 0;
  int b_or_d_strikes = 0;
  int easy_strikes = 0;

  int *strikes_memoized = (int *)alloca (arglen * sizeof (int));
  int strike_index = 0, win, lose;

  cp->function = function;
  cp->arg = TREE_VALUE (tta);
  cp->u.bad_arg = 0;		/* optimistic!  */

  while (ttf && tta)
    {
      int harshness;

      if (TREE_VALUE (ttf) == void_type_node)
	break;

      if (TREE_TYPE (TREE_VALUE (tta)) == unknown_type_node)
	{	  
	  /* Must perform some instantiation here.  */
	  tree rhs = TREE_VALUE (tta);
	  tree lhstype = TREE_VALUE (ttf);

	  /* @@ This is to undo what `grokdeclarator' does to
	     parameter types.  It really should go through
	     something more general.  */

	  TREE_TYPE (tta) = unknown_type_node;
	  if (TREE_CODE (rhs) == OP_EXPR)
	    rhs = build_instantiated_decl (TREE_VALUE (ttf), rhs);
	  else if (TREE_CODE (rhs) == TREE_LIST)
	    {
	      /* Do not let the side-effect take place too deeply.
		 Once we have selected the correct function to
		 call, actualparameterlist will perform the
		 real type instantiation.  */
	      rhs = copy_node (tta);
	      instantiate_type (TREE_VALUE (ttf), rhs);
	      if (TREE_TYPE (rhs) != error_mark_node)
		rhs = TREE_VALUE (rhs);
	      else
		rhs = error_mark_node;
	    }
	  else
	    instantiate_type (TREE_VALUE (ttf), rhs);

	  harshness = convert_harshness (TREE_VALUE (ttf), rhs);
	  harshness |= 2;
	}
      else
	harshness = convert_harshness (TREE_VALUE (ttf), TREE_VALUE (tta));

      strikes_memoized[strike_index++] = harshness;
      if (harshness & 1)
	evil_strikes = 1;
      else if (harshness & 2)
	user_strikes += 1;
      else if (harshness & 4)
	b_or_d_strikes += (harshness >> 3);
      else
	easy_strikes += harshness >> 4;
      ttf = TREE_CHAIN (ttf);
      tta = TREE_CHAIN (tta);
    }

  if (tta)
    {
      /* ran out of formals, and parmlist is fixed size.  */
      if (ttf /* == void_type_node */)
	{
	  cp->evil = 1;
	  cp->u.bad_arg = -1;
	  return;
	}
    }
  else if (ttf)
    {
      /* ran out of actuals, and no defaults.  */
      if (TREE_VALUE (ttf) != void_type_node
	  && TREE_PURPOSE (ttf) == NULL_TREE)
	{
	  cp->evil = 1;
	  cp->u.bad_arg = -2;
	  return;
	}
    }

  /* Argument list lengths work out, so don't need to check them again.  */
  if (evil_strikes)
    {
      /* See if any user-defined conversions apply.
         But make sure that we do not loop.  */
      static int dont_convert_types = 0;

      if (dont_convert_types)
	{
	  cp->evil = 1;
	  return;
	}

      win = 0;			/* Only get one chance to win.  */
      ttf = TYPE_ARG_TYPES (TREE_TYPE (function));
      tta = tta_in;
      evil_strikes = 0;
      user_strikes = 0;
      b_or_d_strikes = 0;
      evil_strikes = 0;
      strike_index = 0;

      while (ttf && tta)
	{
	  if (TREE_VALUE (ttf) == void_type_node)
	    break;

	  lose = strikes_memoized[strike_index++];
	  if (lose&1)
	    {
	      tree actual_type = TREE_TYPE (TREE_VALUE (tta));
	      tree formal_type = TREE_VALUE (ttf);

	      dont_convert_types = 1;

	      if (TREE_CODE (formal_type) == REFERENCE_TYPE)
		formal_type = TREE_TYPE (formal_type);
	      if (TREE_CODE (actual_type) == REFERENCE_TYPE)
		actual_type = TREE_TYPE (actual_type);

	      formal_type = TYPE_MAIN_VARIANT (formal_type);
	      actual_type = TYPE_MAIN_VARIANT (actual_type);

	      if (TREE_HAS_CONSTRUCTOR (formal_type))
		{
		  /* If it has a constructor for this type, try to use it.  */
		  if (convert_to_aggr (formal_type, TREE_VALUE (tta), 0, 1)
		      != error_mark_node)
		    {
		      /* @@ There is no way to save this result yet.
		         @@ So success is NULL_TREE for now.  */
		      win++;
		    }
		}
	      if (IS_AGGR_TYPE (actual_type) && TREE_HAS_TYPE_CONVERSION (actual_type))
		{
		  if (TREE_CODE (formal_type) == INTEGER_TYPE
		      && TREE_HAS_INT_CONVERSION (actual_type))
		    win++;
		  else if (TREE_CODE (formal_type) == REAL_TYPE
			   && TREE_HAS_REAL_CONVERSION (actual_type))
		    win++;
		  else if (build_type_conversion (formal_type, TREE_VALUE (tta), 0))
		    win++;
		}

	      dont_convert_types = 0;

	      if (win == 1)
		{
		  user_strikes += 1;
		  win = 0;
		}
	      else
		{
		  if (cp->u.bad_arg == 0)
		    cp->u.bad_arg = strike_index;

		  evil_strikes = win ? 2 : 1;
		  break;
		}
	    }
	  else if (lose&2)
	    user_strikes += 1;
	  else if (lose&4)
	    b_or_d_strikes += lose>>3;
	  else
	    easy_strikes += lose>>4;

	  ttf = TREE_CHAIN (ttf);
	  tta = TREE_CHAIN (tta);
	}
    }
  cp->evil = evil_strikes;
  cp->user = user_strikes;
  cp->b_or_d = b_or_d_strikes;
  cp->easy = easy_strikes;
}

/* Assume that if the class referred to is not in the
   current class hierarchy, that it may be remote.
   PARENT is assumed to be of aggregate type here.  */
static int
may_be_remote (parent)
     tree parent;
{
  if (TREE_HAS_METHOD_CALL_OVERLOADED (parent) == 0)
    return 0;

  if (current_class_type == NULL_TREE)
    return 0;
  if (parent == current_class_type)
    return 0;

  if (get_base_type (parent, current_class_type))
    return 0;
  return 1;
}

/* Return the number of bytes that the arglist in PARMS would
   occupy on the stack.  */
int
get_arglist_len_in_bytes (parms)
     tree parms;
{
  register tree parm;
  register int bytecount = 0;

  for (parm = parms; parm; parm = TREE_CHAIN (parm))
    {
      register tree pval = TREE_VALUE (parm);
      register int used, size;

      if (TREE_CODE (pval) == ERROR_MARK)
	continue;
      else if (TYPE_MODE (TREE_TYPE (pval)) != BLKmode)
	{
	  used = size = GET_MODE_SIZE (TYPE_MODE (TREE_TYPE (pval)));
	  size = PUSH_ROUNDING (size);
	  used = (((size + PARM_BOUNDARY / BITS_PER_UNIT - 1)
		   / (PARM_BOUNDARY / BITS_PER_UNIT))
		  * (PARM_BOUNDARY / BITS_PER_UNIT));
	}
      else
	{
	  register tree size = size_in_bytes (TREE_TYPE (pval));
	  register tree used_t = convert_units (convert_units (size, BITS_PER_UNIT, PARM_BOUNDARY),
						PARM_BOUNDARY, BITS_PER_UNIT);
	  used = TREE_INT_CST_LOW (used_t);
	}
      bytecount += used;
    }
  return bytecount;
}

/* Build something of the form ptr->method (args)
   or object.method (args).  This can also build
   calls to constructors, and find friends.

   Member functions always take their class variable
   as a pointer.

   INSTANCE is a class instance. It's type name will go into
   BASENAME. Make an expression to refer to the NAME field of
   structure, union, or class value BASENAME.  NAME is an
   FUNCTION_DECL. The parameters PARMS help to figure out what
   that NAME was renamed to. If this is all OK, calls
   build_function_call with resolved overloaded info.

   This function must also handle being called to perform
   initialization, promotion/coercion of arguments, and
   instantiation of default parameters.

   COMPLAIN is nonzero if, upon encountering an error,
   an error message should be printed.

   If COMPLAIN is 1, then figure out INSTANCE.
   If COMPLAIN is 2, then INSTANCE should be of aggregate type.
   If COMPLAIN is 3, then figure out INSTANCE, and do not make a virtual call.
     In this case, we can count on vtbl == NULL_TREE
     @@ This will not work properly with flag_all_virtual.
   If COMPLAIN is 4, then we have license to look for an overloaded
   function if the matches we get in the class are too dismal.  If this
   fails, we do not emit an error message, because it is still possible
   that these arguments will convert to some scalar type, and normal
   operators will take effect on them.

   Note that NAME may refer to an instance variable name.  If
   `operator()()' is defined for the type of that field, then we return
   that result.

   When converting the class instance variable from REFERENCE_TYPE to
   POINTER_TYPE, we must do so with a REFERENCE_EXPR, *not* a NOP_EXPR.
   This is because the conversion is for initialization.  */
tree
build_classfn_ref (instance, name, parms, protect, complain)
     tree instance, name, parms;
     int protect, complain;
{
  register tree function, fntype, value_type;
  register tree classname, basetype, save_basetype, basetypes;
  register enum tree_code form;
  register tree fields, field, result, method_name, parmtypes, parm;
  enum visibility_type visibility;
  int rank_for_overload ();
  tree vtbl = NULL_TREE;
  char *err_name;
  char *name_kind;
  int ever_seen = 0;
  int wrap;
  tree wrap_type;
  tree instance_ptr = NULL_TREE;
  int via_public = 1;
  int all_virtual = flag_all_virtual;
  int saw_private = 0;
  int saw_protected = 0;

  if (instance == error_mark_node
      || name == error_mark_node
      || parms == error_mark_node)
    return error_mark_node;

  if (TREE_CODE (name) == WRAPPER_EXPR)
    {
      wrap_type = TREE_OPERAND (name, 0);
      name = TREE_OPERAND (name, 1);
      wrap = 1;
    }
  else if (TREE_CODE (name) == ANTI_WRAPPER_EXPR)
    {
      wrap_type = TREE_OPERAND (name, 0);
      name = TREE_OPERAND (name, 1);
      wrap = -1;
    }
  else
    {
      wrap_type = NULL_TREE;
      wrap = 0;
    }

  /* Initialize name for error reporting.  */
  if (OPERATOR_NAME_P (name))
    {
      err_name = (char *)alloca (OVERLOAD_MAX_LEN);
      sprintf (err_name, "operator %s", operator_name_string (name));
    }
  else if (name == wrapper_name)
    {
      err_name = "wrapper";
    }
  else
    err_name = IDENTIFIER_POINTER (name);

  if (wrap)
    {
      char *p = (char *)alloca (OVERLOAD_MAX_LEN);
      sprintf (p, "%s for `%s'", wrap < 0 ? "anti-wrapper" : "wrapper", err_name);
      err_name = p;
    }

  if (instance == NULL_TREE)
    {
      /* call to a constructor... */
      if (TREE_TYPE (name))
	basetype = TREE_TYPE (TREE_TYPE (name));
      else
	{
	  tree typedef_name = lookup_name (name);
	  if (typedef_name && TREE_CODE (typedef_name) == TYPE_DECL)
	    {
	      /* Cannonicalize the typedef name.  */
	      basetype = TREE_TYPE (typedef_name);
	      name = DECL_NAME (TYPE_NAME (basetype));
	    }
	  else
	    {
	      error ("no constructor named `%s' in visible scope",
		     IDENTIFIER_POINTER (name));
	      return error_mark_node;
	    }
	}
      if (wrap_type && wrap_type != basetype)
	{
	  error ("invalid constructor `%s::%s'",
		 TYPE_NAME_STRING (wrap_type),
		 TYPE_NAME_STRING (basetype));
	  return error_mark_node;
	}
      if (TREE_VIRTUAL (basetype))
	{
	  wrap_type = basetype;
	}

      form = TREE_CODE (basetype);

      if (! IS_AGGR_TYPE_CODE (form))
	{
	non_aggr_error:
	  if (complain && form != ERROR_MARK)
	    error ("request for member `%s' in something not a structure or union", err_name);

	  return error_mark_node;
	}
    }
  else if (instance == C_C_D || instance == current_class_decl)
    {
      /* Check to see if we really have a reference to an instance variable
	 with `operator()()' overloaded.  */
      instance = lookup_name (name);
      if (TREE_NONLOCAL (instance) && TREE_CODE (instance) ==
#if 1
	  FIELD_DECL
#else
	  VAR_DECL
#endif
	  )
	{
	  if (IS_AGGR_TYPE (TREE_TYPE (instance)) && TREE_HAS_CALL_OVERLOADED (TREE_TYPE (instance)))
	    return build_opfncall (CALL_EXPR, C_C_D, parms);
	}

      /* When doing initialization, we side-effect the TREE_TYPE of
	 C_C_D, hence we cannot set up BASETYPE from CURRENT_CLASS_TYPE.  */

      instance = C_C_D;
      basetype = TREE_TYPE (instance);
      instance_ptr = current_class_decl;
      if (complain != 3 && wrap_type == NULL_TREE && TREE_VIRTUAL (basetype))
	{
	  if (flag_this_is_variable)
	    vtbl = build_indirect_ref (build_component_ref (instance, get_vfield_name (basetype), 0));
	  else
	    vtbl = current_vtable_decl;
	}
    }
  else if (TREE_CODE (instance) == RESULT_DECL)
    {
      basetype = TYPE_MAIN_VARIANT (TREE_TYPE (instance));
      if (wrap_type)
	{
	  if (basetype == wrap_type || get_base_type (basetype, wrap_type))
	    basetype = wrap_type;
	  else
	    {
	      error ("type `%s' is not derived from type `%s'",
		     TYPE_NAME_STRING (wrap_type), TYPE_NAME_STRING (basetype));
	      return error_mark_node;
	    }
	}
      /* Should we ever have to make a virtual function reference
	 from a RESULT_DECL, know that it must be of fixed type
	 within the scope of this function.  */
      else if (complain != 3 && TREE_VIRTUAL (basetype))
	vtbl = get_vtable_name (basetype);
      instance_ptr = build_unary_op (ADDR_EXPR, instance, 0);
    }
  else
    {
      /* The MAIN_VARIANT of the type that `instance_ptr' winds up being.  */
      tree inst_ptr_basetype;

      /* from the file "typecheck.c".  */
      extern tree unary_complex_lvalue ();

      /* the base type of an instance variable is pointer to class */
      basetype = TYPE_MAIN_VARIANT (TREE_TYPE (instance));

      if (basetype == error_mark_node)
	return error_mark_node;

      if (TREE_CODE (basetype) == REFERENCE_TYPE)
	{
	  basetype = TYPE_MAIN_VARIANT (TREE_TYPE (basetype));
	  if (! IS_AGGR_TYPE (basetype))
	    goto non_aggr_error;
	  /* Call to convert not needed because we are remaining
	     within the same type.  */
#if 0
	  instance_ptr = build (REFERENCE_EXPR, TYPE_POINTER_TO (basetype), instance);
#else
	  instance_ptr = build (NOP_EXPR, TYPE_POINTER_TO (basetype), instance);
#endif
	  inst_ptr_basetype = basetype;
	}
      else
	{
	  if (TREE_CODE (basetype) == POINTER_TYPE)
	    {
	      basetype = TREE_TYPE (basetype);
	      instance_ptr = instance;
	    }

	  if (! IS_AGGR_TYPE (basetype))
	    goto non_aggr_error;

	  if (! instance_ptr)
	    if ((lvalue_p (instance)
		 && (instance_ptr = build_unary_op (ADDR_EXPR, instance, 0)))
		|| (instance_ptr = unary_complex_lvalue (ADDR_EXPR, instance)))
	      {
		/* This may only remove an INDIRECT_REF, which might
		   leave us with the wrong type, so we may have to
		   cast.
		   
		   @@ Should we call comp_target_types here?  */
		inst_ptr_basetype = TYPE_MAIN_VARIANT (TREE_TYPE (TREE_TYPE (instance_ptr)));
		if (basetype != inst_ptr_basetype)
		  {
		    /* see when this happens for multiple inheritance.  */
		    abort ();
		    instance_ptr = convert (TYPE_POINTER_TO (basetype), instance_ptr);
		  }
	      }
	    else
	      {
		instance = get_temp_name (basetype, error_mark_node, instance);
		instance_ptr = build_unary_op (ADDR_EXPR, instance, 0);
		inst_ptr_basetype = TYPE_MAIN_VARIANT (TREE_TYPE (TREE_TYPE (instance_ptr)));
	      }
	  else
	    inst_ptr_basetype = TYPE_MAIN_VARIANT (TREE_TYPE (TREE_TYPE (instance_ptr)));
	}

      {
	/* Check to see if this is not really a reference to an instance variable
	   with `operator()()' overloaded.  */
	tree field = lookup_field (inst_ptr_basetype, name, 0);

	/* This can happen if the reference was ambiguous.  */
	if (field == error_mark_node)
	  return error_mark_node;

	if (field && IS_AGGR_TYPE (TREE_TYPE (field))
	    && TREE_HAS_CALL_OVERLOADED (TREE_TYPE (field)))
	  {
	    /* Make the next search for this field very short.  */
	    basetype = DECL_CONTEXT (field);
	    instance_ptr = convert_to_nonzero_pointer (TYPE_POINTER_TO (basetype),
						       instance_ptr);

	    instance = build_indirect_ref (instance_ptr, "class instance dereferencing (compiler error)");
	    return build_opfncall (CALL_EXPR, build_component_ref (instance, name, 1), parms);
	  }
      }

      if (wrap_type)
	{
	  if (basetype == wrap_type || get_base_type (basetype, wrap_type))
	    basetype = wrap_type;
	  else
	    {
	      error ("type `%s' is not derived from type `%s'",
		     TYPE_NAME_STRING (wrap_type), TYPE_NAME_STRING (basetype));
	      return error_mark_node;
	    }
	}
      else if (complain != 3 && TREE_VIRTUAL (basetype))
	{
	  tree ref = instance_ptr;

	  /* No need to make a SAVE_EXPR for really easy things.  */
	  if (TREE_CODE (ref) == ADDR_EXPR)
	    ref = TREE_OPERAND (ref, 0);
	  while (TREE_CODE (ref) == NOP_EXPR
#if 0
		 || TREE_CODE (ref) == REFERENCE_EXPR
#endif
		 )
	    ref = TREE_OPERAND (ref, 0);

	  if (TREE_CODE (ref) != PARM_DECL && TREE_CODE (ref) != VAR_DECL)
	    {
	      /* This action is needed because the instance is needed
		 for providing the base of the virtual function table.
		 Without using a SAVE_EXPR, the function we are building
		 may be called twice, or side effects on the instance
		 variable (such as a post-increment), may happen twice.  */
	      ref = instance_ptr;

	      if (TREE_CODE (TREE_TYPE (ref)) == REFERENCE_TYPE)
#if 0
		ref = build (REFERENCE_EXPR, build_pointer_type (TREE_TYPE (TREE_TYPE (ref))), ref);
#else
	      ref = build (NOP_EXPR, build_pointer_type (TREE_TYPE (TREE_TYPE (ref))), ref);
#endif
	      ref = save_expr (ref);
	      if (TREE_TYPE (ref) == TREE_TYPE (instance_ptr))
		{
		  instance_ptr = ref;
		}
	      else
		{
		  instance_ptr = convert_to_nonzero_pointer (TREE_TYPE (instance_ptr), ref);
		}
	      instance = instance_ptr;
	    }

	  if (TREE_CODE (TREE_TYPE (instance)) == POINTER_TYPE)
	    ref = build_indirect_ref (instance, "class instance dereferencing (compiler error)");
	  else
	    ref = instance;

	  vtbl = build_indirect_ref (build_component_ref (ref, get_vfield_name (basetype), 0), "virtual function table lookup (compiler error)");
	}
    }

  /* Are we building a non-virtual wrapper?  */
  if (complain == 3)
    {
      if (all_virtual)
	sorry ("non-virtual call with -fall-virtual");
      if (wrap)
	wrap_type = basetype;
    }

  save_basetype = basetype;

  if (! strncmp (IDENTIFIER_POINTER (name), "op$method_ref", 13)
      || instance_ptr == NULL_TREE
      || resolves_to_fixed_type_p (instance_ptr))
    all_virtual = 0;
		  
  if (TYPE_SIZE (save_basetype) == 0)
    {
      /* This is worth complaining about, I think.  */
      error ("cannot lookup method in incomplete type `%s'",
	     TYPE_NAME_STRING (save_basetype));
      return error_mark_node;
    }

  /* Build up the name of the function we are looking for.  */
  parmtypes = build_tree_list (NULL_TREE, TYPE_POINTER_TO (basetype));
  for (parm = parms; parm; parm = TREE_CHAIN (parm))
    {
      tree t = TREE_TYPE (TREE_VALUE (parm));
      if (t == error_mark_node)
	return error_mark_node;
      if (TREE_CODE (t) == ARRAY_TYPE)
	{
	  /* Perform the conversion from ARRAY_TYPE to
	     POINTER_TYPE in place.  This eliminates
	     needless calls to `compute_conversion_costs'.  */
	  TREE_VALUE (parm) = default_conversion (TREE_VALUE (parm));
	  t = TREE_TYPE (TREE_VALUE (parm));
	}
      parmtypes = chainon (parmtypes, build_tree_list (NULL_TREE, t));
    }

  if (instance)
    {
      parms = tree_cons (NULL_TREE, instance_ptr, parms);
    }
  else
    {
#if 0
      parms = tree_cons (NULL_TREE, build (REFERENCE_EXPR, TYPE_POINTER_TO (basetype), integer_zero_node), parms);
#else
      parms = tree_cons (NULL_TREE, build (NOP_EXPR, TYPE_POINTER_TO (basetype), integer_zero_node), parms);
#endif
    }

  basetypes = build_tree_list (NULL_TREE, save_basetype);

  /* Look up function name in the structure type definition.  */
  if (TREE_USES_MULTIPLE_INHERITANCE (basetype))
    abort ();

  while (1)
    {
      classname = DECL_NAME (TYPE_NAME (basetype));

      if (wrap)
	;
      else if (classname == name)
	name_kind = "constructor";
      else
	name_kind = "method";

      for (fields = TYPE_FN_FIELDS (basetype); fields; fields = TREE_CHAIN (fields))
	{
	  if (TREE_PURPOSE (fields) == name)
	    {
	      /* We have a hit (of sorts). If the parameter list is
		 "error_mark_node", or some variant thereof, it won't
		 match any methods. Since we have verified that the is
		 some method vaguely matching this one (in name at least),
		 silently return */

	      /* Cast the instance variable to the approriate type.  */
	      TREE_VALUE (parmtypes) = TYPE_POINTER_TO (basetype);

	      /* Now, go look for this method name.
	         We do not find destructors here.  */
	      method_name = do_decl_overload (IDENTIFIER_POINTER (name), parmtypes);
	      field = TREE_VALUE (fields);
	      if (fields == TYPE_FN_FIELDS (basetype) && TREE_HAS_DESTRUCTOR (basetype))
		field = TREE_CHAIN (field);

	      while (field)
		{
		  ever_seen++;

		  if (DECL_NAME (TREE_TYPE (field)) == method_name)
		    {
		      if (protect)
			visibility = compute_visibility (basetypes, field);

		      /* If we are referencing a virtual function
			 from a variable of effectively static type,
			 then there is no need to go through the
			 virtual function table.  */
		      if (vtbl
			  && (TREE_VIRTUAL (field)
			      || (all_virtual
				  && TREE_HAS_METHOD_CALL_OVERLOADED (basetype)
				  && name != DECL_NAME (TYPE_NAME (basetype))
				  && may_be_remote (basetype))))
			{
			  function = build_array_ref (vtbl, DECL_VINDEX (field));
			  TREE_TYPE (function) = build_pointer_type (TREE_TYPE (TREE_TYPE (field)));
			}
		      else
			{
			  function = TREE_TYPE (field);
			}
		      if (protect == 0 || visibility == visibility_public)
			goto found_and_ok;
		      else if (visibility == visibility_private)
			saw_private = 1;
		      else if (visibility == visibility_protected)
			saw_protected = 1;
		      /* Saw a good method, but we did not have access rights
			 to it.  See if a base class provides something
			 which we can "see".  */
		      break;
		    }
		  field = TREE_CHAIN (field);
		}
	      break;		/* rest are losers */
	    }
	}

      /* constructors are in very specific places.  */
      if (classname == name)
	break;

      if (CLASSTYPE_N_BASECLASSES (basetype))
	{
	  if (protect)
	    {
	      via_public &= CLASSTYPE_VIA_PUBLIC (basetype, 1);

	      if (basetype != current_class_type && via_public == 0)
		visibility = visibility_private;
	    }
	  basetypes = tree_cons (CLASSTYPE_VIA_PUBLIC (basetype, 1),
				 CLASSTYPE_BASECLASS (basetype, 1),
				 basetypes);
	  basetype = CLASSTYPE_BASECLASS (basetype, 1);
	}
      else break;
    }

  /* No exact match could be found.  Now try to find match
     using default conversions.  */
  if (complain == 4 && IDENTIFIER_GLOBAL_VALUE (name)
      && (TREE_CODE (IDENTIFIER_GLOBAL_VALUE (name)) == FUNCTION_DECL
	  || TREE_CODE (IDENTIFIER_GLOBAL_VALUE (name)) == TREE_LIST))
    ever_seen += 1;

  if (ever_seen)
    {
      struct candidate *candidates =
	(struct candidate *) alloca ((ever_seen+1) * sizeof (struct candidate));
      struct candidate *cp = candidates;
      int len = list_length (parms);

      /* This increments every time we go up the type hierarchy.
	 The idea is to prefer a function of the derived class if possible.  */
      int b_or_d = 0;

      basetype = save_basetype;
      via_public = 1;
      visibility = visibility_public;
      basetypes = build_tree_list (NULL_TREE, save_basetype);

      /* First see if a global function has a shot at it.  */
      if (complain == 4)
	{
	  tree friend_parms;
	  tree parm = TREE_VALUE (parms);

	  if (TREE_CODE (TREE_TYPE (parm)) == REFERENCE_TYPE)
	    friend_parms = parms;
	  else if (TREE_CODE (TREE_TYPE (parm)) == POINTER_TYPE)
	    {
	      parm = build_indirect_ref (parm, "friendifying parms (compiler error)");
	      parm = convert (build_reference_type (TREE_TYPE (parm)), parm);
	      friend_parms = tree_cons (NULL_TREE, parm, TREE_CHAIN (parms));
	    }
	  else
	    abort ();

	  result = do_actual_overload (name, friend_parms, 0, cp);
	  /* If it turns out to be the one we were actually looking for
	     (it was probably a friend function), the return the
	     good result.  */
	  if (TREE_CODE (result) == CALL_EXPR)
	    return result;

	  if (cp->evil == 0)
	    {
	      /* non-standard uses: this is a special case we must
		 watch out for.  */
	      cp->u.field = 0;
	      cp->function = result;
	      cp++;
	    }
	}

      if (TREE_USES_MULTIPLE_INHERITANCE (basetype))
	abort ();

      while (1)
	{
	  classname = DECL_NAME (TYPE_NAME (basetype));

	  if (classname == name)
	    name_kind = "constructor";
	  else if (wrap)
	    if (wrap > 0)
	      name_kind = "wrapper";
	    else
	      name_kind = "anti-wrapper";
	  else
	    name_kind = "method";

	  for (fields = TYPE_FN_FIELDS (basetype); fields; fields = TREE_CHAIN (fields))
	    {
	      if (TREE_PURPOSE (fields) == name)
		{
		  field = TREE_VALUE (fields);

		  /* Get past destructor, if any.  */
		  if (fields == TYPE_FN_FIELDS (basetype)
		      && TREE_HAS_DESTRUCTOR (basetype))
		    field = TREE_CHAIN (field);

		  while (field)
		    {
		      function = TREE_TYPE (field);
		      compute_conversion_costs (function, parms, cp, len);
		      cp->b_or_d += b_or_d;
		      if (cp->evil == 0)
			{
			  cp->u.field = field;
			  /* If we are referencing a virtual function
			     from a variable of effectively static type,
			     then there is no need to go through the
			     virtual function table.  */
			  if (vtbl
			      && (TREE_VIRTUAL (field)
				  || (all_virtual
				      && TREE_HAS_METHOD_CALL_OVERLOADED (basetype)
				      && name != DECL_NAME (TYPE_NAME (basetype))
				      && may_be_remote (basetype))))
			    {
			      function = build_array_ref (vtbl, DECL_VINDEX (field));
			      TREE_TYPE (function) = build_pointer_type (TREE_TYPE (TREE_TYPE (field)));
			      cp->function = function;
			    }

			  if (protect)
			    {
			      enum visibility_type this_v;
			      this_v = compute_visibility (basetypes, field);
			      if (this_v != visibility_public)
				{
				  if (this_v == visibility_private)
				    saw_private = 1;
				  else
				    saw_protected = 1;
				  field = TREE_CHAIN (field);
				  continue;
				}
			    }
			  if (cp->user == 0 && cp->b_or_d == 0
			      && cp->easy <= 1)
			    {
			      TREE_VALUE (parms) = cp->arg;
			      goto found_and_ok;
			    }
			  cp++;
			}
		      field = TREE_CHAIN (field);
		    }
		  break;	/* rest are losers */
		}
	    }

	  /* Again, constructors can only appear in special places.  */
	  if (classname == name)
	    break;

	  if (CLASSTYPE_N_BASECLASSES (basetype))
	    {
	      if (protect)
		{
		  via_public &= CLASSTYPE_VIA_PUBLIC (basetype, 1);

		  if (basetype != current_class_type && via_public == 0)
		    visibility = visibility_private;
		}
	      basetypes = tree_cons (CLASSTYPE_VIA_PUBLIC (basetype, 1),
				     CLASSTYPE_BASECLASS (basetype, 1),
				     basetypes);
	      basetype = CLASSTYPE_BASECLASS (basetype, 1);
	      b_or_d += 1;
	    }
	  else break;
	}

      if (cp - candidates)
	{
	  /* Rank from worst to best.  Then cp will point to best one.
	     Private fields have their bits flipped.  For unsigned
	     numbers, this should make them look very large.
	     If the best alternate has a (signed) negative value,
	     then all we ever saw were private members.  */
	  if (cp - candidates > 1)
	    {
	      qsort (candidates,		/* char *base */
		     cp - candidates,		/* int nel */
		     sizeof (struct candidate),	/* int width */
		     rank_for_overload);	/* int (*compar)() */

	      if (cp[-1].user && cp[-2].user
		  && (cp[-1].b_or_d != 0 || cp[-2].b_or_d == 0))
		{
		  error ("ambiguous type conversion requested for %s `%s'",
			 name_kind, err_name);
		  return error_mark_node;
		}
	    }
	  else if (cp[-1].evil > 1)
	    {
	      error ("ambiguous type conversion requested for %s `%s'",
		     name_kind, err_name);
	      return error_mark_node;
	    }
	  cp--;

	  /* The global function was the best, so use it.  */
	  if (cp->u.field == 0)
	    {
	      /* We must convert the instance pointer into a reference type.
		 Global overloaded functions can only either take
		 aggregate objects (which come for free from references)
		 or reference data types anyway.  */
	      TREE_TYPE (instance_ptr) = build_reference_type (TREE_TYPE (TREE_TYPE (instance_ptr)));
	      TREE_VALUE (parms) = instance_ptr;
	      return build_function_call (cp->function, parms);
	    }

	  basetype = TREE_TYPE (TREE_TYPE (cp->arg));
	  TREE_VALUE (parms) = cp->arg;
	  function = cp->function;
	  field = cp->u.field;
	  goto found_and_ok;
	}

      if (complain && complain != 4)
	{
	  static char *visibility_err_messages[] =
	    {
	      "only private %ss apply",
	      "only protected %%s apply",
	      "only private and protected %ss apply",
	    };
	  if (saw_protected == 0 && saw_private == 0)
	    report_type_mismatch (cp, parms, name_kind, err_name);
	  else
	    error (visibility_err_messages[saw_private + (saw_protected<<1) - 1], name_kind);
	}
      return error_mark_node;
    }

  else if (complain && complain != 4)
    {
      char buf[OVERLOAD_MAX_LEN];

      if (TREE_CODE (save_basetype) == RECORD_TYPE)
	sprintf (buf, "structure");
      else
	sprintf (buf, "union");

      if (wrap)
	strcat (buf, " has no appropriate wrapper function defined");
      else
	strcat (buf, " has no method named `%s'");

      error (buf, err_name);
    }
  return error_mark_node;

 found:
  function = TREE_TYPE (field);

  if (visibility == visibility_private)
    {
      if (complain)
	{
	  char buf[OVERLOAD_MAX_LEN];
	  basetype = TREE_TYPE (TREE_TYPE (classname));
	  hack_function_decl (buf, basetype, function, 0);
	  error (TREE_PRIVATE (field)
		 ? "%s `%s' is private"
		 : "%s `%s' is from private base class",
		 name_kind, buf);
	}
      return error_mark_node;
    }
  else if (visibility == visibility_protected)
    abort ();

 found_and_ok:

  fntype = TREE_TYPE (function);
  if (TREE_CODE (fntype) == POINTER_TYPE)
    fntype = TREE_TYPE (fntype);
  if (TREE_CODE (fntype) == MEMBER_TYPE)
    fntype = TREE_TYPE (fntype);

  value_type = TREE_TYPE (fntype) ? TREE_TYPE (fntype) : void_type_node;

  /* We do not pass FUNCTION into `actualparameterlist', because by
     now everything should be ok.  If not, then we have a serious error.  */
  parms = tree_cons (NULL_TREE, convert_to_nonzero_pointer (TREE_VALUE (TYPE_ARG_TYPES (fntype)), TREE_VALUE (parms)), actualparameterlist (TREE_CHAIN (TYPE_ARG_TYPES (fntype)), TREE_CHAIN (parms), NULL_TREE));

  /* basetype is the type in which field was actually found.  */
  basetype = DECL_CONTEXT (field);

  /* See if there is a wrapper for this thing.  */
  if (wrap < 0 || name == wrapper_name
      || name == DECL_NAME (TYPE_NAME (basetype)))
    ;
  else if (wrap > 0 || TREE_NEEDS_WRAPPER (basetype))
    {
      if (wrap == 0)
	{
	  wrap = TREE_NEEDS_WRAPPER (basetype);
	  /* If no wrapper specified, wrapper may be virtual.  */
	  complain = 2;
	}

      if (wrap)
	{
	  register int bytecount = get_arglist_len_in_bytes (parms);

	  if (!all_virtual && TREE_CODE (function) == FUNCTION_DECL)
	    parm = build_unary_op (ADDR_EXPR, function, 0);
	  else
	    {
	      fntype = build_pointer_type (build_member_type (basetype, fntype));
	      parm = build (NOP_EXPR, fntype, DECL_VINDEX (field));
	    }
	  parms = tree_cons (NULL_TREE, build_int_2 (bytecount, 0),
			     tree_cons (NULL_TREE, parm, TREE_CHAIN (parms)));

	  result = build_classfn_ref (instance, wrapper_name, parms, 1, complain);
#if 0
	  /* Do this if we want the result of operator->() to inherit
	     the type of the function it is subbing for.  */
	  if (result != error_mark_node)
	    TREE_TYPE (result) = value_type;
#endif
	  return result;
	}
    }
  /* Constructors do not overload method calls.  */
  else if (TREE_HAS_METHOD_CALL_OVERLOADED (basetype)
	   && name != DECL_NAME (TYPE_NAME (basetype))
	   && (TREE_CODE (function) != FUNCTION_DECL
	       || strncmp (IDENTIFIER_POINTER (DECL_NAME (function)),
			   "op$method_ref", 13))
	   && (may_be_remote (basetype) || instance != C_C_D))
    {
      register int bytecount = 0;

      for (parm = parms; parm; parm = TREE_CHAIN (parm))
	{
	  register tree pval = TREE_VALUE (parm);
	  register int used, size;

	  if (TREE_CODE (pval) == ERROR_MARK)
	    continue;
	  else if (TYPE_MODE (TREE_TYPE (pval)) != BLKmode)
	    {
	      used = size = GET_MODE_SIZE (TYPE_MODE (TREE_TYPE (pval)));
	      size = PUSH_ROUNDING (size);
	      used = (((size + PARM_BOUNDARY / BITS_PER_UNIT - 1)
		       / (PARM_BOUNDARY / BITS_PER_UNIT))
		      * (PARM_BOUNDARY / BITS_PER_UNIT));
	    }
	  else
	    {
	      register tree size = size_in_bytes (TREE_TYPE (pval));
	      register tree used_t = convert_units (convert_units (size, BITS_PER_UNIT, PARM_BOUNDARY),
						    PARM_BOUNDARY, BITS_PER_UNIT);
	      used = TREE_INT_CST_LOW (used_t);
	    }
	  bytecount += used;
	}
      instance = build_indirect_ref (TREE_VALUE (parms));
      parms = tree_cons (NULL_TREE, build_int_2 (bytecount, 0),
			 TREE_CHAIN (parms));
      if (!all_virtual && TREE_CODE (function) == FUNCTION_DECL)
	result = build_opfncall (METHOD_REF, instance,
				 build_unary_op (ADDR_EXPR, function, 0),
				 parms);
      else
	result = build_opfncall (METHOD_REF, instance,
				 DECL_VINDEX (field), parms);
      if (result == NULL_TREE)
	{
	  error ("could not overload `operator->()(...)' (compiler error)");
	  return error_mark_node;
	}
#if 0
      /* Do this if we want the result of operator->() to inherit
	 the type of the function it is subbing for.  */
      TREE_TYPE (result) = value_type;
#endif
      return result;
    }

  if (TREE_INLINE (function) && TREE_CODE (function) == FUNCTION_DECL)
    function = build (ADDR_EXPR, build_pointer_type (TREE_TYPE (function)),
		      function);
  else function = default_conversion (function);

  result =
    build_nt (CALL_EXPR, function, parms, NULL_TREE);

  if (TREE_OPERAND (result, 1) == error_mark_node)
    abort ();

  TREE_TYPE (result) = value_type;
  TREE_VOLATILE (result) = 1;
  return result;
}

void
init_class_processing ()
{
  current_class_size = 10;
  current_class_base = (tree *)xmalloc(current_class_size * sizeof (tree));
  current_class_stack = current_class_base;
}

/* Set current scope to NAME. CODE tells us if this is a
   STRUCT, UNION, or ENUM environment.

   NAME may end up being NULL_TREE if this is an anonymous or
   late-bound struct (as in "struct { ... } foo;")  */

/* Set global variables CURRENT_CLASS_NAME and CURRENT_CLASS_TYPE to
   appropriate values, found by looking up the type definition of
   NAME (as a CODE).

   if MODIFY is non-zero, We set IDENTIFIER_CLASS_VALUE's of names
   which can be seen locally to the class. They are shadowed by
   any subsequent local declaration (including parameter names).

   So that we may avoid calls to lookup_name, we cache the TYPE_DECL
   in the TREE_TYPE field of the name.

   For multiple inheritance, we perform a two-pass depth-first search
   of the type lattice.  The first pass performs a pre-order search,
   marking types after the type has had its fields installed in
   the appropriate IDENTIFIER_CLASS_VALUE slot.  The second pass merely
   unmarks the marked types.  If a field or member function name
   appears in an ambiguous way, the IDENTIFIER_CLASS_VALUE of
   that name becomes `error_mark_node'.  */

void
pushclass (type, modify)
     tree type;
     int modify;
{
  tree tmp;
  tree fields, field;

  *current_class_stack++ = current_class_name;
  if (current_class_stack >= current_class_base + current_class_size)
    {
      current_class_base =
	(tree *)xrealloc (current_class_base, current_class_size + 10);
      current_class_stack = current_class_base + current_class_size;
      current_class_size += 10;
    }

  type = TYPE_MAIN_VARIANT (type);
  current_class_name = DECL_NAME (TYPE_NAME (type));
  current_class_type = type;

  type = build_pointer_type (type);

  if (modify)
    {
      build_mi_matrix (current_class_type);
      push_class_decls (current_class_type);
      free_mi_matrix ();
    }
}
  
/* Get out of the current class scope. If we were in a class scope
   previously, that is the one popped to.  The flag MODIFY tells
   whether the current scope declarations needs to be modified
   as a result of popping to the new scope.  */
void
popclass (modify)
     int modify;
{
  tree t, type;
  tree fields;

  type = current_class_type;
  if (TREE_USES_MULTIPLE_INHERITANCE (type))
    abort ();

  if (modify)
    {
      pop_class_decls (type);
    }

  t = *--current_class_stack;

  if (t)
    {
      current_vtable_decl = DECL_VTBL_PTR (t);
      t = TREE_TYPE (t);
      current_class_type = TREE_TYPE (t);
      current_class_name = DECL_NAME (t);
      current_class_decl = lookup_name (get_identifier (THIS_NAME));
      if (current_class_decl)
	{
	  if (TREE_CODE (TREE_TYPE (current_class_decl)) == POINTER_TYPE)
	    C_C_D = build (INDIRECT_REF, current_class_type, current_class_decl);
	  else
	    C_C_D = current_class_decl;
	}
      else C_C_D = NULL_TREE;
    }
  else
    {
      current_class_type = NULL_TREE;
      current_class_name = NULL_TREE;
      current_class_decl = NULL_TREE;
      current_vtable_decl = NULL_TREE;
      C_C_D = NULL_TREE;
    }
}

/* This function will instantiate the type of the expression given
   in RHS to match the type of LHSTYPE.  If LHSTYPE is NULL_TREE,
   or other errors exist, the TREE_TYPE of RHS will be ERROR_MARK_NODE.

   This function is used in build_modify_expr, actualparameterlist,
   build_c_cast, and compute_conversion_costs.

   @@ Dealing with overloaded functions (not mere component refs)
   @@ has made this function exceedingly complex.  Perhaps it is
   @@ time to rethink it.  */
void
instantiate_type (lhstype, rhs)
     tree lhstype, rhs;
{
  if (TREE_CODE (lhstype) == UNKNOWN_TYPE)
    {
      error ("not enough type information");
      TREE_TYPE (rhs) = error_mark_node;
      return;
    }
  if (TREE_TYPE (rhs) != unknown_type_node)
    return;

  /* Cannot work on non-function types.  */
  if (TREE_CODE (lhstype) != POINTER_TYPE
      || TREE_CODE (TREE_TYPE (lhstype)) != FUNCTION_TYPE)
    return;

  /* This should really only be used when attempting to distinguish
     what sort of a pointer to function we have.  For now, any
     arithmethic operation which is not supported on pointers
     is rejected as an error.  */
  TREE_TYPE (rhs) = lhstype;
  switch (TREE_CODE (rhs))
    {

    case OP_EXPR:
    case TYPE_EXPR:
    case SAVE_EXPR:
    case CONSTRUCTOR:
    case BUFFER_REF:
      abort ();
      return;

    case INDIRECT_REF:
    case ARRAY_REF:
      lhstype = build_pointer_type (lhstype);
      if (TREE_CODE (TREE_OPERAND (rhs, 0)) == OP_EXPR)
	TREE_OPERAND (rhs, 0)
	  = build_instantiated_decl (lhstype, TREE_OPERAND (rhs, 0));
      else if (TREE_CODE (TREE_OPERAND (rhs, 0)) == TREE_LIST)
	{
	  tree new_rhs = build_tree_list (NULL_TREE, TREE_OPERAND (rhs, 0));
	  instantiate_type (lhstype, new_rhs);
	  if (TREE_TYPE (new_rhs) != error_mark_node)
	    TREE_OPERAND (rhs, 0) = TREE_VALUE (new_rhs);
	  else
	    TREE_OPERAND (rhs, 0) = error_mark_node;
	}
      else
	instantiate_type (lhstype, TREE_OPERAND (rhs, 0));
      return;

    case NOP_EXPR:
      if (TREE_CODE (TREE_OPERAND (rhs, 0)) == OP_EXPR)
	TREE_OPERAND (rhs, 0)
	  = build_instantiated_decl (lhstype, TREE_OPERAND (rhs, 0));
      else if (TREE_CODE (TREE_OPERAND (rhs, 0)) == TREE_LIST)
	{
	  tree new_rhs = build_tree_list (NULL_TREE, TREE_OPERAND (rhs, 0));
	  instantiate_type (lhstype, new_rhs);
	  if (TREE_TYPE (new_rhs) != error_mark_node)
	    TREE_OPERAND (rhs, 0) = TREE_VALUE (new_rhs);
	  else
	    TREE_OPERAND (rhs, 0) = error_mark_node;
	}
      else
	instantiate_type (lhstype, TREE_OPERAND (rhs, 0));
      return;

    case COMPONENT_REF:
      {
	tree field = TREE_OPERAND (rhs, 1);
	if (TREE_CODE (field) != FIELD_DECL)
	  abort ();

	/* First look for an exact match  */
	lhstype = TREE_TYPE (lhstype);
	TREE_TYPE (rhs) = lhstype;
	while (field && TREE_TYPE (TREE_TYPE (field)) != lhstype)
	  field = TREE_CHAIN (field);
	if (field)
	  {
	    TREE_OPERAND (rhs, 1) = field;
	    return;
	  }

	/* No exact match found, look for a compatible function.  */
	field = TREE_OPERAND (rhs, 1);
	while (field && ! comp_target_types (TREE_TYPE (TREE_TYPE (field)), lhstype))
	  field = TREE_CHAIN (field);
	if (field)
	  {
	    TREE_OPERAND (rhs, 1) = field;
	    field = TREE_CHAIN (field);
	    while (field && ! comp_target_types (TREE_TYPE (TREE_TYPE (field)), lhstype))
	      field = TREE_CHAIN (field);
	    if (field)
	      error ("ambiguous type instantiation requested");
	  }
	else
	  {
	    error ("no appropriate type instantiation exists");
	    TREE_TYPE (rhs) = error_mark_node;
	  }
      }
      return;

    case TREE_LIST:
      {
	/* Fake TREE_LIST:  value is real tree_list.  */
	tree elem = TREE_VALUE (rhs);

	/* First look for an exact match  */
	lhstype = TREE_TYPE (lhstype);
	TREE_TYPE (rhs) = lhstype;
	while (elem && TREE_TYPE (TREE_VALUE (elem)) != lhstype)
	  elem = TREE_CHAIN (elem);
	if (elem)
	  {
	    TREE_VALUE (rhs) = TREE_VALUE (elem);
	    return;
	  }

	/* No exact match found, look for a compatible function.  */
	elem = TREE_VALUE (rhs);
	while (elem && ! comp_target_types (TREE_TYPE (TREE_VALUE (elem)), lhstype))
	  elem = TREE_CHAIN (elem);
	if (elem)
	  {
	    tree save_elem = elem;
	    elem = TREE_CHAIN (elem);
	    while (elem && ! comp_target_types (TREE_TYPE (TREE_VALUE (elem)), lhstype))
	      elem = TREE_CHAIN (elem);
	    if (elem)
	      {
		error ("ambiguous type instantiation requested");
		TREE_VALUE (rhs) = save_elem;
	      }
	  }
	else
	  {
	    error ("no appropriate type instantiation exists");
	    TREE_TYPE (rhs) = error_mark_node;
	    TREE_VALUE (rhs) = error_mark_node;
	  }
      }
      return;

    case CALL_EXPR:
      /* This is too hard for now.  */
      abort ();
      return;

    case CONVERT_EXPR:
      /* should have been done in conversion routines.  */
      abort ();
      return;

    case PLUS_EXPR:
    case MINUS_EXPR:
    case COMPOUND_EXPR:
      if (TREE_CODE (TREE_OPERAND (rhs, 0)) == OP_EXPR)
	TREE_OPERAND (rhs, 0)
	  = build_instantiated_decl (lhstype, TREE_OPERAND (rhs, 0));
      else if (TREE_CODE (TREE_OPERAND (rhs, 0)) == TREE_LIST)
	{
	  tree new_rhs = build_tree_list (NULL_TREE, TREE_OPERAND (rhs, 0));
	  instantiate_type (lhstype, new_rhs);
	  if (TREE_TYPE (new_rhs) != error_mark_node)
	    TREE_OPERAND (rhs, 0) = TREE_VALUE (new_rhs);
	  else
	    TREE_OPERAND (rhs, 0) = error_mark_node;
	}
      else
	instantiate_type (lhstype, TREE_OPERAND (rhs, 0));
      if (TREE_CODE (TREE_OPERAND (rhs, 1)) == OP_EXPR)
	TREE_OPERAND (rhs, 1)
	  = build_instantiated_decl (lhstype, TREE_OPERAND (rhs, 1));
      else if (TREE_CODE (TREE_OPERAND (rhs, 1)) == TREE_LIST)
	{
	  tree new_rhs = build_tree_list (NULL_TREE, TREE_OPERAND (rhs, 1));
	  instantiate_type (lhstype, new_rhs);
	  if (TREE_TYPE (new_rhs) != error_mark_node)
	    TREE_OPERAND (rhs, 1) = TREE_VALUE (new_rhs);
	  else
	    TREE_OPERAND (rhs, 1) = error_mark_node;
	}
      else
	instantiate_type (lhstype, TREE_OPERAND (rhs, 1));
      return;

    case MULT_EXPR:
    case TRUNC_DIV_EXPR:
    case FLOOR_DIV_EXPR:
    case CEIL_DIV_EXPR:
    case ROUND_DIV_EXPR:
    case RDIV_EXPR:
    case TRUNC_MOD_EXPR:
    case FLOOR_MOD_EXPR:
    case CEIL_MOD_EXPR:
    case ROUND_MOD_EXPR:
    case FIX_ROUND_EXPR:
    case FIX_FLOOR_EXPR:
    case FIX_CEIL_EXPR:
    case FIX_TRUNC_EXPR:
    case FLOAT_EXPR:
    case NEGATE_EXPR:
    case ABS_EXPR:
    case MAX_EXPR:
    case MIN_EXPR:
    case FFS_EXPR:

    case BIT_AND_EXPR:
    case BIT_IOR_EXPR:
    case BIT_XOR_EXPR:
    case LSHIFT_EXPR:
    case RSHIFT_EXPR:
    case LROTATE_EXPR:
    case RROTATE_EXPR:

    case PREINCREMENT_EXPR:
    case PREDECREMENT_EXPR:
    case POSTINCREMENT_EXPR:
    case POSTDECREMENT_EXPR:
      error ("illegal operation on uninstantiated type");
      TREE_TYPE (rhs) = error_mark_node;
      return;

    case TRUTH_AND_EXPR:
    case TRUTH_OR_EXPR:
    case LT_EXPR:
    case LE_EXPR:
    case GT_EXPR:
    case GE_EXPR:
    case EQ_EXPR:
    case NE_EXPR:
    case TRUTH_ANDIF_EXPR:
    case TRUTH_ORIF_EXPR:
    case TRUTH_NOT_EXPR:
      error ("not enough type information");
      TREE_TYPE (rhs) = error_mark_node;
      return;

    case COND_EXPR:
      if (TREE_TYPE (TREE_OPERAND (rhs, 0)) == unknown_type_node)
	{
	  error ("not enough type information");
	  TREE_TYPE (rhs) = error_mark_node;
	  return;
	}
      if (TREE_CODE (TREE_OPERAND (rhs, 1)) == OP_EXPR)
	TREE_OPERAND (rhs, 1)
	  = build_instantiated_decl (lhstype, TREE_OPERAND (rhs, 1));
      else if (TREE_CODE (TREE_OPERAND (rhs, 1)) == TREE_LIST)
	{
	  tree new_rhs = build_tree_list (NULL_TREE, TREE_OPERAND (rhs, 1));
	  instantiate_type (lhstype, new_rhs);
	  if (TREE_TYPE (new_rhs) != error_mark_node)
	    TREE_OPERAND (rhs, 1) = TREE_VALUE (new_rhs);
	  else
	    TREE_OPERAND (rhs, 1) = error_mark_node;
	}
      else
	instantiate_type (lhstype, TREE_OPERAND (rhs, 1));
      if (TREE_CODE (TREE_OPERAND (rhs, 2)) == OP_EXPR)
	TREE_OPERAND (rhs, 2)
	  = build_instantiated_decl (lhstype, TREE_OPERAND (rhs, 2));
      else if (TREE_CODE (TREE_OPERAND (rhs, 2)) == TREE_LIST)
	{
	  tree new_rhs = build_tree_list (NULL_TREE, TREE_OPERAND (rhs, 2));
	  instantiate_type (lhstype, new_rhs);
	  if (TREE_TYPE (new_rhs) != error_mark_node)
	    TREE_OPERAND (rhs, 2) = TREE_VALUE (new_rhs);
	  else
	    TREE_OPERAND (rhs, 2) = error_mark_node;
	}
      else
	instantiate_type (lhstype, TREE_OPERAND (rhs, 2));
      return;

    case MODIFY_EXPR:
      if (TREE_CODE (TREE_OPERAND (rhs, 1)) == OP_EXPR)
	TREE_OPERAND (rhs, 1)
	  = build_instantiated_decl (lhstype, TREE_OPERAND (rhs, 1));
      else if (TREE_CODE (TREE_OPERAND (rhs, 1)) == TREE_LIST)
	{
	  tree new_rhs = build_tree_list (NULL_TREE, TREE_OPERAND (rhs, 1));
	  instantiate_type (lhstype, new_rhs);
	  if (TREE_TYPE (new_rhs) != error_mark_node)
	    TREE_OPERAND (rhs, 1) = TREE_VALUE (new_rhs);
	  else
	    TREE_OPERAND (rhs, 1) = error_mark_node;
	}
      else
	instantiate_type (lhstype, TREE_OPERAND (rhs, 1));
      return;
      
    case ADDR_EXPR:
      if (TREE_CODE (TREE_OPERAND (rhs, 0)) == OP_EXPR)
	TREE_OPERAND (rhs, 0)
	  = build_instantiated_decl (TREE_TYPE (lhstype), TREE_OPERAND (rhs, 0));
      else if (TREE_CODE (TREE_OPERAND (rhs, 0)) == TREE_LIST)
	{
	  tree new_rhs = build_tree_list (NULL_TREE, TREE_OPERAND (rhs, 0));
	  instantiate_type (TREE_TYPE (lhstype), new_rhs);
	  if (TREE_TYPE (new_rhs) != error_mark_node)
	    TREE_OPERAND (rhs, 0) = TREE_VALUE (new_rhs);
	  else
	    TREE_OPERAND (rhs, 0) = error_mark_node;
	}
      else
	instantiate_type (TREE_TYPE (lhstype), TREE_OPERAND (rhs, 0));
      return;

    case ENTRY_VALUE_EXPR:
      abort ();

    case ERROR_MARK:
      return;

    default:
      abort ();
    }
}

/* This routine is called when we finally know the type of expression
   we are looking for.  If the operator encoded by EXP can take an
   argument of type TYPE, return the FUNCTION_DECL for that operator.  */
tree
build_instantiated_decl (type, exp)
     tree type, exp;
{
  tree parmtypes, decl, name;

  if (TREE_CODE (exp) != OP_EXPR)
    {
      error ("bad argument to build_instantiated_decl (compiler error)");
      return error_mark_node;
    }
  if (TREE_CODE (type) != POINTER_TYPE
      || TREE_CODE (TREE_TYPE (type)) != FUNCTION_TYPE)
    {
      error ("bad argument list to build_instantiated_decl (possible compiler error)");
      return error_mark_node;
    }


  /* Now we know the type of this function, so overload it.  */
  parmtypes = TYPE_ARG_TYPES (TREE_TYPE (type));
  name = build_operator_fnname (TREE_OPERAND (exp, 0), parmtypes, 0);
  if (name)
    {
      name = do_decl_overload (IDENTIFIER_POINTER (name), parmtypes);
      decl = lookup_name (name);
      if (decl)
	return decl;
      error ("cannot find suitable declaration for `operator %s'",
	     operator_name_string (name));
      return error_mark_node;
    }
  return error_mark_node;
}
