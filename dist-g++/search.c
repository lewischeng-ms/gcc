/* Breadth-first and depth-first routines for
   searching multiple-inheritance lattice for GNU C++.
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
#include "obstack.h"
#include "flags.h"

#define NULL 0

#define obstack_chunk_alloc xmalloc
#define obstack_chunk_free free

extern int xmalloc ();
extern void free ();

void init_search ();

/* Stack of places to restore the search obstack back to.  */
   
struct search_level
{
  /* Pointer back to previous such level.  */
  struct search_level *prev;
  /* First object allocated within this level.  */
  char *base;
  /* First place we start putting classes.  */
  tree *first;
};

struct search_level *search_stack;

static struct obstack search_obstack;

static void
push_search ()
{
  struct search_level tem;

  tem.prev = search_stack;
  tem.base = (char *) obstack_base (&search_obstack);
  search_stack = (struct search_level *) obstack_next_free (&search_obstack);
  obstack_grow (&search_obstack, &tem, sizeof (tem));
  search_stack->first = (tree *) obstack_next_free (&search_obstack);
}

/* Discard a level of search allocation.  */

void
pop_search ()
{
  struct search_level *tem = search_stack;
  search_stack = tem->prev;
  obstack_free (&search_obstack, tem);
}

void init_search ()
{
  obstack_init (&search_obstack);
}

/* Some simple list processing predicates.  */

/* Check whether TYPE is derived from PARENT.
   Return the actual base information if so.  Otherwise return 0.  */
tree
get_base_type (parent, type)
     register tree parent, type;
{
  int head = 0, tail = 0;
  tree rval;

  push_search ();

  parent = CLASSTYPE_MAIN_VARIANT (parent);
  type = CLASSTYPE_MAIN_VARIANT (type);

  while (1)
    {
      int i, n_baselinks = CLASSTYPE_N_BASECLASSES (type);

      /* Process and/or queue base types.  */
      for (i = 1; i <= n_baselinks; i++)
	if (CLASSTYPE_MARKED (CLASSTYPE_BASECLASS (type, i)) == 0)
	  {
	    CLASSTYPE_MARKED (CLASSTYPE_BASECLASS (type, i)) = 1;
	    obstack_grow (&search_obstack, &CLASSTYPE_BASECLASS (type, i), sizeof (tree *));
	    tail++;
	  }

      /* Process head of queue, if one exists.  */
      if (head >= tail)
	{
	  rval = 0;
	  break;
	}


      type = search_stack->first[head++];
      if (CLASSTYPE_MAIN_VARIANT (type) == parent)
	{
	  rval = type;
	  break;
	}
    }
  {
    tree *tp = search_stack->first;
    tree *search_tail = tp + tail;

    while (tp < search_tail)
      {
	CLASSTYPE_MARKED (*tp++) = 0;
      }
  }
  pop_search ();
  return rval;
}

/* Search for a member with name NAME in a multiple inheritance lattice
   specified by TYPE.  If it does not exist, return NULL_TREE.
   If the member is ambiguously referenced, return `error_mark_node'.
   Otherwise, return the FIELD_DECL.  */

/* Do a 1-level search for NAME as a member of TYPE.  The caller
   must figure out whether it has a visible path to this field.
   (Since it is only one level, this is reasonable.)  */
static tree
lookup_field_1 (type, name)
     tree type, name;
{
  register tree field = TYPE_FIELDS (type);

  while (field)
    {
      if (DECL_NAME (field) == name)
	return field;
      field = TREE_CHAIN (field);
    }
  return NULL_TREE;
}

/* Compute the visibility of FIELD.  This is done by computing
   the visibility available to each type in BASETYPES (which comes
   as a list of types in reverse order).  The first one which
   defines a visibility defines the visibility for the field.
   Otherwise, the visibility of the field is that which
   occurs normally.

   Uses global variables CURRENT_CLASS_TYPE and
   CURRENT_FUNCTION_DECL to use friend relationships
   if necessary.
   VISIBILITY may come in as something other than VISIBILITY_DEFAULT.
   In that case, unless FIELD has special visibility for BASETYPE
   or BASETYPE is a friend of CURRENT_CLASS_TYPE, it may override
   what FIELD is willing to offer.

   This will be static when lookup_fnfield comes into this file.  */

enum visibility_type
compute_visibility (basetypes, field)
     tree basetypes, field;
{
  enum visibility_type visibility = visibility_public;
  tree types, type;

  /* Virtual function tables are never private.
     But we should know that we are looking for this,
     and not even try to hide it.  */
  if (VFIELD_NAME_P (DECL_NAME (field)))
    abort ();

  /* Make this special case fast.  */
  if (TREE_CHAIN (basetypes) == NULL_TREE)
    {
      /* Special case: The object is being used in its natural type.  */
      if (TREE_PRIVATE (field) == 0)
	{
	  if (TREE_PROTECTED (field) == 0)
	    return visibility_public;
	  if (current_class_type
	      && get_base_type (DECL_CONTEXT (field), current_class_type))
	    return visibility_public;
	}
      else if (current_class_type == DECL_CONTEXT (field))
	return visibility_public;
    }
  else
    {
      /* must reverse more than one element */
      basetypes = nreverse (basetypes);
    }

  types = basetypes;

  while (types)
    {
      tree member;
      type = CLASSTYPE_MAIN_VARIANT (TREE_VALUE (types));

      if (current_class_type == type
	  || is_friend (current_function_decl, type))
	{
	  nreverse (basetypes);
	  return visibility_public;
	}

      member = purpose_member (type, DECL_VISIBILITY (field));
      if (member)
	{
	  nreverse (basetypes);
	  return (enum visibility_type)TREE_VALUE (member);
	}

      types = TREE_CHAIN (types);
      if (types && TREE_PURPOSE (types) == NULL_TREE)
	visibility = visibility_private;
    }

  /* No special visibilities apply.  Use normal rules.  */
  nreverse (basetypes);

  if (visibility == visibility_private
      && current_class_type != NULL_TREE)
    {
      /* See if the field isn't a public member of
	 a private base class.  */
      int i, n_baselinks = CLASSTYPE_N_BASECLASSES (current_class_type);

      type = DECL_CONTEXT (field);
      for (i = 1; i <= n_baselinks; i++)
	if (CLASSTYPE_MAIN_VARIANT (CLASSTYPE_BASECLASS (current_class_type, i)) == type)
	  {
	    if (! TREE_PRIVATE (field))
	      visibility = visibility_public;
	    break;
	  }

      if (visibility == visibility_private)
	{
	  if (TREE_PROTECTED (field))
	    {
	      if (get_base_type (type, current_class_type))
		visibility = visibility_public;
	      else
		visibility = visibility_protected;
	    }
	}
    }

  return visibility;
}

tree
lookup_field (basetype, name, protect)
     register tree basetype, name;
     int protect;
{
  int head = 0, tail = 0;
  tree type, rval;
  tree basetypes = build_tree_list (NULL_TREE, basetype);
  enum visibility_type this_v = visibility_default;

  rval = lookup_field_1 (basetype, name);
  if (rval)
    {
      if (protect)
	{
	  if (TREE_PRIVATE (rval) || TREE_PROTECTED (rval))
	    this_v = compute_visibility (basetypes, rval);
	  if (this_v == visibility_private)
	    {
	      error ("field `%s' is a private member of class `%s'",
		     IDENTIFIER_POINTER (name),
		     TYPE_NAME_STRING (basetype));
	      rval = error_mark_node;
	    }
	  else if (this_v == visibility_protected)
	    {
	      error ("field `%s' is a protected member of class `%s'",
		     IDENTIFIER_POINTER (name),
		     TYPE_NAME_STRING (basetype));
	      rval = error_mark_node;
	    }
	}
      return rval;
    }

  type = CLASSTYPE_MAIN_VARIANT (basetype);

  push_search ();

  while (1)
    {
      int i, n_baselinks = CLASSTYPE_N_BASECLASSES (type);

      /* Process and/or queue base types.  */
      for (i = 1; i <= n_baselinks; i++)
	{
	  if (CLASSTYPE_MARKED2 (CLASSTYPE_BASECLASS (type, i)) == 0)
	    {
	      tree btypes = basetypes;

	      CLASSTYPE_MARKED2 (CLASSTYPE_BASECLASS (type, i)) = 1;
	      obstack_grow (&search_obstack, &CLASSTYPE_BASECLASS (type, i), sizeof (tree *));
	      btypes = tree_cons (CLASSTYPE_VIA_PUBLIC (type, i),
				  CLASSTYPE_BASECLASS (type, i), basetypes);
	      obstack_grow (&search_obstack, &btypes, sizeof (tree *));
	      tail += 2;
	    }
	}

      /* Process head of queue, if one exists.  */
      if (head >= tail)
	break;

      type = search_stack->first[head++];
      basetypes = search_stack->first[head++];

      if (rval)
	{
	  if (DECL_CONTEXT (rval) == type)
	    ;
	  else if (CLASSTYPE_MAIN_VARIANT (DECL_CONTEXT (rval))
		   == CLASSTYPE_MAIN_VARIANT (type))
	    {
	      error ("member `%s' belongs to distinct base classes `%s'",
		     IDENTIFIER_POINTER (name),
		     TYPE_NAME_STRING (type));
	      rval = error_mark_node;
	      break;
	    }
	  else
	    {
	      tree nval = lookup_field_1 (type, name);
	      if (nval)
		{
		  enum visibility_type new_v;

		  if (get_base_type (DECL_CONTEXT (rval), type) == 0)
		    {
		      error ("request for member `%s' is ambiguous",
			     IDENTIFIER_POINTER (name));
		      rval = error_mark_node;
		      break;
		    }

		  if (protect)
		    new_v = compute_visibility (basetypes, nval);
		  if (protect && this_v != new_v)
		    {
		      error ("conflicting visibilities to member `%s'",
			     IDENTIFIER_POINTER (name));
		      rval = error_mark_node;
		      break;
		    }

		  /* Which do we want?  NVAL or RVAL?  */
		  abort ();
		}
	    }
	}
      else
	{
	  rval = lookup_field_1 (type, name);
	  if (rval && protect)
	    this_v = compute_visibility (basetypes, rval);
	}
    }
  {
    tree *tp = search_stack->first;
    tree *search_tail = tp + tail;

    if (protect && rval
	&& rval != error_mark_node
	&& DECL_VISIBILITY (rval))
      {
	while (tp < search_tail)
	  {
	    /* If is possible for one of the derived types on the
	       path to have defined special visibility for this
	       field.  Look for such declarations and report an
	       error if a conflict is found.  */
	    enum visibility_type new_v;

	    if (this_v != visibility_default)
	      new_v = compute_visibility (tp[1], tp[0], rval);
	    if (this_v != visibility_default && new_v != this_v)
	      {
		error ("conflicting visibilities to member `%s'",
		       IDENTIFIER_POINTER (name));
		this_v = visibility_default;
		rval = error_mark_node;
	      }
	    CLASSTYPE_MARKED2 (*tp++) = 0;
	    tp++;
	  }
      }
    else
      {
	while (tp < search_tail)
	  {
	    CLASSTYPE_MARKED2 (*tp++) = 0;
	    tp++;
	  }
      }
  }
  pop_search ();

 found:
  if (rval != error_mark_node)
    {
      if (this_v == visibility_private)
	{
	  error (TREE_PRIVATE (rval)
		 ? "member `%s' is private"
		 : "member `%s' is from private base class",
		 IDENTIFIER_POINTER (name));
	  rval = error_mark_node;
	}
      else if (this_v == visibility_protected)
	{
	  error ("member `%s' is protected", IDENTIFIER_POINTER (name));
	  rval = error_mark_node;
	}
    }
  return rval;
}

/* BREADTH-FIRST SEARCH ROUTINES.  */
/* Search a multiple inheritance hierarchy for some base class needing a constructor.
   Algorithm is a breadth-first search.

   TYPE is an aggregate type, possibly in a multiple-inheritance hierarchy.
   TESTFN is a function, which, if true, means that our condition has been met,
   and its return value should be returned.
   QFN, if non-NULL, is a predicate dictating whether the type should
   even be queued.  */

int
breadth_first_search (type, testfn, qfn)
     tree type;
     int (*testfn)();
     int (*qfn)();
{
  int head = 0, tail = 0;
  int rval = 0;

  push_search ();

  while (1)
    {
      int n_baselinks = CLASSTYPE_N_BASECLASSES (type);
      int i;

      /* Process and/or queue base types.  */
      for (i = 1; i <= n_baselinks; i++)
	if (CLASSTYPE_MARKED (CLASSTYPE_BASECLASS (type, i)) == 0
	    && (qfn == 0 || (*qfn) (CLASSTYPE_BASECLASS (type, i))))
	  {
	    CLASSTYPE_MARKED (CLASSTYPE_BASECLASS (type, i)) = 1;
	    obstack_grow (&search_obstack, &CLASSTYPE_BASECLASS (type, i), sizeof (tree*));
	    tail++;
	  }

      /* Process head of queue, if one exists.  */
      if (head >= tail)
	{
	  rval = 0;
	  break;
	}

      type = search_stack->first[head++];
      if (rval = (*testfn) (type))
	break;
    }
  {
    tree *tp = search_stack->first;
    tree *search_tail = tp + tail;
    while (tp < search_tail)
      {
	CLASSTYPE_MARKED (*tp++) = 0;
      }
  }

  pop_search ();
  return rval;
}

/* Functions to use in breadth first searches.  */

int tree_needs_constructor_p (type)
     tree type;
{
  return TREE_NEEDS_CONSTRUCTOR (type);
}

tree tree_has_virtual_destructor_p (type)
     tree type;
{
  if (TREE_HAS_DESTRUCTOR (type)
      && TREE_VIRTUAL (TREE_VALUE (TYPE_FN_FIELDS (type))))
    return type;
  return 0;
}

int tree_has_any_destructor_p (type)
     tree type;
{
  return TREE_NEEDS_DESTRUCTOR (type);
}

static tree declarator;

tree tree_virtuals_named_this (type)
     tree type;
{
  tree fields = lookup_fnfields (type, declarator);
  if (fields && TREE_VIRTUAL (TREE_VALUE (fields)))
    return fields;
  return 0;
}

typedef tree (*pft)();
typedef int (*pfi)();

pft tree_has_virtual_named (decl)
     tree decl;
{
  declarator = decl;
  return tree_virtuals_named_this;
}

int
get_n_fnfield_sources (type, name)
{
  return 1;
}

int
get_n_field_sources (type, name)
{
  return 1;
}

/* DEPTH-FIRST SEARCH ROUTINES.  */

/* Assign unique numbers to _CLASSTYPE members of the lattice
   specified by TYPE.  The root nodes are marked first; the nodes
   are marked depth-fisrt, left-right.  */

static int cid;

/* Matrix implementing a relation from CLASSTYPE X CLASSTYPE => INT.
   Relation yields 1 if C1 <= C2, 0 otherwise.  */
static char *mi_matrix;

/* Type for which this matrix is defined.  */
static tree mi_type;

/* Size of the matrix for indexing purposes.  */
static int mi_size;

#define DERIVES_FROM(C1, C2) \
  ((mi_matrix+mi_size*(CLASSTYPE_CID (C1)-1))[CLASSTYPE_CID (C2)-1])

/* The main function which implements depth first search.  */
static void
dfs_walk (type, fn, qfn)
     tree type;
     void (*fn)();
     int (*qfn)();
{
  int i, n_baselinks = CLASSTYPE_N_BASECLASSES (type);

  for (i = 1; i <= n_baselinks; i++)
    if ((*qfn)(CLASSTYPE_BASECLASS (type, i)))
      {
	dfs_walk (CLASSTYPE_BASECLASS (type, i), fn, qfn);
      }

  fn (type);
}

/* Predicate functions which serve for dfs_walk.  */
static int numberedp (type) tree type;
{ return CLASSTYPE_CID (type); }
static int unnumberedp (type) tree type;
{ return CLASSTYPE_CID (type) == 0; }

static int markedp (type) tree type;
{ return CLASSTYPE_MARKED (type); }
static int unmarkedp (type) tree type;
{ return CLASSTYPE_MARKED (type) == 0; }
static int marked2p (type) tree type;
{ return CLASSTYPE_MARKED2 (type); }
static int unmarked2p (type) tree type;
{ return CLASSTYPE_MARKED2 (type) == 0; }

/* The worker functions for `dfs_walk'.  These do not need to
   test anything (vis a vis marking) if they are paired with
   a predicate function (above).  */

/* Assign each type within the lattice a number which is unique
   in the lattice.  The first number assigned is 1.  */

static void
dfs_number (type)
     tree type;
{
  CLASSTYPE_CID (type) = ++cid;
}

static void
dfs_unnumber (type)
     tree type;
{
  CLASSTYPE_CID (type) = 0;
}

static void
dfs_mark (type) tree type;
{ CLASSTYPE_MARKED (type) = 1; }

static void
dfs_unmark (type) tree type;
{ CLASSTYPE_MARKED (type) = 0; }

static void
dfs_mark2 (type) tree type;
{ CLASSTYPE_MARKED2 (type) = 1; }

static void
dfs_unmark2 (type) tree type;
{ CLASSTYPE_MARKED2 (type) = 0; }

static void
dfs_record_inheritance (type)
     tree type;
{
  int i, n_baselinks = CLASSTYPE_N_BASECLASSES (type);

  for (i = 1; i <= n_baselinks; i++)
    DERIVES_FROM (CLASSTYPE_BASECLASS (type, i), type) = 1;

  CLASSTYPE_MARKED (type) = 1;
}

/* Given a _CLASSTYPE node in a multiple inheritance lattice,
   convert the lattice into a simple relation such that,
   given to CIDs, C1 and C2, one can determine if C1 <= C2
   or C2 <= C1 or C1 <> C2.

   Once constructed, we walk the lattice depth fisrt,
   applying various functions to elements as they are encountered.  */

void
build_mi_matrix (type)
     tree type;
{
  cid = 0;
  mi_size = CLASSTYPE_N_SUPERCLASSES (type);
  mi_matrix = (char *)malloc (mi_size * mi_size);
  mi_type = type;
  bzero (mi_matrix, mi_size * mi_size);
  dfs_walk (type, dfs_number, unnumberedp);
  dfs_walk (type, dfs_record_inheritance, unmarkedp);
  dfs_walk (type, dfs_unmark, markedp);
}

void
free_mi_matrix ()
{
  dfs_walk (mi_type, dfs_unnumber, numberedp);
  free (mi_matrix);
  mi_size = 0;
  cid = 0;
}

/* Subroutines of push_class_decls ().  */

/* Add the instance variables which this class contributed to the
   current class binding contour.  When a redefinition occurs,
   if the redefinition is strictly within a single inheritance path,
   we just overwrite (in the case of a data field) or
   cons (in the case of a member function) the old declaration with
   the new.  If the fields are not within a single inheritance path,
   we must cons them in either case.  */

static void
dfs_pushdecls (type)
     tree type;
{
  tree fields;

  for (fields = TYPE_FIELDS (type); fields; fields = TREE_CHAIN (fields))
    {
      if (DECL_NAME (fields))
	{
	  tree value = IDENTIFIER_CLASS_VALUE (DECL_NAME (fields));
	  if (value)
	    {
	      /* Possible ambiguity.  If its defining type(s)
		 is (are all) derived from us, no problem.  */

	      if (TREE_CODE (value) == FIELD_DECL)
		value = DERIVES_FROM (DECL_CONTEXT (value), type)
		  ? fields : tree_cons (NULL_TREE, fields,
					build_tree_list (NULL_TREE, value));
	      else
		{
		  /* All children may derive from us.  */
		  int i, n_children = list_length (value);

		  for (i = 0; i < n_children; i++)
		    if (! DERIVES_FROM (DECL_CONTEXT (TREE_VALUE (value)), type))
		      break;

		  value = (i == n_children) ? fields : tree_cons (NULL_TREE, fields, value);
		}

	      /* Mark this as a potentially ambiguous member.  */
	      if (TREE_CODE (value) == TREE_LIST)
		{
		  /* Leaving TREE_TYPE blank is intentional.
		     We cannot use `error_mark_node' (lookup_name)
		     or `unknown_type_node' (all member functions use this).  */
		  TREE_NONLOCAL (value) = 1;
		}

	      IDENTIFIER_CLASS_VALUE (DECL_NAME (fields)) = value;
	    }
	  else IDENTIFIER_CLASS_VALUE (DECL_NAME (fields)) = fields;
	}
    }

  fields = TYPE_FN_FIELDS (type);

  /* Farm out constructors and destructors.  */

  if (TREE_HAS_CONSTRUCTOR (type))
    fields = TREE_CHAIN (fields);

  /* This does not work for multiple inheritance yet.  */
  while (fields)
    {
      /* This will cause lookup_name to return a pointer
	 to the tree_list of possible methods of this name.
	 If the order is a problem, we can nreverse them.  */
      tree tmp;
      tree old = IDENTIFIER_CLASS_VALUE (TREE_PURPOSE (fields));

      if (old && TREE_CODE (old) == TREE_LIST)
	tmp = tree_cons (TREE_PURPOSE (fields), fields, old);
      else
	{
	  if (old)
	    warning ("shadowing data field `%s' with member function",
		     IDENTIFIER_POINTER (TREE_PURPOSE (fields)));
	  tmp = build_tree_list (TREE_PURPOSE (fields), fields);
	}

      TREE_TYPE (tmp) = unknown_type_node;
      TREE_OVERLOADED (tmp) = TREE_OVERLOADED (fields);
      IDENTIFIER_CLASS_VALUE (TREE_PURPOSE (fields)) = tmp;
      fields = TREE_CHAIN (fields);
    }

  CLASSTYPE_MARKED (type) = 1;
}

/* Consolidate unique (by name) member functions.  */
static void
dfs_compress_decls (type)
     tree type;
{
  tree fields = TYPE_FN_FIELDS (type);

  /* Farm out constructors and destructors.  */
  if (TREE_HAS_CONSTRUCTOR (type))
    fields = TREE_CHAIN (fields);

  while (fields)
    {
      tree tmp = IDENTIFIER_CLASS_VALUE (TREE_PURPOSE (fields));
      if (TREE_CHAIN (tmp) == NULL_TREE
	  && TREE_VALUE (TREE_VALUE (tmp))
	  && TREE_CHAIN (TREE_VALUE (TREE_VALUE (tmp))) == NULL_TREE)
	{
	  IDENTIFIER_CLASS_VALUE (TREE_PURPOSE (fields))
	    = TREE_TYPE (TREE_VALUE (TREE_VALUE (tmp)));
	}
      fields = TREE_CHAIN (fields);
    }

  CLASSTYPE_MARKED (type) = 0;
}

/* When entering the scope of a class, we cache all of the
   fields that that class provides within its inheritance
   lattice.  Where ambiguities result, we mark them
   with `error_mark_node' so that if they are encountered
   without explicit qualification, we can emit an error
   message.  */
void
push_class_decls (type)
     tree type;
{
#if 0
  tree tags = TYPE_TAGS (type);

  while (tags)
    {
      tree code_type_node;
      tree tag;

      switch (TREE_CODE (TREE_VALUE (tags)))
	{
	case ENUMERAL_TYPE:
	  code_type_node = enum_type_node;
	  break;
	case RECORD_TYPE:
	  code_type_node = record_type_node;
	  break;
	case CLASS_TYPE:
	  code_type_node = class_type_node;
	  break;
	case UNION_TYPE:
	  code_type_node = union_type_node;
	  break;
	default:
	  abort ();
	}
      tag = xref_tag (code_type_node, TREE_PURPOSE (tags),
		      CLASSTYPE_BASECLASS (TREE_VALUE (tags), 1));
      pushdecl (build_decl (TYPE_DECL, TREE_PURPOSE (tags), TREE_VALUE (tags)));
    }
#endif

  /* Push class fields into CLASS_VALUE scope, and mark.  */
  dfs_walk (type, dfs_pushdecls, unmarkedp);

  /* Compress fields which have only a single entry
     by a given name, and unmark.  */
  dfs_walk (type, dfs_compress_decls, markedp);
}

static void
dfs_popdecls (type)
     tree type;
{
  tree fields = TYPE_FIELDS (type);

  while (fields)
    {
      if (DECL_NAME (fields))
	IDENTIFIER_CLASS_VALUE (DECL_NAME (fields)) = NULL_TREE;
      fields = TREE_CHAIN (fields);
    }
  for (fields = TYPE_FN_FIELDS (type); fields; fields = TREE_CHAIN (fields))
    {
      IDENTIFIER_CLASS_VALUE (TREE_PURPOSE (fields)) = NULL_TREE;
    }

  CLASSTYPE_MARKED (type) = 1;
}

void
pop_class_decls (type)
     tree type;
{
  /* Clear out the IDENTIFIER_CLASS_VALUE which this
     class may have occupied, and mark.  */
  dfs_walk (type, dfs_popdecls, unmarkedp);

  /* Unmark.  */
  dfs_walk (type, dfs_unmark, markedp);
}
