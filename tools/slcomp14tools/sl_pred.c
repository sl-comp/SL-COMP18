/**************************************************************************/
/*                                                                        */
/*  Compiler for SMTLIB2 frmat for Separation Logic                       */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 3.                                                */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 3.                  */
/*  for more details (enclosed in the file LICENSE).                      */
/*                                                                        */
/**************************************************************************/

/**
 * Predicates for SL.
 */

#include "sl_pred.h"

SL_VECTOR_DEFINE (sl_pred_case_array, sl_pred_case_t *);

SL_VECTOR_DEFINE (sl_pred_array, sl_pred_t *);

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

sl_pred_array *preds_array;

void
sl_pred_init ()
{
  preds_array = sl_pred_array_new ();
  sl_pred_array_reserve (preds_array, 4);
}


/* ====================================================================== */
/* Constructors/Destructors */
/* ====================================================================== */

sl_pred_binding_t *
sl_pred_binding_new (void)
{
  sl_pred_binding_t *pdef =
    (sl_pred_binding_t *) malloc (sizeof (sl_pred_binding_t));
  pdef->pargs = 0;
  pdef->args = NULL;
  pdef->argc = 0;
  pdef->cases = NULL;
  return pdef;
}


void
sl_pred_binding_delete (sl_pred_binding_t * pdef)
{
  if (pdef == NULL)
    return;
  if (pdef->args != NULL)
    sl_var_array_delete (pdef->args);
  if (pdef->cases != NULL)
    sl_pred_case_array_delete (pdef->cases);
  free (pdef);
}

  /* ====================================================================== */
  /* Predicate cases */
  /* ====================================================================== */

sl_pred_case_t *
sl_pred_case_new (uint_t argc)
{
  sl_pred_case_t *ret = (sl_pred_case_t *) malloc (sizeof (sl_pred_case_t));

  ret->lvars = NULL;
  ret->argc = argc;
  ret->is_precise = true;
  ret->pure = sl_pure_array_new ();
  ret->space = sl_space_array_new ();
  return ret;
}

void
sl_pred_case_array_add (sl_pred_case_array * pcases, sl_pred_case_t * c)
{
  assert (NULL != pcases);
  assert (NULL != c);
  sl_pred_case_array_push (pcases, c);
}

/* ====================================================================== */
/* Other methods */
/* ====================================================================== */

sl_pred_t *
sl_pred_new (const char *name, uid_t pid, sl_pred_binding_t * def)
{
  sl_pred_t *p = (sl_pred_t *) malloc (sizeof (struct sl_pred_t));
  p->pname = strdup (name);
  p->pid = pid;
  p->def = def;
  p->typ = NULL;
  /* typing info is computed after syntax analysis, @see sl_pred_type */

  return p;
}

uid_t
sl_pred_array_find (const char *name)
{
  if (preds_array && (sl_vector_size (preds_array) > 0))
    {
      uint_t sz = sl_vector_size (preds_array);
      for (uint_t i = 0; i < sz; i++)
	if (sl_pred_getpred (i) && !strcmp (name, sl_pred_getpred (i)->pname))
	  return i;
    }
  return UNDEFINED_ID;
}

uid_t
sl_pred_register (const char *pname, sl_pred_binding_t * def)
{
  assert (NULL != pname);

  uid_t pid = 0;
  for (; pid < sl_vector_size (preds_array); pid++)
    {
      sl_pred_t *pi = sl_vector_at (preds_array, pid);
      if (0 == strcmp (pname, pi->pname))
	{
	  if (pi->def != NULL && def != NULL)
	    {
	      printf ("Warning: rewrite predicate definition '%s'!\n", pname);
	    }
	  if (def != NULL)
	    pi->def = def;
	  return pid;
	}
    }

  /* Warning: modified to support mutually recursive definitions */
  assert (pid == sl_vector_size (preds_array));
  sl_pred_t *p = sl_pred_new (pname, pid, def);
  sl_pred_array_push (preds_array, p);
  return pid;
}

uid_t
sl_pred_typecheck_call (uid_t pid, sl_type_t** actuals_ty, uid_t size)
{
  if (pid == UNDEFINED_ID)
    return UNDEFINED_ID;
  const sl_pred_t *p = sl_pred_getpred (pid);
  assert (NULL != p);

  if (p->def == NULL)
    // forward call, ignore typing
    return pid;

  if (size != p->def->argc)
    {
      sl_error (0, "sl_pred_typecheck_call", "Bad number of parameters");
      SL_DEBUG ("Predicate call `%s': called with %d parameters instead of %d.\n",
	        p->pname, size, p->def->argc);
      return UNDEFINED_ID;
    }
  for (uint_t i = 0; i < size; i++)
    {
      sl_var_t *fi = sl_vector_at (p->def->args, i + 1);	/* +1 for nil */
      sl_type_t* fi_ty = fi->vty; 
      sl_typ_t fi_ty_kind = fi_ty->kind;
      uid_t a_rid = (actuals_ty[i]->kind != SL_TYP_RECORD) ? UNDEFINED_ID :
		        ((actuals_ty[i]->args == NULL) ? UNDEFINED_ID :
			  sl_vector_at (actuals_ty[i]->args, 0));
      uid_t f_rid = (fi_ty_kind != SL_TYP_RECORD) ? UNDEFINED_ID :
	      	        ((fi_ty->args == NULL) ? UNDEFINED_ID :
                          sl_vector_at (fi_ty->args, 0));

      /* if the kind is diferent */
      if ((actuals_ty[i]->kind != fi_ty_kind) ||
          /* or actual is nil and formal not a record */
	  (fi_ty_kind == SL_TYP_RECORD &&
	   a_rid != f_rid && a_rid != SL_TYP_VOID)
	 )
	{
	  SL_DEBUG ("Predicate call `%s': bad type (%d instead of %d) for the %d-th parameter.\n",
	            p->pname, actuals_ty[i]->kind, fi_ty_kind, i);
          if (fi_ty_kind == SL_TYP_RECORD &&
              actuals_ty[i]->kind == fi_ty_kind) {
            SL_DEBUG ("  record %u instead of %u.\n", a_rid, f_rid);
          }
          sl_error (0, "sl_pred_typecheck_call", "Bad type of parameters");
	  return UNDEFINED_ID;
	}
    }
  return pid;
}

const sl_pred_t *
sl_pred_getpred (uid_t pid)
{
  if (pid >= sl_vector_size (preds_array))
    {
      printf
	("sl_pred_getpred: called with identifier %d not in the global environment.\n",
	 pid);
      return NULL;
    }

  return sl_vector_at (preds_array, pid);
}

const char *
sl_pred_name (uid_t pid)
{
  const sl_pred_t *pred = NULL;
  if ((pred = sl_pred_getpred (pid)) == NULL)
    {
      return "unknown";
    }

  return pred->pname;
}


/**
 * Type the predicate definitions.
 * @return 0 for incorrect typing
 */
int
sl_pred_type ()
{
  assert (preds_array != NULL);
  assert (fields_array != NULL);
  assert (records_array != NULL);

  int res = 1;
  /* go through all predicates starting with the simpler ones */
  for (uint_t pid = 0;
       pid < sl_vector_size (preds_array) && (res == 1); pid++)
    {
      sl_pred_t *p = sl_vector_at (preds_array, pid);
      /* alloc typing info field */
      p->typ = (sl_pred_typing_t *) malloc (sizeof (struct sl_pred_typing_t));

      /* predicate type = type of the first parameter */
      if (p->def != NULL && p->def->args != NULL) {
	p->typ->ptype0 = sl_var_record (p->def->args, 1);
      } else {
	assert (0);
      }
      
      /* types covered */
      p->typ->ptypes = sl_uint_array_new ();
      /* resize the array to cover all the records, filled with 0 */
      sl_uint_array_resize (p->typ->ptypes, sl_vector_size (records_array));
      sl_vector_at (p->typ->ptypes, p->typ->ptype0) = 1;

      /* fields used */
      p->typ->pfields = sl_uint_array_new ();
      /* resize the array to cover all the fields, filled with 0 = SL_PFLD_NONE */
      sl_uint_array_resize (p->typ->pfields, sl_vector_size (fields_array));

      /* used 'nil' */
      p->typ->useNil = false;

      /* two direction predicate */
      /* TODO: better test using the predicate definition */
      p->typ->isTwoDir = (0 == strcmp (p->pname, "dll")) ? true : false;

    }
  return res;
}

/* ====================================================================== */
/* Printing */
/* ====================================================================== */

void
sl_pred_case_fprint (FILE * f, sl_var_array * args, sl_pred_case_t * rule)
{
  fprintf (f, "\nrule: ");
  sl_var_array_fprint (f, rule->lvars, "exists ");
  fprintf (f, ". \n\t(pure) ");
  sl_pure_array_fprint (f, args, rule->lvars, rule->pure);
  fprintf (f, "\n\t & (space) ");
  for (uint_t i = 0; i < sl_vector_size(rule->space); i++) {
  	sl_space_fprint (f, args, rule->lvars, sl_vector_at(rule->space,i));
	fprintf (f, " * ");
  }
  fprintf (f, " emp");
}

void
sl_pred_fprint (FILE * f, uid_t pid)
{
  if (pid == UNDEFINED_ID) {
    fprintf (f, "undefined");
    return;
  }

  sl_pred_t *pi = sl_vector_at (preds_array, pid);
  fprintf (f, "pred-%d: %s(%d args) ", pi->pid, pi->pname, pi->def->argc);

  fprintf (f, "of rules ");
  if (pi->def == NULL)
    {
      fprintf (f, "NULL\n");
      return;
    }

  assert (pi->def->cases != NULL);
  for (uint_t ri = 0; ri < sl_vector_size (pi->def->cases); ri++)
    sl_pred_case_fprint (f, pi->def->args, sl_vector_at (pi->def->cases, ri));
}


void
sl_pred_array_fprint (FILE * f, sl_pred_array * a, const char *msg)
{
  fprintf (f, "\n%s: ", msg);
  fflush (f);
  if (!a)
    {
      fprintf (f, "null\n");
      return;
    }
  fprintf (f, "[");
  uint_t length_a = sl_vector_size (a);
  for (uint_t i = 0; i < length_a; i++)
    {
      sl_pred_t *pi = sl_vector_at (a, i);
      fprintf (f, "pred-%d: %s(%d argc)\n", pi->pid, pi->pname,
	       (pi->def == NULL) ? 0 : pi->def->argc);
    }
  fprintf (f, " - ]");
  fflush (f);
}
