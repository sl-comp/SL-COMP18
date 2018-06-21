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
 * Abstract Syntax Tree of SL formulas.
 */

#include<sys/time.h>

#include "sl_form.h"
#include "sl_pred.h"

SL_VECTOR_DEFINE (sl_term_array, sl_term_t *);

SL_VECTOR_DEFINE (sl_pure_array, sl_pure_t *);

SL_VECTOR_DEFINE (sl_space_array, sl_space_t *);

SL_VECTOR_DEFINE (sl_form_array, sl_form_t *);

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

sl_form_t *
sl_form_new ()
{
  sl_form_t *form = (sl_form_t *) malloc (sizeof (sl_form_t));
  form->lvars = sl_var_array_new ();
  form->pure = sl_pure_array_new ();
  form->space = sl_space_new ();
  return form;
}

void
sl_form_free (sl_form_t * form)
{
  assert (form != NULL);
  if (form->lvars != NULL)
    {
      sl_var_array_delete (form->lvars);
      form->lvars = NULL;
    }
  if (form->pure != NULL)
    {
      sl_pure_array_delete (form->pure);
      form->pure = NULL;
    }
  if (form->space != NULL)
    {
      sl_space_free (form->space);
      form->space = NULL;
    }
  free (form);
}

sl_term_t *
sl_term_new (void)
{
  sl_term_t *ret = (sl_term_t *) malloc (sizeof (struct sl_term_s));
  ret->kind = SL_DATA_INT;
  ret->typ = SL_TYP_INT;
  ret->p.value = 0;
  ret->args = NULL;
  return ret;
}

sl_term_t *
sl_term_new_var (uint_t vid, sl_typ_t ty)
{
  sl_term_t *ret = (sl_term_t *) malloc (sizeof (struct sl_term_s));
  ret->kind = SL_DATA_VAR;
  ret->typ = ty;
  ret->p.sid = vid;
  ret->args = NULL;
  return ret;
}

void
sl_term_free (sl_term_t * d)
{
  if (d == NULL)
    return;
  if ((d->kind > SL_DATA_FIELD) && (d->args != NULL))
    sl_term_array_delete (d->args);
  free (d);
}

sl_pure_t *
sl_pure_new (void)
{
  sl_pure_t *ret = (sl_pure_t *) malloc (sizeof (struct sl_pure_s));
  ret->kind = SL_DATA_EQ;
  ret->typ = SL_TYP_INT;
  ret->targs = sl_term_array_new ();
  sl_term_array_push (ret->targs, sl_term_new());
  sl_term_array_push (ret->targs, sl_term_new());
  return ret;
}

sl_pure_t *
sl_pure_new_eq (sl_term_t * t1, sl_term_t * t2)
{
  assert (t1 != NULL);
  assert (t2 != NULL);
  assert (t1->typ == t2->typ);
  sl_pure_t *ret = (sl_pure_t *) malloc (sizeof (struct sl_pure_s));
  ret->kind = SL_DATA_EQ;
  ret->typ = t1->typ;
  ret->targs = sl_term_array_new ();
  sl_term_array_push (ret->targs, t1);
  sl_term_array_push (ret->targs, t2);
  return ret;
}

void
sl_pure_free (sl_pure_t * d)
{
  if (d == NULL)
    return;
  if (d->kind != SL_DATA_OTHER)
    {
      if (d->targs != NULL)
        sl_term_array_delete (d->targs);
    }
  free (d);
}

sl_space_t *
sl_space_new ()
{
  sl_space_t *ret = (sl_space_t *) malloc (sizeof (sl_space_t));
  ret->kind = SL_SPACE_EMP;
  ret->is_precise = true;
  return ret;
}

void
sl_space_free (sl_space_t * s)
{
  if (!s)
    return;
  switch (s->kind)
    {
    case SL_SPACE_PTO:
      {
	if (sl_vector_size (s->m.pto.fields) > 0)
	  {
	    if (s->m.pto.fields)
	      sl_uid_array_delete (s->m.pto.fields);
	    if (s->m.pto.dest)
	      sl_uid_array_delete (s->m.pto.dest);
	  }
	break;
      }
    case SL_SPACE_LS:
      {
	if (s->m.ls.args && sl_vector_size (s->m.ls.args) > 0)
	  sl_uid_array_delete (s->m.ls.args);
	break;
      }
    case SL_SPACE_SSEP:
      {
	sl_space_array_delete (s->m.sep);
	break;
      }
    default:
      break;
    }
  free (s);
  return;
}

void
sl_pure_push (sl_pure_array * f, sl_pure_op_t op, 
              sl_term_t * e1, sl_term_t * e2)
{
  assert (f != NULL);

  sl_pure_t *res = sl_pure_new_eq (e1,e2);
  res->kind = op;
  sl_pure_array_push (f, res);
}

/* ====================================================================== */
/* Typing */
/* ====================================================================== */


/**
 * Type the formula @p form.
 * @return 0 if incorrect typing
 */
int
sl_form_type (sl_form_t * form)
{
  if (form != NULL)		// only to use form
    return 1;
  /* TODO: redo typing here */
  return 0;
}

/* ====================================================================== */
/* Getters/Setters */
/* ====================================================================== */

/* ====================================================================== */
/* Printing */
/* ====================================================================== */

void
sl_term_fprint (FILE * f, sl_var_array * args, sl_var_array * lvars, sl_term_t * t) 
{
  if (!t)
    {
      fprintf (f, "null term\n");
      return;
    }
  fprintf (f, "(");
  switch (t->kind)
    {
    case SL_DATA_INT: fprintf (f, " %ld ", t->p.value); break;
    case SL_DATA_VAR: {
      char * vname = sl_var_name2(args, lvars, t->p.sid, SL_TYP_RECORD);
      fprintf (f, " (vid:%ud) %s ", t->p.sid, (NULL == vname) ? "error" : vname);
      break;
    }
    case SL_DATA_FIELD: fprintf (f, " (fid:%ud) %s ", t->p.sid,
                                 sl_field_name(t->p.sid));
      sl_term_array_fprint (f, args, lvars, t->args);
      break;
    case SL_DATA_PLUS: fprintf (f, " + ");
      sl_term_array_fprint (f, args, lvars, t->args);
      break;
    case SL_DATA_MINUS: fprintf (f, " - ");
      sl_term_array_fprint (f, args, lvars, t->args);
      break;
    default: fprintf (f, " unknown-op ");
      break;
    }
  fprintf (f, ")");
}

void 
sl_term_array_fprint (FILE * f, sl_var_array * args, 
                      sl_var_array * lvars, sl_term_array * ta)
{
  if (!ta)
    {
      fprintf (f, "null term array\n");
      return;
    }
  for (size_t i = 0; i < sl_vector_size (ta); i++)
    {
      sl_term_t * t = sl_vector_at (ta, i);
      sl_term_fprint (f, args, lvars, t);
      fprintf (f, " ");
    }
  fprintf (f, "\n");
}

void
sl_pure_fprint (FILE * f, sl_var_array * args, sl_var_array * lvars, sl_pure_t * phi)
{
  if (!phi)
    {
      fprintf (f, "null pure\n");
      return;
    }
  fprintf (f, "(");
  switch (phi->kind) 
    {
    case SL_DATA_EQ: fprintf (f, "="); break;
    case SL_DATA_NEQ: fprintf (f, "<>"); break;
    case SL_DATA_LT: fprintf (f, "<"); break;
    case SL_DATA_LE: fprintf (f, "<="); break;
    case SL_DATA_GT: fprintf (f, ">"); break;
    case SL_DATA_GE: fprintf (f, ">="); break;
    default: fprintf (f, "unknown"); break;
    }
  sl_term_array_fprint (f, args, lvars, phi->targs);
  fprintf (f, ")");
}

void
sl_pure_array_fprint (FILE * f, sl_var_array * args, 
                      sl_var_array * lvars, sl_pure_array * phi)
{
  if (!phi)
    {
      fprintf (f, "null\n");
      return;
    }
  for (size_t i = 0; i < sl_vector_size (phi); i++)
    {
      sl_pure_t *fi = sl_vector_at (phi, i);
      sl_pure_fprint (f, args, lvars, fi);
      fprintf (f, "and \n");
    }
  fprintf (f, " true\n");
}

void
sl_space_fprint (FILE * f, sl_var_array * args, sl_var_array * lvars, sl_space_t * phi)
{
  if (!phi)
    {
      fprintf (f, "null\n");
      return;
    }

  if (phi->is_precise == true)
    fprintf (f, "[precise] ");
  else
    fprintf (f, "[junk] ");

  switch (phi->kind)
    {
    case SL_SPACE_EMP:
      fprintf (f, "emp");
      break;
    case SL_SPACE_JUNK:
      fprintf (f, "junk");
      break;
    case SL_SPACE_PTO:
      {
	fprintf (f, "(pto  ");
	if (lvars == NULL)
	  fprintf (f, "*%d ...)", phi->m.pto.sid);
	else {
          char* vname = sl_var_name2(args, lvars, phi->m.pto.sid, SL_TYP_RECORD);
	  fprintf (f, "%s ...)", (NULL == vname) ? "error" : vname);
	}
        break;
      }
    case SL_SPACE_LS:
      {
	const sl_pred_t *pred = sl_pred_getpred (phi->m.ls.pid);
	assert (NULL != pred);
	fprintf (f, "(%s", pred->pname);
	for (uid_t i = 0; i < sl_vector_size (phi->m.ls.args); i++)
	  {
	    uint_t vi = sl_vector_at (phi->m.ls.args, i);
	    if (lvars == NULL)
	      fprintf (f, " *%d ", vi);
	    else if (vi == VNIL_ID)
	      fprintf (f, " nil ");
	    else {
	      char* vname = sl_var_name2(args, lvars, vi, SL_TYP_RECORD);
	      fprintf (f, " %s ", (NULL == vname) ? "error" : vname);
	    }
	  }
	fprintf (f, ")");
	break;
      }
    default:
      {
	assert (phi->kind == SL_SPACE_SSEP);
	fprintf (f, "(ssep ");
	for (uid_t i = 0; i < sl_vector_size (phi->m.sep); i++)
	  {
	    sl_space_fprint (f, args, lvars, sl_vector_at (phi->m.sep, i));
	    fprintf (f, "\n\t");
	  }
	fprintf (f, ")");
	break;
      }
    }
}

void
sl_form_fprint (FILE * f, sl_form_t * phi)
{
  assert (f != NULL);

  if (!phi)
    {
      fprintf (stdout, "null\n");
      return;
    }

  fprintf (f, "\n\t lvars: ");
  sl_var_array_fprint (f, phi->lvars, "\t\t");
  fprintf (f, "\n\n\t pure part: \t");
  sl_pure_array_fprint (f, phi->lvars, phi->lvars, phi->pure);
  fprintf (f, "\n\t spatial part: \t");
  sl_space_fprint (f, phi->lvars, phi->lvars, phi->space);

}
