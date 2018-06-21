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

#ifndef _SL_FORM_H_
#define	_SL_FORM_H_

#ifdef	__cplusplus
extern "C"
{
#endif

#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>
#include <stdio.h>
#include "sl_vector.h"
#include "sl_type.h"
#include "sl_var.h"

/* ====================================================================== */
/* Datatypes */
/* ====================================================================== */

/** Data formulas.
 *  Encoded by smtlib expressions in sl.h
 */
  typedef enum sl_pure_op_t
  {
    SL_DATA_INT = 0,
    SL_DATA_VAR,
    SL_DATA_FIELD,
    SL_DATA_LT,
    SL_DATA_GT,
    SL_DATA_LE,
    SL_DATA_GE,
    SL_DATA_EQ,
    SL_DATA_NEQ,
    SL_DATA_PLUS,
    SL_DATA_MINUS,
    SL_DATA_OTHER             /* NOT TO BE USED */
  } sl_pure_op_t;

  typedef struct sl_term_s sl_term_t;     /* forward definition */

    SL_VECTOR_DECLARE (sl_term_array, sl_term_t *);

  typedef struct sl_pure_s sl_pure_t;     /* forward definition */

    SL_VECTOR_DECLARE (sl_pure_array, sl_pure_t *);

  struct sl_term_s
  {
    sl_pure_op_t kind;        // only data terms
    sl_typ_t typ;             // either SL_TYP_RECORD or SL_TYP_INT

    union
    {
      long value;               // integer constant
      uid_t sid;                // symbol (variable or field) identifier
    } p;

    sl_term_array *args;     // NULL for 0-arity terms
  };


  struct sl_pure_s
  {
    sl_pure_op_t kind;        // only pure formulas
    sl_typ_t typ;             // SL_TYP_INT or ST_TYP_BOOL

    sl_term_array *targs;  // term arguments
  };


/**
 * Spatial formulas.
 */

  typedef struct sl_space_s sl_space_t;	/* forward definition */
    SL_VECTOR_DECLARE (sl_space_array, sl_space_t *);

  typedef enum sl_space_op_t
  {
    SL_SPACE_EMP = 0,
    SL_SPACE_JUNK,
    SL_SPACE_PTO,
    SL_SPACE_LS,
    SL_SPACE_SSEP,
    SL_SPACE_OTHER
/* NOT TO BE USED */
  } sl_space_op_t;

/** Points-to constraint
 */
  typedef struct sl_pto_t
  {
    uid_t sid;			// source location
    sl_uid_array *fields;	// array of fields
    sl_uid_array *dest;		// array of destination locations
  } sl_pto_t;

/** List segment constraint
 */
  typedef struct sl_ls_t
  {
    uid_t pid;			// predicate
    sl_uid_array *args;		// arguments used
    bool is_loop;		// set if it is a loop instance
  } sl_ls_t;

  struct sl_space_s
  {
    sl_space_op_t kind;
    bool is_precise;

    union
    {
      sl_pto_t pto;		// points-to constraint
      sl_ls_t ls;		// list segment constraint
      sl_space_array *sep;	// 
    } m;
  };

/** Formula in SL */
  typedef struct sl_form_t
  {
    sl_var_array *lvars;	// local variables
    sl_pure_array *pure;	// pure part
    sl_space_t *space;		// space part
  } sl_form_t;

    SL_VECTOR_DECLARE (sl_form_array, sl_form_t *);

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

  sl_form_t *sl_form_new (void);
  sl_pure_t *sl_pure_new (void);
  sl_space_t *sl_space_new (void);

  sl_term_t *sl_term_new (void);
  sl_term_t *sl_term_new_var (uint_t vid, sl_typ_t ty);
  sl_pure_t *sl_pure_new (void);
  sl_pure_t *sl_pure_new_eq (sl_term_t * t1, sl_term_t * t2);

/* Allocation */

  void sl_form_free (sl_form_t * f);
  void sl_pure_free (sl_pure_t * p);
  void sl_space_free (sl_space_t * s);
  void sl_term_free (sl_term_t * t);
  void sl_pure_free (sl_pure_t * d);

/* Deallocation */

  int sl_pure_add_pure (sl_pure_t * form, sl_pure_t * df);
  void sl_form_add_eq (sl_form_t * form, uid_t v1, uid_t v2);
  void sl_form_add_neq (sl_form_t * form, uid_t v1, uid_t v2);

  void sl_pure_push (sl_pure_array * form, sl_pure_op_t op, 
                     sl_term_t * e1, sl_term_t * e2);
/* Add equality/inequality pure formula */

/* ====================================================================== */
/* Typing */
/* ====================================================================== */

  int sl_form_type (sl_form_t * form);
  /* Type the formula */

/* ====================================================================== */
/* Getters/Setters */
/* ====================================================================== */


/* ====================================================================== */
/* Printing */
/* ====================================================================== */

  void sl_term_fprint (FILE * f, sl_var_array * args,
                       sl_var_array * lvars, sl_term_t * t);
  void sl_term_array_fprint (FILE * f, sl_var_array * args, 
                             sl_var_array * lvars, sl_term_array * ta);
  void sl_pure_fprint (FILE * f, sl_var_array * args, sl_var_array * lvars, 
		       sl_pure_t * phi);
  void sl_pure_array_fprint (FILE * f, sl_var_array * args, sl_var_array * lvars,
                             sl_pure_array * phi);

  void sl_space_fprint (FILE * f, sl_var_array * args, sl_var_array * lvars, 
		  	sl_space_t * phi);
  void sl_form_fprint (FILE * f, sl_form_t * phi);

#ifdef	__cplusplus
}
#endif

#endif				/* _SL_FORM_H_ */
