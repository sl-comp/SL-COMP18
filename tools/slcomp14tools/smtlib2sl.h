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

#ifndef _SMTLIB2SL_H
#define _SMTLIB2SL_H

#include "smtlib2abstractparser.h"
#include "smtlib2abstractparser_private.h"
#include "sl.h"

/** Internal data for the parser.
 */
typedef struct smtlib2_sl_parser
{
  smtlib2_abstract_parser parent_;
  sl_context_t *ctx_;		// used for local variables and quantifiers 
  smtlib2_hashtable *sorts_;	// all the declared sort symbols
  smtlib2_hashtable *funs_;	// all the declared function symbols 
} smtlib2_sl_parser;

/** Constructor/destructor.
 */
smtlib2_sl_parser *smtlib2_sl_parser_new (void);
void smtlib2_sl_parser_delete (smtlib2_sl_parser * p);

#endif /* _SMTLIB2SL_H */
