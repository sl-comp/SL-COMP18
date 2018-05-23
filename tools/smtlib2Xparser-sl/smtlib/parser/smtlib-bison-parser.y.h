/* A Bison parser, made by GNU Bison 3.0.4.  */

/* Bison interface for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015 Free Software Foundation, Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

#ifndef YY_SMT_YY_SMTLIB_BISON_PARSER_TAB_H_INCLUDED
# define YY_SMT_YY_SMTLIB_BISON_PARSER_TAB_H_INCLUDED
/* Debug traces.  */
#ifndef SMT_YYDEBUG
# if defined YYDEBUG
#if YYDEBUG
#   define SMT_YYDEBUG 1
#  else
#   define SMT_YYDEBUG 0
#  endif
# else /* ! defined YYDEBUG */
#  define SMT_YYDEBUG 0
# endif /* ! defined YYDEBUG */
#endif  /* ! defined SMT_YYDEBUG */
#if SMT_YYDEBUG
extern int smt_yydebug;
#endif

/* Token type.  */
#ifndef SMT_YYTOKENTYPE
# define SMT_YYTOKENTYPE
  enum smt_yytokentype
  {
    KW_AS = 258,
    KW_LET = 259,
    KW_FORALL = 260,
    KW_EXISTS = 261,
    KW_MATCH = 262,
    KW_PAR = 263,
    NOT = 264,
    NUMERAL = 265,
    DECIMAL = 266,
    HEXADECIMAL = 267,
    BINARY = 268,
    KW_ASSERT = 269,
    KW_CHK_SAT = 270,
    KW_CHK_UNSAT = 271,
    KW_CHK_SAT_ASSUM = 272,
    KW_DECL_CONST = 273,
    KW_DECL_FUN = 274,
    KW_DECL_SORT = 275,
    KW_DECL_HEAP = 276,
    KW_DEF_FUN = 277,
    KW_DEF_FUN_REC = 278,
    KW_DEF_FUNS_REC = 279,
    KW_DEF_SORT = 280,
    KW_ECHO = 281,
    KW_EXIT = 282,
    KW_GET_ASSERTS = 283,
    KW_GET_ASSIGNS = 284,
    KW_GET_INFO = 285,
    KW_GET_MODEL = 286,
    KW_GET_OPT = 287,
    KW_GET_PROOF = 288,
    KW_GET_UNSAT_ASSUMS = 289,
    KW_GET_UNSAT_CORE = 290,
    KW_GET_VALUE = 291,
    KW_POP = 292,
    KW_PUSH = 293,
    KW_RESET = 294,
    KW_RESET_ASSERTS = 295,
    KW_SET_INFO = 296,
    KW_SET_LOGIC = 297,
    KW_SET_OPT = 298,
    KW_DECL_DATATYPE = 299,
    KW_DECL_DATATYPES = 300,
    META_SPEC_DECIMAL = 301,
    META_SPEC_NUMERAL = 302,
    META_SPEC_STRING = 303,
    KEYWORD = 304,
    STRING = 305,
    SYMBOL = 306,
    THEORY = 307,
    LOGIC = 308,
    KW_ATTR_SORTS = 309,
    KW_ATTR_FUNS = 310,
    KW_ATTR_THEORIES = 311
  };
#endif

/* Value type.  */
#if ! defined SMT_YYSTYPE && ! defined SMT_YYSTYPE_IS_DECLARED

union SMT_YYSTYPE
{
#line 20 "smtlib-bison-parser.y" /* yacc.c:1915  */

	AstPtr ptr;
	AstList list;
	AstPairList pairList;

#line 125 "smtlib-bison-parser.tab.h" /* yacc.c:1915  */
};

typedef union SMT_YYSTYPE SMT_YYSTYPE;
# define SMT_YYSTYPE_IS_TRIVIAL 1
# define SMT_YYSTYPE_IS_DECLARED 1
#endif

/* Location type.  */
#if ! defined SMT_YYLTYPE && ! defined SMT_YYLTYPE_IS_DECLARED
typedef struct SMT_YYLTYPE SMT_YYLTYPE;
struct SMT_YYLTYPE
{
  int first_line;
  int first_column;
  int last_line;
  int last_column;
};
# define SMT_YYLTYPE_IS_DECLARED 1
# define SMT_YYLTYPE_IS_TRIVIAL 1
#endif


extern SMT_YYSTYPE smt_yylval;
extern SMT_YYLTYPE smt_yylloc;
int smt_yyparse (SmtPrsr parser);

#endif /* !YY_SMT_YY_SMTLIB_BISON_PARSER_TAB_H_INCLUDED  */
