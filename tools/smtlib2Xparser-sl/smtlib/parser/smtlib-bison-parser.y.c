/* A Bison parser, made by GNU Bison 3.0.4.  */

/* Bison implementation for Yacc-like parsers in C

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

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "3.0.4"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1

/* Substitute the type names.  */
#define YYSTYPE         SMT_YYSTYPE
#define YYLTYPE         SMT_YYLTYPE
/* Substitute the variable and function names.  */
#define yyparse         smt_yyparse
#define yylex           smt_yylex
#define yyerror         smt_yyerror
#define yydebug         smt_yydebug
#define yynerrs         smt_yynerrs

#define yylval          smt_yylval
#define yychar          smt_yychar
#define yylloc          smt_yylloc

/* Copy the first part of user declarations.  */
#line 1 "smtlib-bison-parser.y" /* yacc.c:339  */

#include <stdio.h>
#include "smtlib-glue.h"

int yylex();
void yyerror(SmtPrsr parser, const char *);

#define YYMAXDEPTH 300000
#define YYINITDEPTH 300000

#line 88 "smtlib-bison-parser.tab.c" /* yacc.c:339  */

# ifndef YY_NULLPTR
#  if defined __cplusplus && 201103L <= __cplusplus
#   define YY_NULLPTR nullptr
#  else
#   define YY_NULLPTR 0
#  endif
# endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 1
#endif

/* In a future release of Bison, this section will be replaced
   by #include "smtlib-bison-parser.tab.h".  */
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
    KW_CHK_SAT_ASSUM = 271,
    KW_DECL_CONST = 272,
    KW_DECL_FUN = 273,
    KW_DECL_SORT = 274,
    KW_DECL_HEAP = 275,
    KW_DEF_FUN = 276,
    KW_DEF_FUN_REC = 277,
    KW_DEF_FUNS_REC = 278,
    KW_DEF_SORT = 279,
    KW_ECHO = 280,
    KW_EXIT = 281,
    KW_GET_ASSERTS = 282,
    KW_GET_ASSIGNS = 283,
    KW_GET_INFO = 284,
    KW_GET_MODEL = 285,
    KW_GET_OPT = 286,
    KW_GET_PROOF = 287,
    KW_GET_UNSAT_ASSUMS = 288,
    KW_GET_UNSAT_CORE = 289,
    KW_GET_VALUE = 290,
    KW_POP = 291,
    KW_PUSH = 292,
    KW_RESET = 293,
    KW_RESET_ASSERTS = 294,
    KW_SET_INFO = 295,
    KW_SET_LOGIC = 296,
    KW_SET_OPT = 297,
    KW_DECL_DATATYPE = 298,
    KW_DECL_DATATYPES = 299,
    META_SPEC_DECIMAL = 300,
    META_SPEC_NUMERAL = 301,
    META_SPEC_STRING = 302,
    KEYWORD = 303,
    STRING = 304,
    SYMBOL = 305,
    THEORY = 306,
    LOGIC = 307,
    KW_ATTR_SORTS = 308,
    KW_ATTR_FUNS = 309,
    KW_ATTR_THEORIES = 310
  };
#endif

/* Value type.  */
#if ! defined SMT_YYSTYPE && ! defined SMT_YYSTYPE_IS_DECLARED

union SMT_YYSTYPE
{
#line 20 "smtlib-bison-parser.y" /* yacc.c:355  */

	AstPtr ptr;
	AstList list;
	AstPairList pairList;

#line 198 "smtlib-bison-parser.tab.c" /* yacc.c:355  */
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

/* Copy the second part of user declarations.  */

#line 229 "smtlib-bison-parser.tab.c" /* yacc.c:358  */

#ifdef short
# undef short
#endif

#ifdef YYTYPE_UINT8
typedef YYTYPE_UINT8 yytype_uint8;
#else
typedef unsigned char yytype_uint8;
#endif

#ifdef YYTYPE_INT8
typedef YYTYPE_INT8 yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef YYTYPE_UINT16
typedef YYTYPE_UINT16 yytype_uint16;
#else
typedef unsigned short int yytype_uint16;
#endif

#ifdef YYTYPE_INT16
typedef YYTYPE_INT16 yytype_int16;
#else
typedef short int yytype_int16;
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif ! defined YYSIZE_T
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned int
# endif
#endif

#define YYSIZE_MAXIMUM ((YYSIZE_T) -1)

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif

#ifndef YY_ATTRIBUTE
# if (defined __GNUC__                                               \
      && (2 < __GNUC__ || (__GNUC__ == 2 && 96 <= __GNUC_MINOR__)))  \
     || defined __SUNPRO_C && 0x5110 <= __SUNPRO_C
#  define YY_ATTRIBUTE(Spec) __attribute__(Spec)
# else
#  define YY_ATTRIBUTE(Spec) /* empty */
# endif
#endif

#ifndef YY_ATTRIBUTE_PURE
# define YY_ATTRIBUTE_PURE   YY_ATTRIBUTE ((__pure__))
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# define YY_ATTRIBUTE_UNUSED YY_ATTRIBUTE ((__unused__))
#endif

#if !defined _Noreturn \
     && (!defined __STDC_VERSION__ || __STDC_VERSION__ < 201112)
# if defined _MSC_VER && 1200 <= _MSC_VER
#  define _Noreturn __declspec (noreturn)
# else
#  define _Noreturn YY_ATTRIBUTE ((__noreturn__))
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(E) ((void) (E))
#else
# define YYUSE(E) /* empty */
#endif

#if defined __GNUC__ && 407 <= __GNUC__ * 100 + __GNUC_MINOR__
/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN \
    _Pragma ("GCC diagnostic push") \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")\
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# define YY_IGNORE_MAYBE_UNINITIALIZED_END \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif


#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
      /* Use EXIT_SUCCESS as a witness for stdlib.h.  */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
             && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined SMT_YYLTYPE_IS_TRIVIAL && SMT_YYLTYPE_IS_TRIVIAL \
             && defined SMT_YYSTYPE_IS_TRIVIAL && SMT_YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss_alloc;
  YYSTYPE yyvs_alloc;
  YYLTYPE yyls_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE) + sizeof (YYLTYPE)) \
      + 2 * YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYSIZE_T yynewbytes;                                            \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / sizeof (*yyptr);                          \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, (Count) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYSIZE_T yyi;                         \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  41
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   593

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  60
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  61
/* YYNRULES -- Number of rules.  */
#define YYNRULES  155
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  362

/* YYTRANSLATE[YYX] -- Symbol number corresponding to YYX as returned
   by yylex, with out-of-bounds checking.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   310

#define YYTRANSLATE(YYX)                                                \
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, without out-of-bounds checking.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    58,     2,     2,     2,     2,     2,     2,
      56,    57,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,    59,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55
};

#if SMT_YYDEBUG
  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,    61,    61,    63,    65,    69,    83,    94,   107,   119,
     131,   143,   155,   167,   179,   191,   203,   215,   227,   239,
     251,   263,   275,   287,   299,   311,   323,   334,   346,   358,
     370,   382,   394,   406,   418,   430,   442,   454,   466,   480,
     491,   504,   516,   530,   541,   554,   569,   573,   593,   607,
     618,   631,   645,   655,   665,   677,   689,   701,   713,   725,
     737,   751,   762,   775,   786,   799,   813,   823,   837,   847,
     861,   873,   885,   897,   909,   923,   935,   947,   959,   973,
     983,   997,  1009,  1023,  1035,  1049,  1060,  1073,  1085,  1099,
    1110,  1124,  1128,  1148,  1159,  1172,  1186,  1197,  1210,  1224,
    1235,  1249,  1251,  1271,  1283,  1298,  1300,  1320,  1331,  1344,
    1354,  1364,  1378,  1388,  1398,  1408,  1422,  1433,  1446,  1458,
    1473,  1476,  1496,  1510,  1521,  1534,  1550,  1552,  1572,  1583,
    1596,  1610,  1622,  1636,  1649,  1662,  1674,  1685,  1698,  1712,
    1723,  1736,  1738,  1752,  1763,  1776,  1788,  1800,  1814,  1826,
    1838,  1852,  1866,  1878,  1890,  1901
};
#endif

#if SMT_YYDEBUG || YYERROR_VERBOSE || 1
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "KW_AS", "KW_LET", "KW_FORALL",
  "KW_EXISTS", "KW_MATCH", "KW_PAR", "NOT", "NUMERAL", "DECIMAL",
  "HEXADECIMAL", "BINARY", "KW_ASSERT", "KW_CHK_SAT", "KW_CHK_SAT_ASSUM",
  "KW_DECL_CONST", "KW_DECL_FUN", "KW_DECL_SORT", "KW_DECL_HEAP",
  "KW_DEF_FUN", "KW_DEF_FUN_REC", "KW_DEF_FUNS_REC", "KW_DEF_SORT",
  "KW_ECHO", "KW_EXIT", "KW_GET_ASSERTS", "KW_GET_ASSIGNS", "KW_GET_INFO",
  "KW_GET_MODEL", "KW_GET_OPT", "KW_GET_PROOF", "KW_GET_UNSAT_ASSUMS",
  "KW_GET_UNSAT_CORE", "KW_GET_VALUE", "KW_POP", "KW_PUSH", "KW_RESET",
  "KW_RESET_ASSERTS", "KW_SET_INFO", "KW_SET_LOGIC", "KW_SET_OPT",
  "KW_DECL_DATATYPE", "KW_DECL_DATATYPES", "META_SPEC_DECIMAL",
  "META_SPEC_NUMERAL", "META_SPEC_STRING", "KEYWORD", "STRING", "SYMBOL",
  "THEORY", "LOGIC", "KW_ATTR_SORTS", "KW_ATTR_FUNS", "KW_ATTR_THEORIES",
  "'('", "')'", "'!'", "'_'", "$accept", "smt_file", "script",
  "command_plus", "command", "datatype_decl_plus", "datatype_decl",
  "constructor_decl_plus", "constructor_decl", "selector_decl_star",
  "selector_decl", "sort_decl_plus", "sort_decl", "term", "term_plus",
  "match_case_plus", "match_case", "pattern", "qual_constructor",
  "spec_const", "symbol", "qual_identifier", "identifier", "index",
  "index_plus", "sort", "sort_plus", "sort_star", "sort_pair_plus",
  "var_binding", "var_binding_plus", "sorted_var", "sorted_var_plus",
  "sorted_var_star", "attribute", "attribute_star", "attribute_plus",
  "attr_value", "s_exp", "s_exp_plus", "prop_literal", "prop_literal_star",
  "fun_decl", "fun_decl_plus", "fun_def", "symbol_star", "symbol_plus",
  "info_flag", "option", "theory_decl", "theory_attr", "theory_attr_plus",
  "sort_symbol_decl", "sort_symbol_decl_plus", "par_fun_symbol_decl",
  "par_fun_symbol_decl_plus", "fun_symbol_decl", "meta_spec_const",
  "logic", "logic_attr", "logic_attr_plus", YY_NULLPTR
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[NUM] -- (External) token number corresponding to the
   (internal) symbol number NUM (which must be that of a token).  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298,   299,   300,   301,   302,   303,   304,
     305,   306,   307,   308,   309,   310,    40,    41,    33,    95
};
# endif

#define YYPACT_NINF -296

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-296)))

#define YYTABLE_NINF -1

#define yytable_value_is_error(Yytable_value) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int16 yypact[] =
{
     -34,   510,    25,  -296,    32,  -296,  -296,  -296,   456,   -29,
      35,   176,   176,   176,    42,   176,   176,    55,   176,    16,
      56,    59,    61,    74,    72,    85,    81,    89,   102,   456,
     130,   151,   107,   110,   126,   176,   126,   176,   127,   176,
     176,  -296,   549,  -296,  -296,  -296,  -296,  -296,  -296,  -296,
    -296,  -296,   138,  -296,   129,  -296,  -296,  -296,  -296,  -296,
    -296,    58,   162,   197,    58,     4,   175,   189,   191,   194,
     199,   201,  -296,  -296,  -296,  -296,   204,  -296,   212,  -296,
    -296,  -296,  -296,   378,   217,   220,  -296,  -296,   464,   229,
     232,  -296,   236,   226,   240,    83,    -6,    71,   243,   247,
     249,   456,   456,   176,   251,   456,  -296,   125,   225,  -296,
     252,  -296,   254,    58,    58,  -296,  -296,  -296,  -296,   176,
    -296,    26,  -296,  -296,  -296,  -296,  -296,  -296,  -296,  -296,
     395,  -296,  -296,  -296,  -296,  -296,  -296,     2,   255,   176,
      48,  -296,   250,   259,  -296,  -296,   -16,   261,  -296,  -296,
     -28,   269,    58,   262,   264,   264,   275,   126,    36,  -296,
     400,   323,   276,  -296,  -296,    58,  -296,   163,  -296,   277,
      58,    68,   286,   287,  -296,   171,  -296,   395,  -296,  -296,
    -296,   327,   288,   176,    99,  -296,  -296,   335,   293,  -296,
     295,   302,  -296,  -296,  -296,  -296,  -296,   176,   290,   176,
    -296,   135,   176,  -296,   143,   146,   306,  -296,    -9,  -296,
    -296,  -296,    14,  -296,   176,  -296,  -296,   195,    58,  -296,
    -296,   309,    58,  -296,  -296,   456,    58,  -296,   344,  -296,
    -296,   176,  -296,  -296,  -296,   310,   226,    71,  -296,   149,
     314,  -296,   159,  -296,   203,  -296,   456,   456,  -296,    58,
     456,  -296,   456,   238,   180,  -296,  -296,  -296,  -296,  -296,
     311,  -296,  -296,   312,  -296,   456,   216,   451,   315,  -296,
    -296,   257,   223,  -296,   235,  -296,   361,  -296,  -296,   318,
    -296,  -296,  -296,    58,    58,    58,  -296,  -296,  -296,   321,
     322,   324,   328,   338,    31,   456,  -296,  -296,   339,  -296,
    -296,  -296,  -296,    58,   340,  -296,   342,  -296,   176,  -296,
    -296,   345,  -296,  -296,   176,  -296,    58,  -296,  -296,  -296,
    -296,  -296,  -296,   176,   377,   176,   357,  -296,   358,  -296,
     343,    58,  -296,    -1,   291,     9,    11,    15,    58,   433,
    -296,  -296,   245,   360,  -296,  -296,   362,  -296,  -296,  -296,
     363,  -296,   364,  -296,    71,  -296,  -296,    58,    58,    28,
     365,  -296
};

  /* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
     Performed when YYTABLE does not specify something else to do.  Zero
     means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       0,     0,     0,     2,     5,     6,     3,     4,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     1,     0,     7,    77,    70,    71,    72,    73,    76,
      74,    75,     0,    78,     0,    52,    81,    53,    79,     9,
     120,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    22,    23,    24,   130,     0,    26,     0,    28,
      29,    30,    61,     0,     0,     0,    35,    34,   103,     0,
       0,   131,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,    78,     0,    53,     8,     0,     0,    87,
       0,    91,     0,     0,     0,    16,   101,    19,    18,     0,
     123,     0,   126,    21,    25,    27,    31,    62,    32,    33,
       0,   109,   110,   104,    36,    37,    38,     0,     0,     0,
       0,    49,     0,     0,   135,   136,     0,     0,   153,   154,
       0,     0,     0,     0,     0,     0,     0,     0,     0,    60,
       0,     0,     0,   118,   121,     0,    11,     0,    15,     0,
       0,     0,     0,     0,   124,     0,   114,     0,   112,   113,
     116,     0,     0,     0,     0,    43,    12,     0,     0,    50,
       0,     0,   132,   137,   126,   151,   155,     0,     0,     0,
      96,     0,     0,    99,     0,     0,     0,   107,     0,    83,
      84,    85,     0,    54,     0,    10,    89,     0,     0,    92,
      93,     0,     0,   102,   101,     0,     0,   127,     0,   111,
     117,     0,    46,    41,    44,     0,     0,     0,   139,     0,
       0,   143,     0,   141,     0,    80,     0,     0,    97,     0,
       0,   100,     0,     0,     0,    63,    59,   108,    82,    86,
       0,    88,    90,     0,    94,     0,     0,     0,     0,   115,
     128,     0,     0,    51,     0,    39,     0,   133,   140,     0,
     149,   148,   150,     0,     0,     0,   134,   144,   152,     0,
       0,     0,     0,     0,     0,     0,    66,    68,     0,    64,
     119,    14,   125,     0,     0,    20,     0,   129,     0,    45,
      47,     0,    40,   105,     0,   105,   105,   105,    95,    55,
      98,    56,    57,     0,     0,     0,     0,    58,     0,    17,
       0,     0,    13,     0,     0,     0,     0,     0,     0,     0,
      65,   122,     0,     0,   138,   106,     0,   145,   147,   146,
       0,    67,     0,    48,     0,    69,    42,     0,   105,     0,
       0,   142
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -296,  -296,  -296,  -296,   415,  -296,  -231,    93,  -182,  -296,
    -296,  -296,   284,    18,  -102,  -296,   172,  -296,   131,   -75,
      -4,   379,    -8,   218,  -296,   -60,  -278,  -296,  -296,   228,
    -296,  -154,   281,   208,   -18,  -147,  -296,  -296,  -166,   263,
    -296,  -296,   320,  -296,   423,   253,  -295,  -296,  -296,  -296,
     300,  -296,   209,  -296,   210,  -296,  -296,  -296,  -296,   303,
    -296
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     2,     3,     4,     5,   274,   138,   184,   185,   272,
     310,   140,   141,    82,    83,   254,   255,   295,   296,    55,
      56,    57,   109,   211,   212,   216,   217,   167,    65,   200,
     201,   203,   204,   171,   345,   333,   208,   133,   180,   181,
     164,   107,   120,   121,    67,   175,   271,    76,    92,     6,
     145,   146,   238,   239,   241,   242,   243,   285,     7,   149,
     150
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_uint16 yytable[] =
{
      58,   110,   234,   160,   113,   275,   316,    61,    62,    63,
     182,    66,    66,   131,    70,   230,    89,   223,    91,   334,
      88,    58,     1,    44,   209,    41,    54,   147,    59,   195,
     339,    90,    88,    93,   323,    95,    96,   142,   143,    88,
      44,   192,    88,   312,    58,    44,   209,    88,   256,   147,
     251,   251,    49,   169,   170,   178,   344,    88,   183,    88,
     114,   115,   230,    88,    51,    71,   347,    44,   348,    49,
     104,   258,   349,    53,    49,    58,    88,   144,   148,   358,
      44,    51,   119,   173,   132,   360,    51,   324,    42,   152,
      53,    60,   198,    58,    58,    53,    49,    58,    64,   158,
     165,   127,   178,   163,   139,   188,   178,   219,    51,    49,
     221,    69,   223,    72,   108,   172,    73,    53,    74,   156,
     157,    51,    75,   267,   202,   222,   179,   151,   144,    77,
      53,    88,   148,    78,    44,   187,   142,   143,    79,   207,
      84,    97,    98,    99,   100,   101,    80,    44,    45,    46,
      47,    48,    58,   178,   210,   183,   233,   262,   263,    81,
     234,    85,   265,    49,    86,   283,   268,    87,   335,   336,
     337,   227,    44,   179,    88,    51,    49,   179,   127,   232,
      44,   161,   162,    94,    53,    44,   106,    50,    51,   291,
     257,   199,   247,   158,    52,   246,   102,   103,   249,   202,
     250,    49,   202,   252,    44,   237,   277,   112,   210,    49,
     260,   359,    44,    51,    49,   240,   286,    58,   111,   108,
     218,    51,    53,   315,   179,   317,    51,   270,   226,   276,
      53,   116,   284,    49,    44,    53,   253,   298,    58,    58,
     227,    49,    58,   328,    58,    51,   117,    44,   118,   297,
     119,   108,   261,    51,    53,   122,   262,    58,   123,    58,
     288,   124,    53,    49,   289,   290,    44,   307,   292,   125,
     293,   343,   202,   303,   128,    51,    49,   129,   350,   308,
     309,   151,   137,   302,   103,   127,   134,    58,    51,   135,
     297,   137,   311,   136,   294,    49,   139,    53,   262,   153,
      44,   183,   352,   154,   331,   155,   190,    51,   159,   166,
     270,   168,   186,   326,   306,   191,    53,   194,   199,   338,
     202,   270,   279,    44,    45,    46,    47,    48,   197,    49,
     307,   206,   214,   215,   220,   307,    44,    45,    46,    47,
      48,    51,   224,   225,   231,   235,   357,   245,   346,   236,
      53,   237,    49,    44,    45,    46,    47,    48,   240,   280,
     281,   282,   253,    50,    51,    49,   264,   273,   300,   301,
     151,   313,   305,    53,   314,   176,    50,    51,   318,   319,
     323,   320,    49,   177,   229,   321,    53,    44,    45,    46,
      47,    48,   176,    50,    51,   322,   327,   329,   330,   183,
     177,   269,   332,    53,    44,    45,    46,    47,    48,    44,
      45,    46,    47,    48,   340,   341,    49,   353,   354,    43,
     355,   356,   361,   342,   189,   325,   299,    50,    51,   248,
     259,   105,   266,    49,    52,   126,   205,    53,    49,    68,
     228,   174,    44,   176,    50,    51,   193,   244,   278,    50,
      51,   177,   287,   196,    53,     0,    52,   213,     0,    53,
      44,    45,    46,    47,    48,    44,    45,    46,    47,    48,
       0,    49,     0,    44,    45,    46,    47,    48,     0,     0,
       0,     0,     0,    51,     0,     0,     0,     0,     0,    49,
     351,     0,    53,     0,    49,     0,     0,     0,     0,     0,
      50,    51,    49,     0,     0,    50,    51,    52,   304,     0,
      53,     0,    52,    50,    51,    53,     0,     0,     0,     0,
     130,     0,     0,    53,     8,     9,    10,    11,    12,    13,
      14,    15,    16,    17,    18,    19,    20,    21,    22,    23,
      24,    25,    26,    27,    28,    29,    30,    31,    32,    33,
      34,    35,    36,    37,    38,     0,     0,     0,     0,     0,
       0,    39,    40,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38
};

static const yytype_int16 yycheck[] =
{
       8,    61,   184,   105,    64,   236,   284,    11,    12,    13,
       8,    15,    16,    88,    18,   181,    34,   171,    36,   314,
      48,    29,    56,     9,    10,     0,     8,    55,    57,    57,
     325,    35,    48,    37,     3,    39,    40,    53,    54,    48,
       9,    57,    48,   274,    52,     9,    10,    48,    57,    55,
     204,   205,    38,   113,   114,   130,    57,    48,    56,    48,
      56,    57,   228,    48,    50,    49,    57,     9,    57,    38,
      52,    57,    57,    59,    38,    83,    48,    95,    96,   357,
       9,    50,    56,    57,    88,    57,    50,    56,    56,    97,
      59,    56,   152,   101,   102,    59,    38,   105,    56,   103,
     108,    83,   177,   107,    56,    57,   181,   167,    50,    38,
     170,    56,   266,    57,    56,   119,    57,    59,    57,   101,
     102,    50,    48,   225,    56,    57,   130,    56,   146,    57,
      59,    48,   150,    48,     9,   139,    53,    54,    57,   157,
      10,     3,     4,     5,     6,     7,    57,     9,    10,    11,
      12,    13,   160,   228,   158,    56,    57,   217,   218,    57,
     342,    10,   222,    38,    57,   240,   226,    57,   315,   316,
     317,   175,     9,   177,    48,    50,    38,   181,   160,   183,
       9,    56,    57,    56,    59,     9,    57,    49,    50,   249,
     208,    56,    57,   197,    56,   199,    58,    59,   202,    56,
      57,    38,    56,    57,     9,    56,    57,    10,   212,    38,
     214,   358,     9,    50,    38,    56,    57,   225,    56,    56,
      57,    50,    59,   283,   228,   285,    50,   231,    57,   237,
      59,    56,   240,    38,     9,    59,    56,    57,   246,   247,
     244,    38,   250,   303,   252,    50,    57,     9,    57,   253,
      56,    56,    57,    50,    59,    56,   316,   265,    57,   267,
      57,    57,    59,    38,   246,   247,     9,   271,   250,    57,
     252,   331,    56,    57,    57,    50,    38,    57,   338,    56,
      57,    56,    56,   265,    59,   267,    57,   295,    50,    57,
     294,    56,    57,    57,    56,    38,    56,    59,   358,    56,
       9,    56,    57,    56,   308,    56,    56,    50,    57,    57,
     314,    57,    57,   295,    57,    56,    59,    56,    56,   323,
      56,   325,     8,     9,    10,    11,    12,    13,    59,    38,
     334,    56,     9,    57,    57,   339,     9,    10,    11,    12,
      13,    50,    56,    56,    56,    10,   354,    57,    57,    56,
      59,    56,    38,     9,    10,    11,    12,    13,    56,    45,
      46,    47,    56,    49,    50,    38,    57,    57,    57,    57,
      56,    10,    57,    59,    56,    48,    49,    50,    57,    57,
       3,    57,    38,    56,    57,    57,    59,     9,    10,    11,
      12,    13,    48,    49,    50,    57,    57,    57,    56,    56,
      56,    57,    57,    59,     9,    10,    11,    12,    13,     9,
      10,    11,    12,    13,    57,    57,    38,    57,    56,     4,
      57,    57,    57,   330,   140,   294,   254,    49,    50,   201,
     212,    52,   224,    38,    56,    57,   155,    59,    38,    16,
     177,   121,     9,    48,    49,    50,   146,   194,   239,    49,
      50,    56,   242,   150,    59,    -1,    56,    57,    -1,    59,
       9,    10,    11,    12,    13,     9,    10,    11,    12,    13,
      -1,    38,    -1,     9,    10,    11,    12,    13,    -1,    -1,
      -1,    -1,    -1,    50,    -1,    -1,    -1,    -1,    -1,    38,
      57,    -1,    59,    -1,    38,    -1,    -1,    -1,    -1,    -1,
      49,    50,    38,    -1,    -1,    49,    50,    56,    57,    -1,
      59,    -1,    56,    49,    50,    59,    -1,    -1,    -1,    -1,
      56,    -1,    -1,    59,    14,    15,    16,    17,    18,    19,
      20,    21,    22,    23,    24,    25,    26,    27,    28,    29,
      30,    31,    32,    33,    34,    35,    36,    37,    38,    39,
      40,    41,    42,    43,    44,    -1,    -1,    -1,    -1,    -1,
      -1,    51,    52,    14,    15,    16,    17,    18,    19,    20,
      21,    22,    23,    24,    25,    26,    27,    28,    29,    30,
      31,    32,    33,    34,    35,    36,    37,    38,    39,    40,
      41,    42,    43,    44
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,    56,    61,    62,    63,    64,   109,   118,    14,    15,
      16,    17,    18,    19,    20,    21,    22,    23,    24,    25,
      26,    27,    28,    29,    30,    31,    32,    33,    34,    35,
      36,    37,    38,    39,    40,    41,    42,    43,    44,    51,
      52,     0,    56,    64,     9,    10,    11,    12,    13,    38,
      49,    50,    56,    59,    73,    79,    80,    81,    82,    57,
      56,    80,    80,    80,    56,    88,    80,   104,   104,    56,
      80,    49,    57,    57,    57,    48,   107,    57,    48,    57,
      57,    57,    73,    74,    10,    10,    57,    57,    48,    94,
      80,    94,   108,    80,    56,    80,    80,     3,     4,     5,
       6,     7,    58,    59,    73,    81,    57,   101,    56,    82,
      85,    56,    10,    85,    56,    57,    56,    57,    57,    56,
     102,   103,    56,    57,    57,    57,    57,    73,    57,    57,
      56,    79,    80,    97,    57,    57,    57,    56,    66,    56,
      71,    72,    53,    54,    94,   110,   111,    55,    94,   119,
     120,    56,    82,    56,    56,    56,    73,    73,    80,    57,
      74,    56,    57,    80,   100,    82,    57,    87,    57,    85,
      85,    93,    80,    57,   102,   105,    48,    56,    79,    80,
      98,    99,     8,    56,    67,    68,    57,    80,    57,    72,
      56,    56,    57,   110,    56,    57,   119,    59,    85,    56,
      89,    90,    56,    91,    92,    92,    56,    94,    96,    10,
      80,    83,    84,    57,     9,    57,    85,    86,    57,    85,
      57,    85,    57,    91,    56,    56,    57,    80,    99,    57,
      98,    56,    80,    57,    68,    10,    56,    56,   112,   113,
      56,   114,   115,   116,   105,    57,    80,    57,    89,    80,
      57,    91,    57,    56,    75,    76,    57,    94,    57,    83,
      80,    57,    85,    85,    57,    85,    93,    74,    85,    57,
      80,   106,    69,    57,    65,    66,    82,    57,   112,     8,
      45,    46,    47,    79,    82,   117,    57,   114,    57,    73,
      73,    85,    73,    73,    56,    77,    78,    80,    57,    76,
      57,    57,    73,    57,    57,    57,    57,    80,    56,    57,
      70,    57,    66,    10,    56,    85,    86,    85,    57,    57,
      57,    57,    57,     3,    56,    78,    73,    57,    85,    57,
      56,    80,    57,    95,   106,    95,    95,    95,    80,   106,
      57,    57,    67,    85,    57,    94,    57,    57,    57,    57,
      85,    57,    57,    57,    56,    57,    57,    82,    86,    95,
      57,    57
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    60,    61,    61,    61,    62,    63,    63,    64,    64,
      64,    64,    64,    64,    64,    64,    64,    64,    64,    64,
      64,    64,    64,    64,    64,    64,    64,    64,    64,    64,
      64,    64,    64,    64,    64,    64,    64,    64,    64,    65,
      65,    66,    66,    67,    67,    68,    69,    69,    70,    71,
      71,    72,    73,    73,    73,    73,    73,    73,    73,    73,
      73,    74,    74,    75,    75,    76,    77,    77,    78,    78,
      79,    79,    79,    79,    79,    80,    80,    80,    80,    81,
      81,    82,    82,    83,    83,    84,    84,    85,    85,    86,
      86,    87,    87,    88,    88,    89,    90,    90,    91,    92,
      92,    93,    93,    94,    94,    95,    95,    96,    96,    97,
      97,    97,    98,    98,    98,    98,    99,    99,   100,   100,
     101,   101,   102,   103,   103,   104,   105,   105,   106,   106,
     107,   108,   109,   110,   110,   110,   111,   111,   112,   113,
     113,   114,   114,   115,   115,   116,   116,   116,   117,   117,
     117,   118,   119,   119,   120,   120
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     1,     1,     1,     1,     1,     2,     4,     3,
       6,     5,     5,     9,     8,     5,     4,     9,     4,     4,
       8,     4,     3,     3,     3,     4,     3,     4,     3,     3,
       3,     4,     4,     4,     3,     3,     4,     4,     4,     1,
       2,     3,     9,     1,     2,     4,     0,     2,     4,     1,
       2,     4,     1,     1,     4,     7,     7,     7,     7,     5,
       3,     1,     2,     1,     2,     4,     1,     4,     1,     5,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       5,     1,     5,     1,     1,     1,     2,     1,     4,     1,
       2,     0,     2,     4,     5,     4,     1,     2,     4,     1,
       2,     0,     2,     1,     2,     0,     2,     1,     2,     1,
       1,     3,     1,     1,     1,     3,     1,     2,     1,     4,
       0,     2,     7,     1,     2,     6,     0,     2,     1,     2,
       1,     1,     5,     4,     4,     1,     1,     2,     5,     1,
       2,     1,    11,     1,     2,     5,     5,     5,     1,     1,
       1,     5,     4,     1,     1,     2
};


#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)
#define YYEMPTY         (-2)
#define YYEOF           0

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                  \
do                                                              \
  if (yychar == YYEMPTY)                                        \
    {                                                           \
      yychar = (Token);                                         \
      yylval = (Value);                                         \
      YYPOPSTACK (yylen);                                       \
      yystate = *yyssp;                                         \
      goto yybackup;                                            \
    }                                                           \
  else                                                          \
    {                                                           \
      yyerror (parser, YY_("syntax error: cannot back up")); \
      YYERROR;                                                  \
    }                                                           \
while (0)

/* Error token number */
#define YYTERROR        1
#define YYERRCODE       256


/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)                                \
    do                                                                  \
      if (N)                                                            \
        {                                                               \
          (Current).first_line   = YYRHSLOC (Rhs, 1).first_line;        \
          (Current).first_column = YYRHSLOC (Rhs, 1).first_column;      \
          (Current).last_line    = YYRHSLOC (Rhs, N).last_line;         \
          (Current).last_column  = YYRHSLOC (Rhs, N).last_column;       \
        }                                                               \
      else                                                              \
        {                                                               \
          (Current).first_line   = (Current).last_line   =              \
            YYRHSLOC (Rhs, 0).last_line;                                \
          (Current).first_column = (Current).last_column =              \
            YYRHSLOC (Rhs, 0).last_column;                              \
        }                                                               \
    while (0)
#endif

#define YYRHSLOC(Rhs, K) ((Rhs)[K])


/* Enable debugging if requested.  */
#if SMT_YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)


/* YY_LOCATION_PRINT -- Print the location on the stream.
   This macro was not mandated originally: define only if we know
   we won't break user code: when these are the locations we know.  */

#ifndef YY_LOCATION_PRINT
# if defined SMT_YYLTYPE_IS_TRIVIAL && SMT_YYLTYPE_IS_TRIVIAL

/* Print *YYLOCP on YYO.  Private, do not rely on its existence. */

YY_ATTRIBUTE_UNUSED
static unsigned
yy_location_print_ (FILE *yyo, YYLTYPE const * const yylocp)
{
  unsigned res = 0;
  int end_col = 0 != yylocp->last_column ? yylocp->last_column - 1 : 0;
  if (0 <= yylocp->first_line)
    {
      res += YYFPRINTF (yyo, "%d", yylocp->first_line);
      if (0 <= yylocp->first_column)
        res += YYFPRINTF (yyo, ".%d", yylocp->first_column);
    }
  if (0 <= yylocp->last_line)
    {
      if (yylocp->first_line < yylocp->last_line)
        {
          res += YYFPRINTF (yyo, "-%d", yylocp->last_line);
          if (0 <= end_col)
            res += YYFPRINTF (yyo, ".%d", end_col);
        }
      else if (0 <= end_col && yylocp->first_column < end_col)
        res += YYFPRINTF (yyo, "-%d", end_col);
    }
  return res;
 }

#  define YY_LOCATION_PRINT(File, Loc)          \
  yy_location_print_ (File, &(Loc))

# else
#  define YY_LOCATION_PRINT(File, Loc) ((void) 0)
# endif
#endif


# define YY_SYMBOL_PRINT(Title, Type, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Type, Value, Location, parser); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*----------------------------------------.
| Print this symbol's value on YYOUTPUT.  |
`----------------------------------------*/

static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, SmtPrsr parser)
{
  FILE *yyo = yyoutput;
  YYUSE (yyo);
  YYUSE (yylocationp);
  YYUSE (parser);
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# endif
  YYUSE (yytype);
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, SmtPrsr parser)
{
  YYFPRINTF (yyoutput, "%s %s (",
             yytype < YYNTOKENS ? "token" : "nterm", yytname[yytype]);

  YY_LOCATION_PRINT (yyoutput, *yylocationp);
  YYFPRINTF (yyoutput, ": ");
  yy_symbol_value_print (yyoutput, yytype, yyvaluep, yylocationp, parser);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yytype_int16 *yybottom, yytype_int16 *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yytype_int16 *yyssp, YYSTYPE *yyvsp, YYLTYPE *yylsp, int yyrule, SmtPrsr parser)
{
  unsigned long int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       yystos[yyssp[yyi + 1 - yynrhs]],
                       &(yyvsp[(yyi + 1) - (yynrhs)])
                       , &(yylsp[(yyi + 1) - (yynrhs)])                       , parser);
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, yylsp, Rule, parser); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !SMT_YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !SMT_YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif


#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
static YYSIZE_T
yystrlen (const char *yystr)
{
  YYSIZE_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
yystpcpy (char *yydest, const char *yysrc)
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYSIZE_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYSIZE_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
        switch (*++yyp)
          {
          case '\'':
          case ',':
            goto do_not_strip_quotes;

          case '\\':
            if (*++yyp != '\\')
              goto do_not_strip_quotes;
            /* Fall through.  */
          default:
            if (yyres)
              yyres[yyn] = *yyp;
            yyn++;
            break;

          case '"':
            if (yyres)
              yyres[yyn] = '\0';
            return yyn;
          }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return yystrlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.

   Return 0 if *YYMSG was successfully written.  Return 1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return 2 if the
   required number of bytes is too large to store.  */
static int
yysyntax_error (YYSIZE_T *yymsg_alloc, char **yymsg,
                yytype_int16 *yyssp, int yytoken)
{
  YYSIZE_T yysize0 = yytnamerr (YY_NULLPTR, yytname[yytoken]);
  YYSIZE_T yysize = yysize0;
  enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULLPTR;
  /* Arguments of yyformat. */
  char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
  /* Number of reported tokens (one for the "unexpected", one per
     "expected"). */
  int yycount = 0;

  /* There are many possibilities here to consider:
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yytoken != YYEMPTY)
    {
      int yyn = yypact[*yyssp];
      yyarg[yycount++] = yytname[yytoken];
      if (!yypact_value_is_default (yyn))
        {
          /* Start YYX at -YYN if negative to avoid negative indexes in
             YYCHECK.  In other words, skip the first -YYN actions for
             this state because they are default actions.  */
          int yyxbegin = yyn < 0 ? -yyn : 0;
          /* Stay within bounds of both yycheck and yytname.  */
          int yychecklim = YYLAST - yyn + 1;
          int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
          int yyx;

          for (yyx = yyxbegin; yyx < yyxend; ++yyx)
            if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR
                && !yytable_value_is_error (yytable[yyx + yyn]))
              {
                if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                  {
                    yycount = 1;
                    yysize = yysize0;
                    break;
                  }
                yyarg[yycount++] = yytname[yyx];
                {
                  YYSIZE_T yysize1 = yysize + yytnamerr (YY_NULLPTR, yytname[yyx]);
                  if (! (yysize <= yysize1
                         && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
                    return 2;
                  yysize = yysize1;
                }
              }
        }
    }

  switch (yycount)
    {
# define YYCASE_(N, S)                      \
      case N:                               \
        yyformat = S;                       \
      break
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
# undef YYCASE_
    }

  {
    YYSIZE_T yysize1 = yysize + yystrlen (yyformat);
    if (! (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
      return 2;
    yysize = yysize1;
  }

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return 1;
    }

  /* Avoid sprintf, as that infringes on the user's name space.
     Don't have undefined behavior even if the translation
     produced a string with the wrong number of "%s"s.  */
  {
    char *yyp = *yymsg;
    int yyi = 0;
    while ((*yyp = *yyformat) != '\0')
      if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
        {
          yyp += yytnamerr (yyp, yyarg[yyi++]);
          yyformat += 2;
        }
      else
        {
          yyp++;
          yyformat++;
        }
  }
  return 0;
}
#endif /* YYERROR_VERBOSE */

/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep, YYLTYPE *yylocationp, SmtPrsr parser)
{
  YYUSE (yyvaluep);
  YYUSE (yylocationp);
  YYUSE (parser);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YYUSE (yytype);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}




/* The lookahead symbol.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;
/* Location data for the lookahead symbol.  */
YYLTYPE yylloc
# if defined SMT_YYLTYPE_IS_TRIVIAL && SMT_YYLTYPE_IS_TRIVIAL
  = { 1, 1, 1, 1 }
# endif
;
/* Number of syntax errors so far.  */
int yynerrs;


/*----------.
| yyparse.  |
`----------*/

int
yyparse (SmtPrsr parser)
{
    int yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       'yyss': related to states.
       'yyvs': related to semantic values.
       'yyls': related to locations.

       Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* The state stack.  */
    yytype_int16 yyssa[YYINITDEPTH];
    yytype_int16 *yyss;
    yytype_int16 *yyssp;

    /* The semantic value stack.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs;
    YYSTYPE *yyvsp;

    /* The location stack.  */
    YYLTYPE yylsa[YYINITDEPTH];
    YYLTYPE *yyls;
    YYLTYPE *yylsp;

    /* The locations where the error started and ended.  */
    YYLTYPE yyerror_range[3];

    YYSIZE_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken = 0;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;
  YYLTYPE yyloc;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N), yylsp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yyssp = yyss = yyssa;
  yyvsp = yyvs = yyvsa;
  yylsp = yyls = yylsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY; /* Cause a token to be read.  */
  yylsp[0] = yylloc;
  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyss + yystacksize - 1 <= yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
        /* Give user a chance to reallocate the stack.  Use copies of
           these so that the &'s don't force the real ones into
           memory.  */
        YYSTYPE *yyvs1 = yyvs;
        yytype_int16 *yyss1 = yyss;
        YYLTYPE *yyls1 = yyls;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * sizeof (*yyssp),
                    &yyvs1, yysize * sizeof (*yyvsp),
                    &yyls1, yysize * sizeof (*yylsp),
                    &yystacksize);

        yyls = yyls1;
        yyss = yyss1;
        yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyexhaustedlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
        goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yytype_int16 *yyss1 = yyss;
        union yyalloc *yyptr =
          (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
        if (! yyptr)
          goto yyexhaustedlab;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
        YYSTACK_RELOCATE (yyls_alloc, yyls);
#  undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;
      yylsp = yyls + yysize - 1;

      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
                  (unsigned long int) yystacksize));

      if (yyss + yystacksize - 1 <= yyssp)
        YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid lookahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = yylex ();
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token.  */
  yychar = YYEMPTY;

  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END
  *++yylsp = yylloc;
  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     '$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];

  /* Default location.  */
  YYLLOC_DEFAULT (yyloc, (yylsp - yylen), yylen);
  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 2:
#line 61 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { (yyval.ptr) = (yyvsp[0].ptr); ast_setAst(parser, (yyvsp[0].ptr)); }
#line 1710 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 3:
#line 63 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { (yyval.ptr) = (yyvsp[0].ptr); ast_setAst(parser, (yyvsp[0].ptr)); }
#line 1716 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 4:
#line 65 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { (yyval.ptr) = (yyvsp[0].ptr); ast_setAst(parser, (yyvsp[0].ptr)); }
#line 1722 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 5:
#line 70 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newScript((yyvsp[0].list));

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1737 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 6:
#line 84 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 	
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 1751 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 7:
#line 95 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 1765 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 8:
#line 108 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newAssertCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1780 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 9:
#line 120 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newCheckSatCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1795 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 10:
#line 132 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newCheckSatAssumCommand((yyvsp[-2].list)); 

			(yyloc).first_line = (yylsp[-5]).first_line;
            (yyloc).first_column = (yylsp[-5]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1810 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 11:
#line 144 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newDeclareConstCommand((yyvsp[-2].ptr), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1825 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 12:
#line 156 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newDeclareDatatypeCommand((yyvsp[-2].ptr), (yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-4]).first_line;
			(yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1840 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 13:
#line 168 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newDeclareDatatypesCommand((yyvsp[-5].list), (yyvsp[-2].list));

			(yyloc).first_line = (yylsp[-8]).first_line;
			(yyloc).first_column = (yylsp[-8]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1855 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 14:
#line 180 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newDeclareFunCommand((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-7]).first_line;
            (yyloc).first_column = (yylsp[-7]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1870 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 15:
#line 192 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newDeclareSortCommand((yyvsp[-2].ptr), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1885 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 16:
#line 204 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newDeclareHeapCommand((yyvsp[-1].pairList));

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1900 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 17:
#line 216 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newDefineFunsRecCommand((yyvsp[-5].list), (yyvsp[-2].list)); 

			(yyloc).first_line = (yylsp[-8]).first_line;
            (yyloc).first_column = (yylsp[-8]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1915 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 18:
#line 228 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newDefineFunRecCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1930 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 19:
#line 240 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newDefineFunCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1945 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 20:
#line 252 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newDefineSortCommand((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-7]).first_line;
            (yyloc).first_column = (yylsp[-7]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1960 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 21:
#line 264 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newEchoCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1975 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 22:
#line 276 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newExitCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1990 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 23:
#line 288 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newGetAssertsCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2005 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 24:
#line 300 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newGetAssignsCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2020 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 25:
#line 312 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newGetInfoCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2035 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 26:
#line 324 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newGetModelCommand(); 
			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[-2]).last_line;
            (yyloc).last_column = (yylsp[-2]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2049 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 27:
#line 335 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newGetOptionCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2064 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 28:
#line 347 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newGetProofCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2079 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 29:
#line 359 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newGetModelCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2094 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 30:
#line 371 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newGetUnsatCoreCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2109 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 31:
#line 383 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newGetValueCommand((yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2124 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 32:
#line 395 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newPopCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2139 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 33:
#line 407 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newPushCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2154 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 34:
#line 419 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newResetAssertsCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2169 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 35:
#line 431 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newResetCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2184 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 36:
#line 443 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newSetInfoCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2199 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 37:
#line 455 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newSetLogicCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
            (yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2214 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 38:
#line 467 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newSetOptionCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2229 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 39:
#line 481 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.list) = ast_listCreate();
			ast_listAdd((yyval.list), (yyvsp[0].ptr));

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2243 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 40:
#line 492 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr));
			(yyval.list) = (yyvsp[-1].list);

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2257 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 41:
#line 505 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newSimpleDatatypeDeclaration((yyvsp[-1].list));

			(yyloc).first_line = (yylsp[-2]).first_line;
			(yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2272 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 42:
#line 517 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newParametricDatatypeDeclaration((yyvsp[-5].list), (yyvsp[-2].list));

			(yyloc).first_line = (yylsp[-8]).first_line;
			(yyloc).first_column = (yylsp[-8]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2287 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 43:
#line 531 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.list) = ast_listCreate();
			ast_listAdd((yyval.list), (yyvsp[0].ptr));

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2301 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 44:
#line 542 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr));
			(yyval.list) = (yyvsp[-1].list);

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2315 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 45:
#line 555 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newConstructorDeclaration((yyvsp[-2].ptr), (yyvsp[-1].list));

			(yyloc).first_line = (yylsp[-3]).first_line;
			(yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2330 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 46:
#line 569 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.list) = ast_listCreate();
		}
#line 2338 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 47:
#line 574 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr));
			(yyval.list) = (yyvsp[-1].list);

			if(!(yylsp[-1]).first_line) {
				(yyloc).first_line = (yylsp[0]).first_line;
            	(yyloc).first_column = (yylsp[0]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
			} else {
				(yyloc).first_line = (yylsp[-1]).first_line;
            	(yyloc).first_column = (yylsp[-1]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
			}
		}
#line 2359 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 48:
#line 594 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newSelectorDeclaration((yyvsp[-2].ptr), (yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-3]).first_line;
			(yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2374 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 49:
#line 608 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.list) = ast_listCreate();
			ast_listAdd((yyval.list), (yyvsp[0].ptr));

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2388 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 50:
#line 619 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr));
			(yyval.list) = (yyvsp[-1].list);

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2402 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 51:
#line 632 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newSortDeclaration((yyvsp[-2].ptr), (yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2417 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 52:
#line 646 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2430 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 53:
#line 656 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2443 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 54:
#line 666 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newQualifiedTerm((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2458 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 55:
#line 678 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newLetTerm((yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-6]).first_line;
            (yyloc).first_column = (yylsp[-6]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2473 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 56:
#line 690 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newForallTerm((yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-6]).first_line;
            (yyloc).first_column = (yylsp[-6]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2488 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 57:
#line 702 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newExistsTerm((yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-6]).first_line;
            (yyloc).first_column = (yylsp[-6]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2503 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 58:
#line 714 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newMatchTerm((yyvsp[-4].ptr), (yyvsp[-2].list));

			(yyloc).first_line = (yylsp[-6]).first_line;
            (yyloc).first_column = (yylsp[-6]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2518 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 59:
#line 726 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newAnnotatedTerm((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[-1]).last_line;
            (yyloc).last_column = (yylsp[-1]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2533 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 60:
#line 738 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[-1].ptr); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2548 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 61:
#line 752 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2562 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 62:
#line 763 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2576 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 63:
#line 776 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.list) = ast_listCreate();
			ast_listAdd((yyval.list), (yyvsp[0].ptr));

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2590 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 64:
#line 787 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr));
			(yyval.list) = (yyvsp[-1].list);

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2604 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 65:
#line 800 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newMatchCase((yyvsp[-2].ptr), (yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-3]).first_line;
			(yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2619 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 66:
#line 814 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = (yyvsp[0].ptr);

			(yyloc).first_line = (yylsp[0]).first_line;
			(yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2632 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 67:
#line 824 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newQualifiedPattern((yyvsp[-2].ptr), (yyvsp[-1].list));

			(yyloc).first_line = (yylsp[-3]).first_line;
			(yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2647 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 68:
#line 838 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = (yyvsp[0].ptr);

			(yyloc).first_line = (yylsp[0]).first_line;
			(yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2660 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 69:
#line 848 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newQualifiedConstructor((yyvsp[-2].ptr), (yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-4]).first_line;
			(yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[-1]).last_line;
			(yyloc).last_column = (yylsp[-1]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2675 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 70:
#line 862 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2690 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 71:
#line 874 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2705 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 72:
#line 886 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2720 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 73:
#line 898 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2735 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 74:
#line 910 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2750 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 75:
#line 924 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = (yyvsp[0].ptr);

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2765 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 76:
#line 936 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newSymbol("reset");

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2780 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 77:
#line 948 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newSymbol("not");

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2795 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 78:
#line 960 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newSymbol("_");

			(yyloc).first_line = (yylsp[0]).first_line;
			(yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2810 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 79:
#line 974 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2823 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 80:
#line 984 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newQualifiedIdentifier((yyvsp[-2].ptr), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2838 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 81:
#line 998 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newSimpleIdentifier1((yyvsp[0].ptr));

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2853 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 82:
#line 1010 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newSimpleIdentifier2((yyvsp[-2].ptr), (yyvsp[-1].list));

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2868 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 83:
#line 1024 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2883 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 84:
#line 1036 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2898 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 85:
#line 1050 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2912 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 86:
#line 1061 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2926 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 87:
#line 1074 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newSort1((yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2941 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 88:
#line 1086 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newSort2((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2956 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 89:
#line 1100 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2970 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 90:
#line 1111 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2984 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 91:
#line 1124 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate();
		}
#line 2992 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 92:
#line 1129 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			if(!(yylsp[-1]).first_line) {
				(yyloc).first_line = (yylsp[0]).first_line;
            	(yyloc).first_column = (yylsp[0]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
			} else {
				(yyloc).first_line = (yylsp[-1]).first_line;
            	(yyloc).first_column = (yylsp[-1]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
			}
		}
#line 3013 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 93:
#line 1149 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.pairList) = ast_pairListCreate();
			ast_pairListAdd((yyval.pairList), (yyvsp[-2].ptr), (yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[-1]).last_line;
            (yyloc).last_column = (yylsp[-1]).last_column;
		}
#line 3027 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 94:
#line 1160 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			ast_pairListAdd((yyvsp[-4].pairList), (yyvsp[-2].ptr), (yyvsp[-1].ptr));
			(yyval.pairList) = (yyvsp[-4].pairList);

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3041 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 95:
#line 1173 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newVariableBinding((yyvsp[-2].ptr), (yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[-1]).last_line;
            (yyloc).last_column = (yylsp[-1]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3056 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 96:
#line 1187 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3070 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 97:
#line 1198 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3084 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 98:
#line 1211 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newSortedVariable((yyvsp[-2].ptr), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[-1]).last_line;
            (yyloc).last_column = (yylsp[-1]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3099 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 99:
#line 1225 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3113 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 100:
#line 1236 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3127 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 101:
#line 1249 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { (yyval.list) = ast_listCreate(); }
#line 3133 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 102:
#line 1252 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			if(!(yylsp[-1]).first_line) {
				(yyloc).first_line = (yylsp[0]).first_line;
            	(yyloc).first_column = (yylsp[0]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
        	} else {
        		(yyloc).first_line = (yylsp[-1]).first_line;
            	(yyloc).first_column = (yylsp[-1]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
        	}
		}
#line 3154 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 103:
#line 1272 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newAttribute1((yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3169 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 104:
#line 1284 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newAttribute2((yyvsp[-1].ptr), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3184 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 105:
#line 1298 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { (yyval.list) = ast_listCreate(); }
#line 3190 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 106:
#line 1301 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			if(!(yylsp[-1]).first_line) {
				(yyloc).first_line = (yylsp[0]).first_line;
            	(yyloc).first_column = (yylsp[0]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
        	} else {
        		(yyloc).first_line = (yylsp[-1]).first_line;
            	(yyloc).first_column = (yylsp[-1]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
        	}
		}
#line 3211 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 107:
#line 1321 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3225 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 108:
#line 1332 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
        	(yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
        	(yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3239 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 109:
#line 1345 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3252 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 110:
#line 1355 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3265 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 111:
#line 1365 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newCompSExpression((yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3280 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 112:
#line 1379 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3293 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 113:
#line 1389 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3306 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 114:
#line 1399 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3319 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 115:
#line 1409 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newCompSExpression((yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3334 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 116:
#line 1423 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3348 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 117:
#line 1434 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3362 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 118:
#line 1447 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newPropLiteral((yyvsp[0].ptr), 0); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3377 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 119:
#line 1459 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newPropLiteral((yyvsp[-1].ptr), 1); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3392 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 120:
#line 1473 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { (yyval.list) = ast_listCreate(); }
#line 3398 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 121:
#line 1477 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			if(!(yylsp[-1]).first_line) {
				(yyloc).first_line = (yylsp[0]).first_line;
            	(yyloc).first_column = (yylsp[0]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
        	} else {
        		(yyloc).first_line = (yylsp[-1]).first_line;
            	(yyloc).first_column = (yylsp[-1]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
        	}
		}
#line 3419 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 122:
#line 1497 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newFunctionDeclaration((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-6]).first_line;
            (yyloc).first_column = (yylsp[-6]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3434 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 123:
#line 1511 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3448 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 124:
#line 1522 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3462 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 125:
#line 1535 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newFunctionDefinition(
				ast_newFunctionDeclaration((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[-5]).first_line;
            (yyloc).first_column = (yylsp[-5]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3478 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 126:
#line 1550 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { (yyval.list) = ast_listCreate(); }
#line 3484 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 127:
#line 1553 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			if(!(yylsp[-1]).first_line) {
				(yyloc).first_line = (yylsp[0]).first_line;
            	(yyloc).first_column = (yylsp[0]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
        	} else {
        		(yyloc).first_line = (yylsp[-1]).first_line;
            	(yyloc).first_column = (yylsp[-1]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
        	}
		}
#line 3505 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 128:
#line 1573 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3519 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 129:
#line 1584 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3533 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 130:
#line 1597 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3548 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 131:
#line 1611 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3561 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 132:
#line 1623 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newTheory((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3576 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 133:
#line 1637 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newAttribute2((yyvsp[-3].ptr), 
				ast_newCompAttributeValue((yyvsp[-1].list)));

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3592 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 134:
#line 1650 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newAttribute2((yyvsp[-3].ptr), 
				ast_newCompAttributeValue((yyvsp[-1].list)));

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3608 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 135:
#line 1663 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3621 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 136:
#line 1675 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3635 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 137:
#line 1686 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3649 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 138:
#line 1699 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newSortSymbolDeclaration((yyvsp[-3].ptr), (yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3664 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 139:
#line 1713 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3678 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 140:
#line 1724 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3692 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 142:
#line 1739 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newParametricFunDeclaration((yyvsp[-7].list), (yyvsp[-4].ptr), (yyvsp[-3].list), (yyvsp[-2].list));

			(yyloc).first_line = (yylsp[-10]).first_line;
            (yyloc).first_column = (yylsp[-10]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3707 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 143:
#line 1753 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3721 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 144:
#line 1764 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list);

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column; 
		}
#line 3735 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 145:
#line 1777 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newSpecConstFunDeclaration((yyvsp[-3].ptr), (yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3750 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 146:
#line 1789 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newMetaSpecConstFunDeclaration((yyvsp[-3].ptr), (yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3765 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 147:
#line 1801 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newSimpleFunDeclaration((yyvsp[-3].ptr), (yyvsp[-2].list), (yyvsp[-1].list));

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3780 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 148:
#line 1815 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3795 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 149:
#line 1827 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3810 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 150:
#line 1839 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3825 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 151:
#line 1853 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newLogic((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3840 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 152:
#line 1867 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newAttribute2((yyvsp[-3].ptr), ast_newCompAttributeValue((yyvsp[-1].list)));

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3855 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 153:
#line 1879 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3868 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 154:
#line 1891 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3882 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 155:
#line 1902 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3896 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;


#line 3900 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;
  *++yylsp = yyloc;

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYEMPTY : YYTRANSLATE (yychar);

  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (parser, YY_("syntax error"));
#else
# define YYSYNTAX_ERROR yysyntax_error (&yymsg_alloc, &yymsg, \
                                        yyssp, yytoken)
      {
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        yysyntax_error_status = YYSYNTAX_ERROR;
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == 1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = (char *) YYSTACK_ALLOC (yymsg_alloc);
            if (!yymsg)
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = 2;
              }
            else
              {
                yysyntax_error_status = YYSYNTAX_ERROR;
                yymsgp = yymsg;
              }
          }
        yyerror (parser, yymsgp);
        if (yysyntax_error_status == 2)
          goto yyexhaustedlab;
      }
# undef YYSYNTAX_ERROR
#endif
    }

  yyerror_range[1] = yylloc;

  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
         error, discard it.  */

      if (yychar <= YYEOF)
        {
          /* Return failure if at end of input.  */
          if (yychar == YYEOF)
            YYABORT;
        }
      else
        {
          yydestruct ("Error: discarding",
                      yytoken, &yylval, &yylloc, parser);
          yychar = YYEMPTY;
        }
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:

  /* Pacify compilers like GCC when the user code never invokes
     YYERROR and the label yyerrorlab therefore never appears in user
     code.  */
  if (/*CONSTCOND*/ 0)
     goto yyerrorlab;

  yyerror_range[1] = yylsp[1-yylen];
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;      /* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYTERROR;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
            {
              yyn = yytable[yyn];
              if (0 < yyn)
                break;
            }
        }

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
        YYABORT;

      yyerror_range[1] = *yylsp;
      yydestruct ("Error: popping",
                  yystos[yystate], yyvsp, yylsp, parser);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  yyerror_range[2] = yylloc;
  /* Using YYLLOC is tempting, but would change the location of
     the lookahead.  YYLOC is available though.  */
  YYLLOC_DEFAULT (yyloc, yyerror_range, 2);
  *++yylsp = yyloc;

  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#if !defined yyoverflow || YYERROR_VERBOSE
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (parser, YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval, &yylloc, parser);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  yystos[*yyssp], yyvsp, yylsp, parser);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  return yyresult;
}
#line 1913 "smtlib-bison-parser.y" /* yacc.c:1906  */


void yyerror(SmtPrsr parser, const char* s) {
	ast_reportError(parser, yylloc.first_line, yylloc.first_column,
					yylloc.last_line, yylloc.last_column, s);
}
