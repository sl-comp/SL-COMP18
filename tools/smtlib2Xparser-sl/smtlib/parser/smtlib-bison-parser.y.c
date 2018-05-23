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
#line 20 "smtlib-bison-parser.y" /* yacc.c:355  */

	AstPtr ptr;
	AstList list;
	AstPairList pairList;

#line 199 "smtlib-bison-parser.tab.c" /* yacc.c:355  */
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

#line 230 "smtlib-bison-parser.tab.c" /* yacc.c:358  */

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
#define YYFINAL  42
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   571

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  61
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  61
/* YYNRULES -- Number of rules.  */
#define YYNRULES  156
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  364

/* YYTRANSLATE[YYX] -- Symbol number corresponding to YYX as returned
   by yylex, with out-of-bounds checking.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   311

#define YYTRANSLATE(YYX)                                                \
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, without out-of-bounds checking.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    59,     2,     2,     2,     2,     2,     2,
      57,    58,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,    60,     2,     2,     2,     2,
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
      55,    56
};

#if SMT_YYDEBUG
  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,    61,    61,    63,    65,    69,    83,    94,   107,   119,
     131,   143,   155,   167,   179,   191,   203,   215,   227,   239,
     251,   263,   275,   287,   299,   311,   323,   335,   346,   358,
     370,   382,   394,   406,   418,   430,   442,   454,   466,   478,
     492,   503,   516,   528,   542,   553,   566,   581,   585,   605,
     619,   630,   643,   657,   667,   677,   689,   701,   713,   725,
     737,   749,   763,   774,   787,   798,   811,   825,   835,   849,
     859,   873,   885,   897,   909,   921,   935,   947,   959,   971,
     985,   995,  1009,  1021,  1035,  1047,  1061,  1072,  1085,  1097,
    1111,  1122,  1136,  1140,  1160,  1171,  1184,  1198,  1209,  1222,
    1236,  1247,  1261,  1263,  1283,  1295,  1310,  1312,  1332,  1343,
    1356,  1366,  1376,  1390,  1400,  1410,  1420,  1434,  1445,  1458,
    1470,  1485,  1488,  1508,  1522,  1533,  1546,  1562,  1564,  1584,
    1595,  1608,  1622,  1634,  1648,  1661,  1674,  1686,  1697,  1710,
    1724,  1735,  1748,  1750,  1764,  1775,  1788,  1800,  1812,  1826,
    1838,  1850,  1864,  1878,  1890,  1902,  1913
};
#endif

#if SMT_YYDEBUG || YYERROR_VERBOSE || 1
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "KW_AS", "KW_LET", "KW_FORALL",
  "KW_EXISTS", "KW_MATCH", "KW_PAR", "NOT", "NUMERAL", "DECIMAL",
  "HEXADECIMAL", "BINARY", "KW_ASSERT", "KW_CHK_SAT", "KW_CHK_UNSAT",
  "KW_CHK_SAT_ASSUM", "KW_DECL_CONST", "KW_DECL_FUN", "KW_DECL_SORT",
  "KW_DECL_HEAP", "KW_DEF_FUN", "KW_DEF_FUN_REC", "KW_DEF_FUNS_REC",
  "KW_DEF_SORT", "KW_ECHO", "KW_EXIT", "KW_GET_ASSERTS", "KW_GET_ASSIGNS",
  "KW_GET_INFO", "KW_GET_MODEL", "KW_GET_OPT", "KW_GET_PROOF",
  "KW_GET_UNSAT_ASSUMS", "KW_GET_UNSAT_CORE", "KW_GET_VALUE", "KW_POP",
  "KW_PUSH", "KW_RESET", "KW_RESET_ASSERTS", "KW_SET_INFO", "KW_SET_LOGIC",
  "KW_SET_OPT", "KW_DECL_DATATYPE", "KW_DECL_DATATYPES",
  "META_SPEC_DECIMAL", "META_SPEC_NUMERAL", "META_SPEC_STRING", "KEYWORD",
  "STRING", "SYMBOL", "THEORY", "LOGIC", "KW_ATTR_SORTS", "KW_ATTR_FUNS",
  "KW_ATTR_THEORIES", "'('", "')'", "'!'", "'_'", "$accept", "smt_file",
  "script", "command_plus", "command", "datatype_decl_plus",
  "datatype_decl", "constructor_decl_plus", "constructor_decl",
  "selector_decl_star", "selector_decl", "sort_decl_plus", "sort_decl",
  "term", "term_plus", "match_case_plus", "match_case", "pattern",
  "qual_constructor", "spec_const", "symbol", "qual_identifier",
  "identifier", "index", "index_plus", "sort", "sort_plus", "sort_star",
  "sort_pair_plus", "var_binding", "var_binding_plus", "sorted_var",
  "sorted_var_plus", "sorted_var_star", "attribute", "attribute_star",
  "attribute_plus", "attr_value", "s_exp", "s_exp_plus", "prop_literal",
  "prop_literal_star", "fun_decl", "fun_decl_plus", "fun_def",
  "symbol_star", "symbol_plus", "info_flag", "option", "theory_decl",
  "theory_attr", "theory_attr_plus", "sort_symbol_decl",
  "sort_symbol_decl_plus", "par_fun_symbol_decl",
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
     305,   306,   307,   308,   309,   310,   311,    40,    41,    33,
      95
};
# endif

#define YYPACT_NINF -302

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-302)))

#define YYTABLE_NINF -1

#define yytable_value_is_error(Yytable_value) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int16 yypact[] =
{
     -34,   486,    31,  -302,     5,  -302,  -302,  -302,   419,    27,
      29,    33,    55,    55,    55,    36,    55,    55,    43,    55,
      47,    46,    53,    77,    91,    90,   102,    97,   105,   116,
     419,   182,   186,   140,   151,   165,    55,   165,    55,   159,
      55,    55,  -302,   526,  -302,  -302,  -302,  -302,  -302,  -302,
    -302,  -302,  -302,   290,  -302,   166,  -302,  -302,  -302,  -302,
    -302,  -302,  -302,    79,   161,   220,    79,    -1,   175,   195,
     197,   203,   207,   210,  -302,  -302,  -302,  -302,   221,  -302,
     230,  -302,  -302,  -302,  -302,   307,   232,   233,  -302,  -302,
     424,   246,   247,  -302,   249,   251,   252,    98,   -10,   160,
     254,   256,   257,   419,   419,    55,   266,   419,  -302,    16,
     271,  -302,   267,  -302,   268,    79,    79,  -302,  -302,  -302,
    -302,    55,  -302,   119,  -302,  -302,  -302,  -302,  -302,  -302,
    -302,  -302,   359,  -302,  -302,  -302,  -302,  -302,  -302,    12,
     269,    55,   128,  -302,   273,   277,  -302,  -302,   -14,   278,
    -302,  -302,    -6,   276,    79,   281,   282,   282,   285,   165,
      19,  -302,   367,   334,   286,  -302,  -302,    79,  -302,    74,
    -302,   287,    79,   130,   302,   303,  -302,    24,  -302,   359,
    -302,  -302,  -302,   133,   304,    55,   144,  -302,  -302,   352,
     309,  -302,   316,   317,  -302,  -302,  -302,  -302,  -302,    55,
     325,    55,  -302,   147,    55,  -302,   150,   164,   328,  -302,
      -7,  -302,  -302,  -302,   155,  -302,    55,  -302,  -302,   110,
      79,  -302,  -302,   329,    79,  -302,  -302,   419,    79,  -302,
     226,  -302,  -302,    55,  -302,  -302,  -302,   330,   251,   160,
    -302,   170,   343,  -302,   190,  -302,   194,  -302,   419,   419,
    -302,    79,   419,  -302,   419,   324,   192,  -302,  -302,  -302,
    -302,  -302,   337,  -302,  -302,   339,  -302,   419,   200,   402,
     341,  -302,  -302,   387,   205,  -302,   216,  -302,   376,  -302,
    -302,   335,  -302,  -302,  -302,    79,    79,    79,  -302,  -302,
    -302,   344,   346,   347,   349,   362,    21,   419,  -302,  -302,
     363,  -302,  -302,  -302,  -302,    79,   364,  -302,   366,  -302,
      55,  -302,  -302,   381,  -302,  -302,    55,  -302,    79,  -302,
    -302,  -302,  -302,  -302,  -302,    55,   398,    55,   382,  -302,
     384,  -302,   389,    79,  -302,    40,   434,    65,    75,    80,
      79,   439,  -302,  -302,   224,   386,  -302,  -302,   392,  -302,
    -302,  -302,   393,  -302,   396,  -302,   160,  -302,  -302,    79,
      79,    92,   397,  -302
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
       0,     0,     1,     0,     7,    78,    71,    72,    73,    74,
      77,    75,    76,     0,    79,     0,    53,    82,    54,    80,
       9,    10,   121,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    23,    24,    25,   131,     0,    27,
       0,    29,    30,    31,    62,     0,     0,     0,    36,    35,
     104,     0,     0,   132,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,    79,     0,    54,     8,     0,
       0,    88,     0,    92,     0,     0,     0,    17,   102,    20,
      19,     0,   124,     0,   127,    22,    26,    28,    32,    63,
      33,    34,     0,   110,   111,   105,    37,    38,    39,     0,
       0,     0,     0,    50,     0,     0,   136,   137,     0,     0,
     154,   155,     0,     0,     0,     0,     0,     0,     0,     0,
       0,    61,     0,     0,     0,   119,   122,     0,    12,     0,
      16,     0,     0,     0,     0,     0,   125,     0,   115,     0,
     113,   114,   117,     0,     0,     0,     0,    44,    13,     0,
       0,    51,     0,     0,   133,   138,   127,   152,   156,     0,
       0,     0,    97,     0,     0,   100,     0,     0,     0,   108,
       0,    84,    85,    86,     0,    55,     0,    11,    90,     0,
       0,    93,    94,     0,     0,   103,   102,     0,     0,   128,
       0,   112,   118,     0,    47,    42,    45,     0,     0,     0,
     140,     0,     0,   144,     0,   142,     0,    81,     0,     0,
      98,     0,     0,   101,     0,     0,     0,    64,    60,   109,
      83,    87,     0,    89,    91,     0,    95,     0,     0,     0,
       0,   116,   129,     0,     0,    52,     0,    40,     0,   134,
     141,     0,   150,   149,   151,     0,     0,     0,   135,   145,
     153,     0,     0,     0,     0,     0,     0,     0,    67,    69,
       0,    65,   120,    15,   126,     0,     0,    21,     0,   130,
       0,    46,    48,     0,    41,   106,     0,   106,   106,   106,
      96,    56,    99,    57,    58,     0,     0,     0,     0,    59,
       0,    18,     0,     0,    14,     0,     0,     0,     0,     0,
       0,     0,    66,   123,     0,     0,   139,   107,     0,   146,
     148,   147,     0,    68,     0,    49,     0,    70,    43,     0,
     106,     0,     0,   143
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -302,  -302,  -302,  -302,   446,  -302,  -227,   124,  -184,  -302,
    -302,  -302,   315,    18,  -101,  -302,   208,  -302,   169,   -71,
      -4,   408,    -8,   253,  -302,   -62,  -279,  -302,  -302,   263,
    -302,  -159,   311,   245,   -32,  -301,  -302,  -302,  -162,   293,
    -302,  -302,   354,  -302,   463,   291,  -289,  -302,  -302,  -302,
     338,  -302,   241,  -302,   239,  -302,  -302,  -302,  -302,   336,
    -302
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     2,     3,     4,     5,   276,   140,   186,   187,   274,
     312,   142,   143,    84,    85,   256,   257,   297,   298,    56,
      57,    58,   111,   213,   214,   218,   219,   169,    67,   202,
     203,   205,   206,   173,   347,   335,   210,   135,   182,   183,
     166,   109,   122,   123,    69,   177,   273,    78,    94,     6,
     147,   148,   240,   241,   243,   244,   245,   287,     7,   151,
     152
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_uint16 yytable[] =
{
      59,   112,   236,    91,   115,    93,   162,   318,    63,    64,
      65,   277,    68,    68,   225,    72,   337,   338,   339,   133,
     184,   232,    59,     1,   325,    45,    55,   336,    45,   211,
      45,    42,    92,    45,    95,    90,    97,    98,   341,    90,
     144,   145,    90,    90,   194,    59,   149,   253,   253,   314,
     149,   258,   197,   171,   172,    50,   116,   117,    50,   361,
      50,   180,    43,    50,    45,   146,   150,    52,   232,   185,
      52,   106,    52,   163,   164,    52,    54,    59,   326,    54,
     360,    54,   228,    45,    54,    60,   134,    61,    45,    90,
      62,   154,   200,    66,    50,    59,    59,    73,   346,    59,
      71,   160,   167,   129,    74,   165,    52,   221,   180,   225,
     223,    75,   180,    50,    90,    54,   146,   174,    50,    45,
     150,   158,   159,   349,    90,    52,   269,   209,   181,    90,
      52,   110,   220,   350,    54,    76,   110,   189,   351,    54,
      77,    90,    45,    46,    47,    48,    49,    90,    79,    50,
     362,    80,   144,   145,    59,    81,   212,   264,   265,   180,
     236,    52,   267,    82,    45,   211,   270,   110,   263,    45,
      54,   285,    50,   229,    83,   181,   121,   175,   259,   181,
     129,   234,   178,    51,    52,   141,   190,   204,   224,   293,
     179,   231,    86,    54,    50,   160,    87,   248,    88,    50,
     251,   185,   235,    45,   201,   249,    52,   204,   252,    89,
     212,    52,   262,   260,    90,    54,    96,   153,   113,    59,
      54,   204,   254,   317,   108,   319,   181,   239,   279,   272,
     114,   278,   118,    50,   286,    45,    46,    47,    48,    49,
      59,    59,   229,   330,    59,    52,    59,   242,   288,   255,
     300,   299,   290,   119,    54,   120,   264,   204,   305,    59,
     121,    59,   310,   311,   124,    50,   291,   292,   125,   309,
     294,   345,   295,   139,   313,   178,    51,    52,   352,   126,
      45,   185,   354,   179,   271,   304,    54,   129,   127,    59,
     130,   131,   299,    99,   100,   101,   102,   103,   264,    45,
      46,    47,    48,    49,   136,   137,   333,   138,   139,   141,
      50,   155,   272,   156,   157,   328,    45,    46,    47,    48,
      49,   340,    52,   272,   161,   168,   170,   188,   153,    50,
     192,   105,   309,    45,   193,   196,   199,   309,   201,   204,
      51,    52,   208,   216,   217,   222,    50,    53,   359,   104,
     105,   281,    45,    46,    47,    48,    49,    51,    52,   226,
     227,   233,   237,    50,    53,   128,   238,    54,    45,    46,
      47,    48,    49,   239,   242,    52,    45,    46,    47,    48,
      49,   296,    50,   247,    54,   255,   315,   266,   275,   282,
     283,   284,   316,    51,    52,   302,    45,   303,    50,   307,
     153,   325,   320,    54,   321,   322,    50,   323,   178,    51,
      52,    45,    46,    47,    48,    49,   179,    51,    52,    54,
     324,   329,   331,   332,    53,   215,    50,    54,    45,    46,
      47,    48,    49,    45,    46,    47,    48,    49,    52,   334,
     342,    50,   343,    45,   355,   308,   185,    54,    45,   356,
      44,   357,    51,    52,   358,   363,   344,   191,    50,    53,
     306,   107,    54,    50,   301,   327,   250,   261,   207,    51,
      52,   268,   230,    50,    51,    52,    53,   176,    50,    54,
      70,   132,   280,   289,    54,    52,   195,   246,   198,     0,
      52,     0,   348,     0,    54,     0,     0,   353,     0,    54,
       8,     9,    10,    11,    12,    13,    14,    15,    16,    17,
      18,    19,    20,    21,    22,    23,    24,    25,    26,    27,
      28,    29,    30,    31,    32,    33,    34,    35,    36,    37,
      38,    39,     0,     0,     0,     0,     0,     0,    40,    41,
       8,     9,    10,    11,    12,    13,    14,    15,    16,    17,
      18,    19,    20,    21,    22,    23,    24,    25,    26,    27,
      28,    29,    30,    31,    32,    33,    34,    35,    36,    37,
      38,    39
};

static const yytype_int16 yycheck[] =
{
       8,    63,   186,    35,    66,    37,   107,   286,    12,    13,
      14,   238,    16,    17,   173,    19,   317,   318,   319,    90,
       8,   183,    30,    57,     3,     9,     8,   316,     9,    10,
       9,     0,    36,     9,    38,    49,    40,    41,   327,    49,
      54,    55,    49,    49,    58,    53,    56,   206,   207,   276,
      56,    58,    58,   115,   116,    39,    57,    58,    39,   360,
      39,   132,    57,    39,     9,    97,    98,    51,   230,    57,
      51,    53,    51,    57,    58,    51,    60,    85,    57,    60,
     359,    60,    58,     9,    60,    58,    90,    58,     9,    49,
      57,    99,   154,    57,    39,   103,   104,    50,    58,   107,
      57,   105,   110,    85,    58,   109,    51,   169,   179,   268,
     172,    58,   183,    39,    49,    60,   148,   121,    39,     9,
     152,   103,   104,    58,    49,    51,   227,   159,   132,    49,
      51,    57,    58,    58,    60,    58,    57,   141,    58,    60,
      49,    49,     9,    10,    11,    12,    13,    49,    58,    39,
      58,    49,    54,    55,   162,    58,   160,   219,   220,   230,
     344,    51,   224,    58,     9,    10,   228,    57,    58,     9,
      60,   242,    39,   177,    58,   179,    57,    58,   210,   183,
     162,   185,    49,    50,    51,    57,    58,    57,    58,   251,
      57,    58,    10,    60,    39,   199,    10,   201,    58,    39,
     204,    57,    58,     9,    57,    58,    51,    57,    58,    58,
     214,    51,   216,    58,    49,    60,    57,    57,    57,   227,
      60,    57,    58,   285,    58,   287,   230,    57,    58,   233,
      10,   239,    57,    39,   242,     9,    10,    11,    12,    13,
     248,   249,   246,   305,   252,    51,   254,    57,    58,    57,
      58,   255,    58,    58,    60,    58,   318,    57,    58,   267,
      57,   269,    57,    58,    57,    39,   248,   249,    58,   273,
     252,   333,   254,    57,    58,    49,    50,    51,   340,    58,
       9,    57,    58,    57,    58,   267,    60,   269,    58,   297,
      58,    58,   296,     3,     4,     5,     6,     7,   360,     9,
      10,    11,    12,    13,    58,    58,   310,    58,    57,    57,
      39,    57,   316,    57,    57,   297,     9,    10,    11,    12,
      13,   325,    51,   327,    58,    58,    58,    58,    57,    39,
      57,    60,   336,     9,    57,    57,    60,   341,    57,    57,
      50,    51,    57,     9,    58,    58,    39,    57,   356,    59,
      60,     8,     9,    10,    11,    12,    13,    50,    51,    57,
      57,    57,    10,    39,    57,    58,    57,    60,     9,    10,
      11,    12,    13,    57,    57,    51,     9,    10,    11,    12,
      13,    57,    39,    58,    60,    57,    10,    58,    58,    46,
      47,    48,    57,    50,    51,    58,     9,    58,    39,    58,
      57,     3,    58,    60,    58,    58,    39,    58,    49,    50,
      51,     9,    10,    11,    12,    13,    57,    50,    51,    60,
      58,    58,    58,    57,    57,    58,    39,    60,     9,    10,
      11,    12,    13,     9,    10,    11,    12,    13,    51,    58,
      58,    39,    58,     9,    58,    58,    57,    60,     9,    57,
       4,    58,    50,    51,    58,    58,   332,   142,    39,    57,
      58,    53,    60,    39,   256,   296,   203,   214,   157,    50,
      51,   226,   179,    39,    50,    51,    57,   123,    39,    60,
      17,    57,   241,   244,    60,    51,   148,   196,   152,    -1,
      51,    -1,    58,    -1,    60,    -1,    -1,    58,    -1,    60,
      14,    15,    16,    17,    18,    19,    20,    21,    22,    23,
      24,    25,    26,    27,    28,    29,    30,    31,    32,    33,
      34,    35,    36,    37,    38,    39,    40,    41,    42,    43,
      44,    45,    -1,    -1,    -1,    -1,    -1,    -1,    52,    53,
      14,    15,    16,    17,    18,    19,    20,    21,    22,    23,
      24,    25,    26,    27,    28,    29,    30,    31,    32,    33,
      34,    35,    36,    37,    38,    39,    40,    41,    42,    43,
      44,    45
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,    57,    62,    63,    64,    65,   110,   119,    14,    15,
      16,    17,    18,    19,    20,    21,    22,    23,    24,    25,
      26,    27,    28,    29,    30,    31,    32,    33,    34,    35,
      36,    37,    38,    39,    40,    41,    42,    43,    44,    45,
      52,    53,     0,    57,    65,     9,    10,    11,    12,    13,
      39,    50,    51,    57,    60,    74,    80,    81,    82,    83,
      58,    58,    57,    81,    81,    81,    57,    89,    81,   105,
     105,    57,    81,    50,    58,    58,    58,    49,   108,    58,
      49,    58,    58,    58,    74,    75,    10,    10,    58,    58,
      49,    95,    81,    95,   109,    81,    57,    81,    81,     3,
       4,     5,     6,     7,    59,    60,    74,    82,    58,   102,
      57,    83,    86,    57,    10,    86,    57,    58,    57,    58,
      58,    57,   103,   104,    57,    58,    58,    58,    58,    74,
      58,    58,    57,    80,    81,    98,    58,    58,    58,    57,
      67,    57,    72,    73,    54,    55,    95,   111,   112,    56,
      95,   120,   121,    57,    83,    57,    57,    57,    74,    74,
      81,    58,    75,    57,    58,    81,   101,    83,    58,    88,
      58,    86,    86,    94,    81,    58,   103,   106,    49,    57,
      80,    81,    99,   100,     8,    57,    68,    69,    58,    81,
      58,    73,    57,    57,    58,   111,    57,    58,   120,    60,
      86,    57,    90,    91,    57,    92,    93,    93,    57,    95,
      97,    10,    81,    84,    85,    58,     9,    58,    86,    87,
      58,    86,    58,    86,    58,    92,    57,    57,    58,    81,
     100,    58,    99,    57,    81,    58,    69,    10,    57,    57,
     113,   114,    57,   115,   116,   117,   106,    58,    81,    58,
      90,    81,    58,    92,    58,    57,    76,    77,    58,    95,
      58,    84,    81,    58,    86,    86,    58,    86,    94,    75,
      86,    58,    81,   107,    70,    58,    66,    67,    83,    58,
     113,     8,    46,    47,    48,    80,    83,   118,    58,   115,
      58,    74,    74,    86,    74,    74,    57,    78,    79,    81,
      58,    77,    58,    58,    74,    58,    58,    58,    58,    81,
      57,    58,    71,    58,    67,    10,    57,    86,    87,    86,
      58,    58,    58,    58,    58,     3,    57,    79,    74,    58,
      86,    58,    57,    81,    58,    96,   107,    96,    96,    96,
      81,   107,    58,    58,    68,    86,    58,    95,    58,    58,
      58,    58,    86,    58,    58,    58,    57,    58,    58,    83,
      87,    96,    58,    58
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    61,    62,    62,    62,    63,    64,    64,    65,    65,
      65,    65,    65,    65,    65,    65,    65,    65,    65,    65,
      65,    65,    65,    65,    65,    65,    65,    65,    65,    65,
      65,    65,    65,    65,    65,    65,    65,    65,    65,    65,
      66,    66,    67,    67,    68,    68,    69,    70,    70,    71,
      72,    72,    73,    74,    74,    74,    74,    74,    74,    74,
      74,    74,    75,    75,    76,    76,    77,    78,    78,    79,
      79,    80,    80,    80,    80,    80,    81,    81,    81,    81,
      82,    82,    83,    83,    84,    84,    85,    85,    86,    86,
      87,    87,    88,    88,    89,    89,    90,    91,    91,    92,
      93,    93,    94,    94,    95,    95,    96,    96,    97,    97,
      98,    98,    98,    99,    99,    99,    99,   100,   100,   101,
     101,   102,   102,   103,   104,   104,   105,   106,   106,   107,
     107,   108,   109,   110,   111,   111,   111,   112,   112,   113,
     114,   114,   115,   115,   116,   116,   117,   117,   117,   118,
     118,   118,   119,   120,   120,   121,   121
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     1,     1,     1,     1,     1,     2,     4,     3,
       3,     6,     5,     5,     9,     8,     5,     4,     9,     4,
       4,     8,     4,     3,     3,     3,     4,     3,     4,     3,
       3,     3,     4,     4,     4,     3,     3,     4,     4,     4,
       1,     2,     3,     9,     1,     2,     4,     0,     2,     4,
       1,     2,     4,     1,     1,     4,     7,     7,     7,     7,
       5,     3,     1,     2,     1,     2,     4,     1,     4,     1,
       5,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     5,     1,     5,     1,     1,     1,     2,     1,     4,
       1,     2,     0,     2,     4,     5,     4,     1,     2,     4,
       1,     2,     0,     2,     1,     2,     0,     2,     1,     2,
       1,     1,     3,     1,     1,     1,     3,     1,     2,     1,
       4,     0,     2,     7,     1,     2,     6,     0,     2,     1,
       2,     1,     1,     5,     4,     4,     1,     1,     2,     5,
       1,     2,     1,    11,     1,     2,     5,     5,     5,     1,
       1,     1,     5,     4,     1,     1,     2
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
#line 1709 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 3:
#line 63 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { (yyval.ptr) = (yyvsp[0].ptr); ast_setAst(parser, (yyvsp[0].ptr)); }
#line 1715 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 4:
#line 65 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { (yyval.ptr) = (yyvsp[0].ptr); ast_setAst(parser, (yyvsp[0].ptr)); }
#line 1721 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
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
#line 1736 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
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
#line 1750 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
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
#line 1764 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
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
#line 1779 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
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
#line 1794 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 10:
#line 132 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newCheckUnsatCommand();

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1809 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 11:
#line 144 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newCheckSatAssumCommand((yyvsp[-2].list)); 

			(yyloc).first_line = (yylsp[-5]).first_line;
            (yyloc).first_column = (yylsp[-5]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1824 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 12:
#line 156 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newDeclareConstCommand((yyvsp[-2].ptr), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1839 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 13:
#line 168 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newDeclareDatatypeCommand((yyvsp[-2].ptr), (yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-4]).first_line;
			(yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1854 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 14:
#line 180 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newDeclareDatatypesCommand((yyvsp[-5].list), (yyvsp[-2].list));

			(yyloc).first_line = (yylsp[-8]).first_line;
			(yyloc).first_column = (yylsp[-8]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1869 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 15:
#line 192 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newDeclareFunCommand((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-7]).first_line;
            (yyloc).first_column = (yylsp[-7]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1884 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 16:
#line 204 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newDeclareSortCommand((yyvsp[-2].ptr), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1899 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 17:
#line 216 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newDeclareHeapCommand((yyvsp[-1].pairList));

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1914 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 18:
#line 228 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newDefineFunsRecCommand((yyvsp[-5].list), (yyvsp[-2].list)); 

			(yyloc).first_line = (yylsp[-8]).first_line;
            (yyloc).first_column = (yylsp[-8]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1929 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 19:
#line 240 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newDefineFunRecCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1944 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 20:
#line 252 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newDefineFunCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1959 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 21:
#line 264 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newDefineSortCommand((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-7]).first_line;
            (yyloc).first_column = (yylsp[-7]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1974 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 22:
#line 276 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newEchoCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1989 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 23:
#line 288 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newExitCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2004 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 24:
#line 300 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newGetAssertsCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2019 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 25:
#line 312 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newGetAssignsCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2034 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 26:
#line 324 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newGetInfoCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2049 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 27:
#line 336 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newGetModelCommand(); 
			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[-2]).last_line;
            (yyloc).last_column = (yylsp[-2]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2063 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 28:
#line 347 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newGetOptionCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2078 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 29:
#line 359 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newGetProofCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2093 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 30:
#line 371 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newGetModelCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2108 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 31:
#line 383 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newGetUnsatCoreCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2123 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 32:
#line 395 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newGetValueCommand((yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2138 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 33:
#line 407 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newPopCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2153 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 34:
#line 419 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newPushCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2168 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 35:
#line 431 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newResetAssertsCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2183 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 36:
#line 443 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newResetCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2198 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 37:
#line 455 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newSetInfoCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2213 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 38:
#line 467 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newSetLogicCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
            (yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2228 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 39:
#line 479 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newSetOptionCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2243 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 40:
#line 493 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.list) = ast_listCreate();
			ast_listAdd((yyval.list), (yyvsp[0].ptr));

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2257 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 41:
#line 504 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr));
			(yyval.list) = (yyvsp[-1].list);

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2271 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 42:
#line 517 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newSimpleDatatypeDeclaration((yyvsp[-1].list));

			(yyloc).first_line = (yylsp[-2]).first_line;
			(yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2286 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 43:
#line 529 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newParametricDatatypeDeclaration((yyvsp[-5].list), (yyvsp[-2].list));

			(yyloc).first_line = (yylsp[-8]).first_line;
			(yyloc).first_column = (yylsp[-8]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2301 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 44:
#line 543 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.list) = ast_listCreate();
			ast_listAdd((yyval.list), (yyvsp[0].ptr));

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2315 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 45:
#line 554 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr));
			(yyval.list) = (yyvsp[-1].list);

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2329 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 46:
#line 567 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newConstructorDeclaration((yyvsp[-2].ptr), (yyvsp[-1].list));

			(yyloc).first_line = (yylsp[-3]).first_line;
			(yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2344 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 47:
#line 581 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.list) = ast_listCreate();
		}
#line 2352 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 48:
#line 586 "smtlib-bison-parser.y" /* yacc.c:1661  */
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
#line 2373 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 49:
#line 606 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newSelectorDeclaration((yyvsp[-2].ptr), (yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-3]).first_line;
			(yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2388 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 50:
#line 620 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.list) = ast_listCreate();
			ast_listAdd((yyval.list), (yyvsp[0].ptr));

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2402 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 51:
#line 631 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr));
			(yyval.list) = (yyvsp[-1].list);

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2416 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 52:
#line 644 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newSortDeclaration((yyvsp[-2].ptr), (yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2431 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 53:
#line 658 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2444 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 54:
#line 668 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2457 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 55:
#line 678 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newQualifiedTerm((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2472 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 56:
#line 690 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newLetTerm((yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-6]).first_line;
            (yyloc).first_column = (yylsp[-6]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2487 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 57:
#line 702 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newForallTerm((yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-6]).first_line;
            (yyloc).first_column = (yylsp[-6]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2502 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 58:
#line 714 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newExistsTerm((yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-6]).first_line;
            (yyloc).first_column = (yylsp[-6]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2517 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 59:
#line 726 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newMatchTerm((yyvsp[-4].ptr), (yyvsp[-2].list));

			(yyloc).first_line = (yylsp[-6]).first_line;
            (yyloc).first_column = (yylsp[-6]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2532 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 60:
#line 738 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newAnnotatedTerm((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[-1]).last_line;
            (yyloc).last_column = (yylsp[-1]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2547 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 61:
#line 750 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[-1].ptr); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2562 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 62:
#line 764 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2576 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 63:
#line 775 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2590 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 64:
#line 788 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.list) = ast_listCreate();
			ast_listAdd((yyval.list), (yyvsp[0].ptr));

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2604 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 65:
#line 799 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr));
			(yyval.list) = (yyvsp[-1].list);

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2618 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 66:
#line 812 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newMatchCase((yyvsp[-2].ptr), (yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-3]).first_line;
			(yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2633 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 67:
#line 826 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = (yyvsp[0].ptr);

			(yyloc).first_line = (yylsp[0]).first_line;
			(yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2646 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 68:
#line 836 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newQualifiedPattern((yyvsp[-2].ptr), (yyvsp[-1].list));

			(yyloc).first_line = (yylsp[-3]).first_line;
			(yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2661 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 69:
#line 850 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = (yyvsp[0].ptr);

			(yyloc).first_line = (yylsp[0]).first_line;
			(yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2674 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 70:
#line 860 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newQualifiedConstructor((yyvsp[-2].ptr), (yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-4]).first_line;
			(yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[-1]).last_line;
			(yyloc).last_column = (yylsp[-1]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2689 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
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
#line 2704 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
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
#line 2719 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
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
#line 2734 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
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
#line 2749 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 75:
#line 922 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2764 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 76:
#line 936 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = (yyvsp[0].ptr);

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2779 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 77:
#line 948 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newSymbol("reset");

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2794 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 78:
#line 960 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newSymbol("not");

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2809 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 79:
#line 972 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.ptr) = ast_newSymbol("_");

			(yyloc).first_line = (yylsp[0]).first_line;
			(yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2824 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 80:
#line 986 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2837 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 81:
#line 996 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newQualifiedIdentifier((yyvsp[-2].ptr), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2852 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 82:
#line 1010 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newSimpleIdentifier1((yyvsp[0].ptr));

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2867 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 83:
#line 1022 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newSimpleIdentifier2((yyvsp[-2].ptr), (yyvsp[-1].list));

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2882 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
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
#line 2897 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 85:
#line 1048 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2912 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 86:
#line 1062 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2926 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 87:
#line 1073 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2940 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 88:
#line 1086 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newSort1((yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2955 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 89:
#line 1098 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newSort2((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2970 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 90:
#line 1112 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2984 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 91:
#line 1123 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2998 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 92:
#line 1136 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate();
		}
#line 3006 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 93:
#line 1141 "smtlib-bison-parser.y" /* yacc.c:1661  */
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
#line 3027 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 94:
#line 1161 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			(yyval.pairList) = ast_pairListCreate();
			ast_pairListAdd((yyval.pairList), (yyvsp[-2].ptr), (yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[-1]).last_line;
            (yyloc).last_column = (yylsp[-1]).last_column;
		}
#line 3041 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 95:
#line 1172 "smtlib-bison-parser.y" /* yacc.c:1661  */
    {
			ast_pairListAdd((yyvsp[-4].pairList), (yyvsp[-2].ptr), (yyvsp[-1].ptr));
			(yyval.pairList) = (yyvsp[-4].pairList);

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3055 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 96:
#line 1185 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newVariableBinding((yyvsp[-2].ptr), (yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[-1]).last_line;
            (yyloc).last_column = (yylsp[-1]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3070 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 97:
#line 1199 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3084 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 98:
#line 1210 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3098 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 99:
#line 1223 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newSortedVariable((yyvsp[-2].ptr), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[-1]).last_line;
            (yyloc).last_column = (yylsp[-1]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3113 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 100:
#line 1237 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3127 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 101:
#line 1248 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3141 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 102:
#line 1261 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { (yyval.list) = ast_listCreate(); }
#line 3147 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 103:
#line 1264 "smtlib-bison-parser.y" /* yacc.c:1661  */
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
#line 3168 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 104:
#line 1284 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newAttribute1((yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3183 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 105:
#line 1296 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newAttribute2((yyvsp[-1].ptr), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3198 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 106:
#line 1310 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { (yyval.list) = ast_listCreate(); }
#line 3204 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 107:
#line 1313 "smtlib-bison-parser.y" /* yacc.c:1661  */
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
#line 3225 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 108:
#line 1333 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3239 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 109:
#line 1344 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
        	(yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
        	(yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3253 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 110:
#line 1357 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3266 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 111:
#line 1367 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3279 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 112:
#line 1377 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newCompSExpression((yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3294 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 113:
#line 1391 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3307 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 114:
#line 1401 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3320 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 115:
#line 1411 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3333 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 116:
#line 1421 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newCompSExpression((yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3348 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 117:
#line 1435 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3362 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 118:
#line 1446 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3376 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 119:
#line 1459 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newPropLiteral((yyvsp[0].ptr), 0); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3391 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 120:
#line 1471 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newPropLiteral((yyvsp[-1].ptr), 1); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3406 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 121:
#line 1485 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { (yyval.list) = ast_listCreate(); }
#line 3412 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 122:
#line 1489 "smtlib-bison-parser.y" /* yacc.c:1661  */
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
#line 3433 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 123:
#line 1509 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newFunctionDeclaration((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-6]).first_line;
            (yyloc).first_column = (yylsp[-6]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3448 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 124:
#line 1523 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3462 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 125:
#line 1534 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3476 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 126:
#line 1547 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newFunctionDefinition(
				ast_newFunctionDeclaration((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[-5]).first_line;
            (yyloc).first_column = (yylsp[-5]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3492 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 127:
#line 1562 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { (yyval.list) = ast_listCreate(); }
#line 3498 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 128:
#line 1565 "smtlib-bison-parser.y" /* yacc.c:1661  */
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
#line 3519 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 129:
#line 1585 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3533 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 130:
#line 1596 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3547 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 131:
#line 1609 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3562 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 132:
#line 1623 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3575 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 133:
#line 1635 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newTheory((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3590 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 134:
#line 1649 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newAttribute2((yyvsp[-3].ptr), 
				ast_newCompAttributeValue((yyvsp[-1].list)));

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3606 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 135:
#line 1662 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newAttribute2((yyvsp[-3].ptr), 
				ast_newCompAttributeValue((yyvsp[-1].list)));

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3622 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 136:
#line 1675 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3635 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 137:
#line 1687 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3649 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 138:
#line 1698 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3663 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 139:
#line 1711 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newSortSymbolDeclaration((yyvsp[-3].ptr), (yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3678 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 140:
#line 1725 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3692 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 141:
#line 1736 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3706 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 143:
#line 1751 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newParametricFunDeclaration((yyvsp[-7].list), (yyvsp[-4].ptr), (yyvsp[-3].list), (yyvsp[-2].list));

			(yyloc).first_line = (yylsp[-10]).first_line;
            (yyloc).first_column = (yylsp[-10]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3721 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 144:
#line 1765 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3735 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 145:
#line 1776 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list);

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column; 
		}
#line 3749 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 146:
#line 1789 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newSpecConstFunDeclaration((yyvsp[-3].ptr), (yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3764 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 147:
#line 1801 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newMetaSpecConstFunDeclaration((yyvsp[-3].ptr), (yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3779 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 148:
#line 1813 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newSimpleFunDeclaration((yyvsp[-3].ptr), (yyvsp[-2].list), (yyvsp[-1].list));

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3794 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
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
#line 3809 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
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
#line 3824 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 151:
#line 1851 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3839 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 152:
#line 1865 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newLogic((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3854 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 153:
#line 1879 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = ast_newAttribute2((yyvsp[-3].ptr), ast_newCompAttributeValue((yyvsp[-1].list)));

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            ast_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3869 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 154:
#line 1891 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3882 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 155:
#line 1903 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			(yyval.list) = ast_listCreate(); 
			ast_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3896 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;

  case 156:
#line 1914 "smtlib-bison-parser.y" /* yacc.c:1661  */
    { 
			ast_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3910 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
    break;


#line 3914 "smtlib-bison-parser.tab.c" /* yacc.c:1661  */
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
#line 1925 "smtlib-bison-parser.y" /* yacc.c:1906  */


void yyerror(SmtPrsr parser, const char* s) {
	ast_reportError(parser, yylloc.first_line, yylloc.first_column,
					yylloc.last_line, yylloc.last_column, s);
}
