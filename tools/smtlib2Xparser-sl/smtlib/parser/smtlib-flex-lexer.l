%{ 
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include "smtlib-glue.h" 
#include "smtlib-bison-parser.y.h"

int smt_yycolumn = 1;
#define UPDATE_COLUMN(n) smt_yycolumn += n;

#define RESET_COLUMN smt_yycolumn = 1;

#define SET_LOCATION smt_yylloc.first_line = smt_yylloc.last_line = smt_yylineno; \
smt_yylloc.first_column = smt_yycolumn; smt_yylloc.last_column = smt_yycolumn + yyleng - 1; \
UPDATE_COLUMN(yyleng);

#define SET_LEFT smt_yylloc.first_line = smt_yylineno; \
smt_yylloc.first_column = smt_yycolumn; \
UPDATE_COLUMN(yyleng);

#define SET_RIGHT smt_yylloc.last_line = smt_yylineno; \
smt_yylloc.last_column = smt_yycolumn + yyleng - 1; \
UPDATE_COLUMN(yyleng);
%}

whitespace     	[\x09 \xA0]
printable_char 	[\x20-\x7E\xA0-xFF]
digit          	[0-9]
letter         	[a-zA-Z]
numeral        	0|[1-9][0-9]*
decimal        	{numeral}\.0*{numeral}
hexadecimal    	"#x"[0-9A-Fa-f]+
binary         	"#b"[01]+
special_char	[+\-/*=%?!.$_~&^<>@]

comment			";".*[\n\r]+

sym_begin      {letter}|{special_char}
sym_continue   {sym_begin}|{digit}
simple_symbol  {sym_begin}{sym_continue}*

%x string
%x quoted

%option noyywrap
%option yylineno
%option prefix="smt_yy"

%%

"_"                	{ SET_LOCATION; return '_'; }
"!"                	{ SET_LOCATION; return '!'; }
"as"               	{ SET_LOCATION; return KW_AS; }
"let"              	{ SET_LOCATION; return KW_LET; }
"exists"           	{ SET_LOCATION; return KW_EXISTS; }
"forall"           	{ SET_LOCATION; return KW_FORALL; }
"match"           	{ SET_LOCATION; return KW_MATCH; }
"par"              	{ SET_LOCATION; return KW_PAR; }

"("				   	{ SET_LOCATION; return '('; }
")"				   	{ SET_LOCATION; return ')'; }

{numeral}		   	{ 
						SET_LOCATION;
						smt_yylval.ptr = ast_newNumeralLiteral(
							strtol(yytext, NULL, 10), 10); 
						return NUMERAL; 
					}

{decimal}		   	{
						SET_LOCATION;
						smt_yylval.ptr = ast_newDecimalLiteral(
							strtod(yytext, NULL));  
						return DECIMAL; 
					}
{hexadecimal}	   	{ 
						SET_LOCATION;
						smt_yylval.ptr = ast_newNumeralLiteral(
							strtol(yytext+2, NULL, 16), 16); 
						return HEXADECIMAL; 
					}
{binary}		   	{
						SET_LOCATION;
						smt_yylval.ptr = ast_newNumeralLiteral(
							strtol(yytext+2, NULL, 2), 2); 
						return BINARY; 
					}
"not"					{ SET_LOCATION; return NOT; }

"assert"		   		{ SET_LOCATION; return KW_ASSERT; }
"check-sat-assuming"	{ SET_LOCATION; return KW_CHK_SAT_ASSUM; }
"check-sat"		   		{ SET_LOCATION; return KW_CHK_SAT; }
"check-unsat"		   		{ SET_LOCATION; return KW_CHK_UNSAT; }
"declare-const"		   	{ SET_LOCATION; return KW_DECL_CONST; }
"declare-datatype"		{ SET_LOCATION; return KW_DECL_DATATYPE; }
"declare-datatypes"		{ SET_LOCATION; return KW_DECL_DATATYPES; }
"declare-fun"			{ SET_LOCATION; return KW_DECL_FUN; }
"declare-sort"	   		{ SET_LOCATION; return KW_DECL_SORT; }
"declare-heap"	   		{ SET_LOCATION; return KW_DECL_HEAP; }
"define-funs-rec"		{ SET_LOCATION; return KW_DEF_FUNS_REC; }
"define-fun-rec"		{ SET_LOCATION; return KW_DEF_FUN_REC; }
"define-fun"			{ SET_LOCATION; return KW_DEF_FUN; }
"define-sort"			{ SET_LOCATION; return KW_DEF_SORT; }
"echo"					{ SET_LOCATION; return KW_ECHO; }
"exit"					{ SET_LOCATION; return KW_EXIT; }
"get-assertions"		{ SET_LOCATION; return KW_GET_ASSERTS; }
"get-assignment"		{ SET_LOCATION; return KW_GET_ASSIGNS; }
"get-info"				{ SET_LOCATION; return KW_GET_INFO; }
"get-model"				{ SET_LOCATION; return KW_GET_MODEL; }
"get-option"			{ SET_LOCATION; return KW_GET_OPT; }
"get-proof"				{ SET_LOCATION; return KW_GET_PROOF; }
"get-unsat-assumptions"	{ SET_LOCATION; return KW_GET_UNSAT_ASSUMS; }
"get-unsat-core"		{ SET_LOCATION; return KW_GET_UNSAT_CORE; }
"get-value"				{ SET_LOCATION; return KW_GET_VALUE; }
"pop"					{ SET_LOCATION; return KW_POP; }
"push"					{ SET_LOCATION; return KW_PUSH; }
"reset-assertions"		{ SET_LOCATION; return KW_RESET_ASSERTS; }
"reset"					{ SET_LOCATION; return KW_RESET; }
"set-info"				{ SET_LOCATION; return KW_SET_INFO; }
"set-logic"				{ SET_LOCATION; return KW_SET_LOGIC; }
"set-option"			{ SET_LOCATION; return KW_SET_OPT; }

"DECIMAL"	{ 
				SET_LOCATION;
				smt_yylval.ptr = ast_newMetaSpecConstant(1);
				return META_SPEC_DECIMAL; 
			}
"NUMERAL"	{ 
				SET_LOCATION;
				smt_yylval.ptr = ast_newMetaSpecConstant(0);
				return META_SPEC_NUMERAL; 
			}
"STRING"	{ 
				SET_LOCATION;
				smt_yylval.ptr = ast_newMetaSpecConstant(2);
				return META_SPEC_STRING; 
			}

"theory" 	{ 
				SET_LOCATION;
				smt_yylval.ptr = ast_newSymbol(yytext); 
				return THEORY; 
			}
"logic" 	{ 
				SET_LOCATION;
				smt_yylval.ptr = ast_newSymbol(yytext); 
				return LOGIC; 
			}

":sorts"				{ 
							SET_LOCATION;
							smt_yylval.ptr = ast_newKeyword(yytext);
							return KW_ATTR_SORTS; 
						}
":funs"					{ 
							SET_LOCATION;
							smt_yylval.ptr = ast_newKeyword(yytext);
							return KW_ATTR_FUNS; 
						}
":theories" 			{
							SET_LOCATION;
							smt_yylval.ptr = ast_newKeyword(yytext); 
							return KW_ATTR_THEORIES; 
						}

{simple_symbol}		{
						SET_LOCATION;
						smt_yylval.ptr = ast_newSymbol(yytext); 
						return SYMBOL; 
					}
":"{simple_symbol}	{ 
						SET_LOCATION;
						smt_yylval.ptr = ast_newKeyword(yytext); 
						return KEYWORD; 
					}

\"					{ SET_LEFT; BEGIN string; yymore(); }
<string>\"\"   		{ UPDATE_COLUMN(2);; yymore(); }
<string>[\n\r]+		{ RESET_COLUMN; yymore(); }
<string>\"			{ 	
						SET_RIGHT;
						BEGIN 0; 
						smt_yylval.ptr = ast_newStringLiteral(yytext);
						return STRING; 
					}
<string>.			{ UPDATE_COLUMN(1); yymore(); }

\|					{ SET_LEFT; BEGIN quoted; yymore(); }
<quoted>[\n\r]+		{ RESET_COLUMN; yymore(); }
<quoted>\|			{ 
						SET_RIGHT;
						BEGIN 0; 
						smt_yylval.ptr = ast_newSymbol(yytext);
						return SYMBOL; 
					}
<quoted>\\			{ }
<quoted>.			{ UPDATE_COLUMN(1); yymore(); }

[\n\r]+				{ SET_LOCATION; smt_yycolumn = 1; }
{whitespace}		{ SET_LOCATION; /*ignore*/ }
{comment}			{ SET_LOCATION; smt_yycolumn = 1; /*ignore*/ }
