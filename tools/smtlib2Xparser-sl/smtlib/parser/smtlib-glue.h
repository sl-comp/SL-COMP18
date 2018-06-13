#ifndef SLCOMP_PARSER_SMTLIB_GLUE_H
#define SLCOMP_PARSER_SMTLIB_GLUE_H

#ifdef __cplusplus

#include "smtlib/ast/ast_abstract.h"

namespace smtlib {
    namespace ast {
        class Node;
    }
    class Parser;
}
class ParserInternalList;
class ParserInternalPairList;

typedef class smtlib::ast::Node* AstPtr;
typedef class ParserInternalList* AstList;
typedef class ParserInternalPairList* AstPairList;
typedef class smtlib::Parser* SmtPrsr;
#else
typedef void *AstPtr, *AstList, *AstPairList, *SmtPrsr;
#endif

#ifdef __cplusplus
extern "C" {
#endif

int smt_yylex(void);
int smt_yyparse(SmtPrsr);

void ast_print(AstPtr ptr);

void ast_setAst(SmtPrsr parser, AstPtr ast);
void ast_reportError(SmtPrsr parser,
                     int rowLeft, int colLeft,
                     int rowRight, int colRight,
                     const char* msg);

AstList ast_listCreate();
void ast_listAdd(AstList list, AstPtr item);
void ast_listDelete(AstList list);

AstPairList ast_pairListCreate();
void ast_pairListAdd(AstPairList list, AstPtr item1, AstPtr item2);
void ast_pairListDelete(AstPairList list);

void ast_setLocation(SmtPrsr parser, AstPtr ptr,
                     int rowLeft, int colLeft,
                     int rowRight, int colRight);

int ast_bool_value(AstPtr ptr);

// ast_attribute.h
AstPtr ast_newAttribute1(AstPtr keyword);
AstPtr ast_newAttribute2(AstPtr keyword, AstPtr attr_value);
AstPtr ast_newCompAttributeValue(AstList values);

// ast_basic.h
AstPtr ast_newSymbol(char const* value);
AstPtr ast_newKeyword(char const* value);
AstPtr ast_newMetaSpecConstant(int value);
AstPtr ast_newBooleanValue(int value);
AstPtr ast_newPropLiteral(AstPtr symbol, int negated);

// ast_command.h
AstPtr ast_newAssertCommand(AstPtr term);
AstPtr ast_newCheckSatCommand();
AstPtr ast_newCheckSatAssumCommand(AstList assumptions);
AstPtr ast_newDeclareConstCommand(AstPtr symbol, AstPtr sort);
AstPtr ast_newDeclareDatatypeCommand(AstPtr symbol, AstPtr declaration);
AstPtr ast_newDeclareDatatypesCommand(AstList sorts, AstList declarations);
AstPtr ast_newDeclareFunCommand(AstPtr symbol, AstList params, AstPtr sort);
AstPtr ast_newDeclareSortCommand(AstPtr symbol, AstPtr arity);
AstPtr ast_newDeclareHeapCommand(AstPairList pairs);
AstPtr ast_newDefineFunCommand(AstPtr definition);
AstPtr ast_newDefineFunRecCommand(AstPtr definition);
AstPtr ast_newDefineFunsRecCommand(AstList declarations, AstList bodies);
AstPtr ast_newDefineSortCommand(AstPtr symbol, AstList params, AstPtr sort);
AstPtr ast_newEchoCommand(AstPtr);
AstPtr ast_newExitCommand();
AstPtr ast_newGetAssertsCommand();
AstPtr ast_newGetAssignsCommand();
AstPtr ast_newGetInfoCommand(AstPtr keyword);
AstPtr ast_newGetModelCommand();
AstPtr ast_newGetOptionCommand(AstPtr keyword);
AstPtr ast_newGetProofCommand();
AstPtr ast_newGetUnsatAssumsCommand();
AstPtr ast_newGetUnsatCoreCommand();
AstPtr ast_newGetValueCommand(AstList terms);
AstPtr ast_newPopCommand(AstPtr numeral);
AstPtr ast_newPushCommand(AstPtr numeral);
AstPtr ast_newResetCommand();
AstPtr ast_newResetAssertsCommand();
AstPtr ast_newSetInfoCommand(AstPtr info);
AstPtr ast_newSetLogicCommand(AstPtr logic);
AstPtr ast_newSetOptionCommand(AstPtr option);

//ast_datatype.h
AstPtr ast_newSortDeclaration(AstPtr symbol, AstPtr numeral);
AstPtr ast_newSelectorDeclaration(AstPtr symbol, AstPtr sort);
AstPtr ast_newConstructorDeclaration(AstPtr symbol, AstList selectors);
AstPtr ast_newSimpleDatatypeDeclaration(AstList constructors);
AstPtr ast_newParametricDatatypeDeclaration(AstList params, AstList constructors);

// ast_fun.h
AstPtr ast_newFunctionDeclaration(AstPtr symbol, AstList params, AstPtr sort);
AstPtr ast_newFunctionDefinition(AstPtr signature, AstPtr body);

// ast_identifier.h
AstPtr ast_newSimpleIdentifier1(AstPtr symbol);
AstPtr ast_newSimpleIdentifier2(AstPtr symbol, AstList indices);
AstPtr ast_newQualifiedIdentifier(AstPtr identifier, AstPtr sort);

// ast_literal.h
AstPtr ast_newNumeralLiteral(long value, unsigned int base);
AstPtr ast_newDecimalLiteral(double value);
AstPtr ast_newStringLiteral(char const* value);

// ast_logic.h
AstPtr ast_newLogic(AstPtr name, AstList attributes);

// ast_match.h
AstPtr ast_newQualifiedConstructor(AstPtr symbol, AstPtr sort);
AstPtr ast_newQualifiedPattern(AstPtr constructor, AstList symbols);
AstPtr ast_newMatchCase(AstPtr pattern, AstPtr term);

// ast_s_expr.h
AstPtr ast_newCompSExpression(AstList exprs);

// ast_script.h
AstPtr ast_newScript(AstList cmds);

// ast_sort.h
AstPtr ast_newSort1(AstPtr identifier);
AstPtr ast_newSort2(AstPtr identifier, AstList params);

// ast_symbol_decl.h
AstPtr ast_newSortSymbolDeclaration(AstPtr identifier, AstPtr arity, AstList attributes);
AstPtr ast_newSpecConstFunDeclaration(AstPtr constant, AstPtr sort, AstList attributes);
AstPtr ast_newMetaSpecConstFunDeclaration(AstPtr constant, AstPtr sort, AstList attributes);
AstPtr ast_newSimpleFunDeclaration(AstPtr identifier, AstList signature, AstList attributes);
AstPtr ast_newParametricFunDeclaration(AstList params, AstPtr identifier, AstList signature, AstList attributes);

// ast_term.h
AstPtr ast_newQualifiedTerm(AstPtr identifier, AstList terms);
AstPtr ast_newLetTerm(AstList bindings, AstPtr term);
AstPtr ast_newForallTerm(AstList bindings, AstPtr term);
AstPtr ast_newExistsTerm(AstList bindings, AstPtr term);
AstPtr ast_newMatchTerm(AstPtr term, AstList cases);
AstPtr ast_newAnnotatedTerm(AstPtr term, AstList attrs);

// ast_theory.h
AstPtr ast_newTheory(AstPtr name, AstList attributes);

// ast_variable.h
AstPtr ast_newSortedVariable(AstPtr symbol, AstPtr sort);
AstPtr ast_newVariableBinding(AstPtr symbol, AstPtr term);

#ifdef __cplusplus
}; // extern "C"
#endif

#endif //SLCOMP_PARSER_SMTLIB_GLUE_H
