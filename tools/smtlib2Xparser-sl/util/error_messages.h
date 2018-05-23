/**
 * \file error_messages.h
 * \brief Constants and builders for error messages.
 */

#ifndef SLCOMP_PARSER_ERROR_MESSAGES_H
#define SLCOMP_PARSER_ERROR_MESSAGES_H

#include "ast/ast_classes.h"
#include "sep/sep_classes.h"

#include <sstream>
#include <string>
#include <vector>

class ErrorMessages {
private:
    static std::string extractFirstN(const std::string& str, unsigned long n);

    template<class T>
    static void printArray(std::stringstream& ss,
                           const std::vector<std::shared_ptr<T>>& array,
                           const std::string& separator) {
        std::vector<std::string> strArray;
        for (const auto& node : array) {
            strArray.push_back(node->toString());
        }

        printStringArray(ss, strArray, separator);
    }

    static void printStringArray(std::stringstream& ss,
                                 const std::vector<std::string>& array,
                                 const std::string& separator);

public:
    static const std::string ERR_INVALID_IND_CASE;
    static const std::string ERR_NULL_NODE_VISIT;
    static const std::string ERR_ATTR_MISSING_KEYWORD;
    static const std::string ERR_SYMBOL_MALFORMED;
    static const std::string ERR_KEYWORD_MALFORMED;
    static const std::string ERR_PROP_LIT_MISSING_SYMBOL;
    static const std::string ERR_ASSERT_MISSING_TERM;
    static const std::string ERR_DECL_CONST_MISSING_NAME;
    static const std::string ERR_DECL_CONST_MISSING_SORT;
    static const std::string ERR_DECL_DATATYPE_MISSING_NAME;
    static const std::string ERR_DECL_DATATYPE_MISSING_DECL;
    static const std::string ERR_DECL_DATATYPES_MISSING_SORTS;
    static const std::string ERR_DECL_DATATYPES_MISSING_DECLS;
    static const std::string ERR_DECL_FUN_MISSING_NAME;
    static const std::string ERR_DECL_FUN_MISSING_RET;
    static const std::string ERR_DECL_SORT_MISSING_NAME;
    static const std::string ERR_DECL_SORT_MISSING_ARITY;
    static const std::string ERR_DECL_HEAP_MISSING_LOC;
    static const std::string ERR_DECL_HEAP_MISSING_DATA;
    static const std::string ERR_DEF_FUN_MISSING_DEF;
    static const std::string ERR_DEF_FUN_REC_MISSING_DEF;
    static const std::string ERR_DEF_FUNS_REC_EMPTY_DECLS;
    static const std::string ERR_DEF_FUNS_REC_EMPTY_BODIES;
    static const std::string ERR_DEF_SORT_MISSING_NAME;
    static const std::string ERR_DEF_SORT_MISSING_DEF;
    static const std::string ERR_ECHO_EMPTY_STRING;
    static const std::string ERR_GET_INFO_MISSING_FLAG;
    static const std::string ERR_GET_OPT_MISSING_OPT;
    static const std::string ERR_GET_VALUE_EMPTY_TERMS;
    static const std::string ERR_POP_MISSING_NUMERAL;
    static const std::string ERR_PUSH_MISSING_NUMERAL;
    static const std::string ERR_SET_INFO_MISSING_INFO;
    static const std::string ERR_SET_LOGIC_MISSING_LOGIC;
    static const std::string ERR_SET_OPT_MISSING_OPT;
    static const std::string ERR_OPT_VALUE_STRING;
    static const std::string ERR_OPT_VALUE_NUMERAL;
    static const std::string ERR_OPT_VALUE_BOOLEAN;
    static const std::string ERR_FUN_DECL_MISSING_NAME;
    static const std::string ERR_FUN_DECL_MISSING_RET;
    static const std::string ERR_FUN_DEF_MISSING_SIG;
    static const std::string ERR_FUN_DEF_MISSING_BODY;
    static const std::string ERR_ID_MISSING_SYMBOL;
    static const std::string ERR_ID_EMPTY_INDICES;
    static const std::string ERR_QUAL_ID_MISSING_ID;
    static const std::string ERR_QUAL_ID_MISSING_SORT;
    static const std::string ERR_LOGIC_MISSING_NAME;
    static const std::string ERR_LOGIC_EMPTY_ATTRS;
    static const std::string ERR_THEORY_MISSING_NAME;
    static const std::string ERR_THEORY_EMPTY_ATTRS;
    static const std::string ERR_ATTR_VALUE_STRING;
    static const std::string ERR_ATTR_VALUE_SORTS;
    static const std::string ERR_ATTR_VALUE_SORTS_EMPTY;
    static const std::string ERR_ATTR_VALUE_FUNS;
    static const std::string ERR_ATTR_VALUE_FUNS_EMPTY;
    static const std::string ERR_ATTR_VALUE_THEORIES;
    static const std::string ERR_ATTR_VALUE_THEORIES_EMPTY;
    static const std::string ERR_SORT_MISSING_ID;
    static const std::string ERR_SORT_EMPTY_ARGS;
    static const std::string ERR_SORT_SYM_DECL_MISSING_ID;
    static const std::string ERR_SORT_SYM_DECL_MISSING_ARITY;
    static const std::string ERR_SPEC_CONST_DECL_MISSING_CONST;
    static const std::string ERR_SPEC_CONST_DECL_MISSING_SORT;
    static const std::string ERR_META_SPEC_CONST_DECL_MISSING_CONST;
    static const std::string ERR_META_SPEC_CONST_DECL_MISSING_SORT;
    static const std::string ERR_FUN_SYM_DECL_MISSING_ID;
    static const std::string ERR_FUN_SYM_DECL_EMPTY_SIG;
    static const std::string ERR_PARAM_FUN_SYM_DECL_EMPTY_PARAMS;
    static const std::string ERR_PARAM_FUN_SYM_DECL_MISSING_ID;
    static const std::string ERR_PARAM_FUN_SYM_DECL_EMPTY_SIG;
    static const std::string ERR_SORT_DECL_MISSING_SYMBOL;
    static const std::string ERR_SORT_DECL_MISSING_ARITY;
    static const std::string ERR_SEL_DECL_MISSING_SYMBOL;
    static const std::string ERR_SEL_DECL_MISSING_SORT;
    static const std::string ERR_CONS_DECL_MISSING_SYMBOL;
    static const std::string ERR_DATATYPE_DECL_EMPTY_CONS;
    static const std::string ERR_PARAM_DATATYPE_DECL_EMPTY_PARAMS;
    static const std::string ERR_PARAM_DATATYPE_DECL_EMPTY_CONS;
    static const std::string ERR_QUAL_CONS_MISSING_SYMBOL;
    static const std::string ERR_QUAL_CONS_MISSING_SORT;
    static const std::string ERR_QUAL_PATTERN_MISSING_CONS;
    static const std::string ERR_QUAL_PATTERN_EMPTY_SYMS;
    static const std::string ERR_MATCH_CASE_MISSING_PATTERN;
    static const std::string ERR_MATCH_CASE_MISSING_TERM;
    static const std::string ERR_QUAL_TERM_MISSING_ID;
    static const std::string ERR_QUAL_TERM_EMPTY_TERMS;
    static const std::string ERR_LET_TERM_MISSING_TERM;
    static const std::string ERR_LET_TERM_EMPTY_VARS;
    static const std::string ERR_FORALL_TERM_MISSING_TERM;
    static const std::string ERR_FORALL_TERM_EMPTY_VARS;
    static const std::string ERR_EXISTS_TERM_MISSING_TERM;
    static const std::string ERR_EXISTS_TERM_EMPTY_VARS;
    static const std::string ERR_MATCH_TERM_MISSING_TERM;
    static const std::string ERR_MATCH_TERM_EMPTY_CASES;
    static const std::string ERR_ANNOT_TERM_MISSING_TERM;
    static const std::string ERR_ANNOT_TERM_EMPTY_ATTRS;
    static const std::string ERR_SORTED_VAR_MISSING_SYMBOL;
    static const std::string ERR_SORTED_VAR_MISSING_SORT;
    static const std::string ERR_VAR_BIND_MISSING_SYMBOL;
    static const std::string ERR_VAR_BIND_MISSING_SORT;
    static const std::string ERR_UFLD_LVL_NEGATIVE;
    static const std::string ERR_UFLD_LVL_INVALID;
    static const std::string ERR_OUT_PATH_INVALID;
    static const std::string ERR_UNSPECIFIED_LOC_SORT;
    static const std::string ERR_UNSPECIFIED_DATA_SORT;
    static const std::string ERR_UNSPECIFIED_NIL_SORT;
    static const std::string ERR_PTO_LEFT_NIL;

    static std::string buildTheoryUnloadable(const std::string& theory);

    static std::string buildTheoryUnknown(const std::string& theory);

    static std::string buildTheoryAlreadyLoaded(const std::string& theory);

    static std::string buildLogicUnloadable(const std::string& logic);

    static std::string buildLogicUnknown(const std::string& logic);

    static std::string buildLogicAlreadySet(const std::string& logic);


    static std::string buildSortUnknown(const std::string& name,
                                        int rowLeft, int colLeft,
                                        int rowRight, int colRight);

    static std::string buildSortArity(const std::string& name,
                                      unsigned long arity, size_t argCount,
                                      int rowLeft, int colLeft,
                                      int rowRight, int colRight);

    static std::string buildSortParamArity(const std::string& sort,
                                           const std::string& sortName);

    static std::string buildAssertTermNotWellSorted(const std::string& term,
                                                    int rowLeft, int colLeft,
                                                    int rowRight, int colRight);

    static std::string buildAssertTermNotBool(const std::string& term,
                                              const std::string& termSort,
                                              int rowLeft, int colLeft,
                                              int rowRight, int colRight);

    static std::string buildConstAlreadyExists(const std::string& name);

    static std::string buildConstUnknown(const std::string& name);

    static std::string buildConstNoSorts(const std::string& name);

    static std::string buildConstMultipleSorts(const std::string& name,
                                               const std::vector<smtlib::ast::SortPtr>& possibleSorts);

    static std::string buildConstWrongSort(const std::string& name,
                                           const std::string& wrongSort,
                                           const std::vector<smtlib::ast::SortPtr>& possibleSorts);

    static std::string buildFunAlreadyExists(const std::string& name);

    static std::string buildFunBodyWrongSort(const std::string& body,
                                             const std::string& wrongSort,
                                             const std::string& rightSort,
                                             int rowLeft, int colLeft,
                                             int rowRight, int colRight);

    static std::string buildFunBodyWrongSort(const std::string& name,
                                             const std::string& body,
                                             const std::string& wrongSort,
                                             const std::string& rightSort,
                                             int rowLeft, int colLeft,
                                             int rowRight, int colRight);

    static std::string buildFunBodyNotWellSorted(const std::string& body,
                                                 int rowLeft, int colLeft,
                                                 int rowRight, int colRight);

    static std::string buildFunBodyNotWellSorted(const std::string& name,
                                                 const std::string& body,
                                                 int rowLeft, int colLeft,
                                                 int rowRight, int colRight);

    static std::string buildSortAlreadyExists(const std::string& name);

    static std::string buildSpecConstAlreadyExists(const std::string& name);

    static std::string buildMetaSpecConstAlreadyExists(const std::string& name);

    static std::string buildRightAssocParamCount(const std::string& name);

    static std::string buildRightAssocRetSort(const std::string& name);

    static std::string buildLeftAssocParamCount(const std::string& name);

    static std::string buildLeftAssocRetSort(const std::string& name);

    static std::string buildChainableAndPairwise(const std::string& name);

    static std::string buildChainableParamCount(const std::string& name);

    static std::string buildChainableParamSort(const std::string& name);

    static std::string buildChainableRetSort(const std::string& name);

    static std::string buildPairwiseParamCount(const std::string& name);

    static std::string buildPairwiseParamSort(const std::string& name);

    static std::string buildPairwiseRetSort(const std::string& name);

    static std::string buildTermNotWellSorted(const std::string& term,
                                              int rowLeft, int colLeft,
                                              int rowRight, int colRight);

    static std::string buildStackUnpoppable(unsigned long levels);

    static std::string buildLiteralUnknownSort(const std::string& literalType);

    static std::string buildLiteralMultipleSorts(const std::string& literalType,
                                                 const std::vector<smtlib::ast::SortPtr>& possibleSorts);

    static std::string buildFunUnknownDecl(const std::string& name,
                                           const std::string& retSort);

    static std::string buildFunUnknownDecl(const std::string& name,
                                           size_t paramCount,
                                           const std::string& retSort);

    static std::string buildFunUnknownDecl(const std::string& name,
                                           const std::vector<std::string>& argSorts);

    static std::string buildFunUnknownDecl(const std::string& name,
                                           const std::vector<std::string>& argSorts,
                                           const std::string& retSort);

    static std::string buildFunMultipleDecls(const std::string& name,
                                             size_t paramCount,
                                             const std::string& retSort);

    static std::string buildFunMultipleDecls(const std::string& name,
                                             const std::vector<std::string>& argSorts,
                                             const std::vector<std::string>& retSorts);

    static std::string buildQuantTermWrongSort(const std::string& term,
                                               const std::string& wrongSort,
                                               const std::string& rightSort,
                                               int rowLeft, int colLeft,
                                               int rowRight, int colRight);

    static std::string buildPatternMismatch(const std::string& sort,
                                            const std::string& pattern);

    static std::string buildCasesMismatch(const std::vector<smtlib::ast::SortPtr>& caseSorts);

    static std::string buildParamFunDeclUnusedSortParams(const std::vector<std::string>& unusedParams);

    static std::string buildParamDatatypeDeclUnusedSortParams(const std::vector<std::string>& unusedParams);

    static std::string buildSortDefUnusedSortParams(const std::vector<std::string>& unusedParams);

    static std::string buildAttrValueSortDecl(const std::string& attrValue);

    static std::string buildAttrValueFunDecl(const std::string& attrValue);

    static std::string buildAttrValueSymbol(const std::string& attrValue);

    static std::string buildDeclDatatypesCount(size_t sortDeclCount,
                                               size_t datatypeDeclCount);

    static std::string buildDeclDatatypeArity(const std::string& name,
                                              long arity,
                                              size_t paramCount);

    static std::string buildDefFunsRecCount(size_t declCount,
                                            size_t bodyCount);

    static std::string buildLocDataPairUnaccepted(smtlib::sep::SortPtr loc,
                                                  smtlib::sep::SortPtr data,
                                                  const std::vector<std::string>& acceptedPairs);

    static std::string buildLocSortUnaccepted(smtlib::sep::SortPtr loc,
                                              const std::vector<std::string>& acceptedLoc);
};

typedef std::shared_ptr<ErrorMessages> ErrorMessagesPtr;

#endif //SLCOMP_PARSER_ERROR_MESSAGES_H
