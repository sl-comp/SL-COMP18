#include "error_messages.h"

#include "ast/ast_sort.h"
#include "sep/sep_sort.h"

using namespace std;
using namespace smtlib::ast;

const string ErrorMessages::ERR_INVALID_IND_CASE = "Not a valid inductive case";
const string ErrorMessages::ERR_NULL_NODE_VISIT = "Attempt to visit NULL node";
const string ErrorMessages::ERR_ATTR_MISSING_KEYWORD = "Missing keyword from attribute";
const string ErrorMessages::ERR_SYMBOL_MALFORMED = "Malformed symbol";
const string ErrorMessages::ERR_KEYWORD_MALFORMED = "Malformed keyword";
const string ErrorMessages::ERR_PROP_LIT_MISSING_SYMBOL = "Missing symbol from propositional literal";
const string ErrorMessages::ERR_ASSERT_MISSING_TERM = "Missing term from assert command";
const string ErrorMessages::ERR_DECL_CONST_MISSING_NAME = "Missing constant name from declare-const command";
const string ErrorMessages::ERR_DECL_CONST_MISSING_SORT = "Missing constant sort from declare-const command";
const string ErrorMessages::ERR_DECL_DATATYPE_MISSING_NAME = "Missing datatype name from declare-datatype command";
const string ErrorMessages::ERR_DECL_DATATYPE_MISSING_DECL = "Missing datatype declaration from declare-datatype command";
const string ErrorMessages::ERR_DECL_DATATYPES_MISSING_SORTS = "Empty sort declaration list for declare-datatypes command";
const string ErrorMessages::ERR_DECL_DATATYPES_MISSING_DECLS = "Empty datatype declaration list for declare-datatypes command";
const string ErrorMessages::ERR_DECL_FUN_MISSING_NAME = "Missing function name from declare-fun command";
const string ErrorMessages::ERR_DECL_FUN_MISSING_RET = "Missing function sort from declare-fun command";
const string ErrorMessages::ERR_DECL_SORT_MISSING_NAME = "Missing sort name from declare-sort command";
const string ErrorMessages::ERR_DECL_SORT_MISSING_ARITY = "Missing arity from declare-sort command";
const string ErrorMessages::ERR_DECL_HEAP_MISSING_LOC = "Missing location sort from declare-heap command";
const string ErrorMessages::ERR_DECL_HEAP_MISSING_DATA = "Missing data sort from declare-heap command";
const string ErrorMessages::ERR_DEF_FUN_MISSING_DEF = "Missing function definition from define-fun command";
const string ErrorMessages::ERR_DEF_FUN_REC_MISSING_DEF = "Missing function definition from define-fun-rec command";
const string ErrorMessages::ERR_DEF_FUNS_REC_EMPTY_DECLS = "Empty function declaration list from define-funs-rec command";
const string ErrorMessages::ERR_DEF_FUNS_REC_EMPTY_BODIES = "Empty function body list from define-funs-rec command";
const string ErrorMessages::ERR_DEF_SORT_MISSING_NAME = "Missing sort name from define-sort command";
const string ErrorMessages::ERR_DEF_SORT_MISSING_DEF = "Missing sort definition from define-sort command";
const string ErrorMessages::ERR_ECHO_EMPTY_STRING = "Attempting to echo empty string";
const string ErrorMessages::ERR_GET_INFO_MISSING_FLAG = "Missing flag in get-info command";
const string ErrorMessages::ERR_GET_OPT_MISSING_OPT = "Missing option in get-option command";
const string ErrorMessages::ERR_GET_VALUE_EMPTY_TERMS = "Empty term list for get-value command";
const string ErrorMessages::ERR_POP_MISSING_NUMERAL = "Missing numeral in pop command";
const string ErrorMessages::ERR_PUSH_MISSING_NUMERAL = "Missing numeral in push command";
const string ErrorMessages::ERR_SET_INFO_MISSING_INFO = "Missing info in set-info command";
const string ErrorMessages::ERR_SET_LOGIC_MISSING_LOGIC = "Missing logic in set-logic command";
const string ErrorMessages::ERR_SET_OPT_MISSING_OPT = "Missing option in set-option command";
const string ErrorMessages::ERR_OPT_VALUE_STRING = "Option value should be string literal";
const string ErrorMessages::ERR_OPT_VALUE_NUMERAL = "Option value should be numeral literal";
const string ErrorMessages::ERR_OPT_VALUE_BOOLEAN = "Option value should be boolean";
const string ErrorMessages::ERR_FUN_DECL_MISSING_NAME = "Missing name from function declaration";
const string ErrorMessages::ERR_FUN_DECL_MISSING_RET = "Missing return sort from function declaration";
const string ErrorMessages::ERR_FUN_DEF_MISSING_SIG = "Missing signature from function definition";
const string ErrorMessages::ERR_FUN_DEF_MISSING_BODY = "Missing body from function definition";
const string ErrorMessages::ERR_ID_MISSING_SYMBOL = "Missing symbol from identifier";
const string ErrorMessages::ERR_ID_EMPTY_INDICES = "Indexed identifier has no indices";
const string ErrorMessages::ERR_QUAL_ID_MISSING_ID = "Missing identifier from qualified identifier";
const string ErrorMessages::ERR_QUAL_ID_MISSING_SORT = "Missing sort from qualified identifier";
const string ErrorMessages::ERR_THEORY_MISSING_NAME = "Missing theory name";
const string ErrorMessages::ERR_THEORY_EMPTY_ATTRS = "Theory has no attributes";
const string ErrorMessages::ERR_LOGIC_MISSING_NAME = "Missing logic name";
const string ErrorMessages::ERR_LOGIC_EMPTY_ATTRS = "Logic has no attributes";
const string ErrorMessages::ERR_ATTR_VALUE_STRING = "Attribute value should be string literal";
const string ErrorMessages::ERR_ATTR_VALUE_SORTS = "Attribute value should be a list of sort symbol declarations";
const string ErrorMessages::ERR_ATTR_VALUE_SORTS_EMPTY = "Empty list of sort symbol declarations";
const string ErrorMessages::ERR_ATTR_VALUE_FUNS = "Attribute value should be a list of function symbol declarations";
const string ErrorMessages::ERR_ATTR_VALUE_FUNS_EMPTY = "Empty list of function symbol declarations";
const string ErrorMessages::ERR_ATTR_VALUE_THEORIES = "Attribute value should be a list of theory names";
const string ErrorMessages::ERR_ATTR_VALUE_THEORIES_EMPTY = "Empty list of theory names";
const string ErrorMessages::ERR_SORT_MISSING_ID = "Missing identifier from sort";
const string ErrorMessages::ERR_SORT_EMPTY_ARGS = "Parametric sort has no arguments";
const string ErrorMessages::ERR_SORT_SYM_DECL_MISSING_ID = "Missing identifier from sort symbol declaration";
const string ErrorMessages::ERR_SORT_SYM_DECL_MISSING_ARITY = "Missing arity from sort symbol declaration";
const string ErrorMessages::ERR_SPEC_CONST_DECL_MISSING_CONST = "Missing constant from specification constant symbol declaration";
const string ErrorMessages::ERR_SPEC_CONST_DECL_MISSING_SORT = "Missing sort from specification constant symbol declaration";
const string ErrorMessages::ERR_META_SPEC_CONST_DECL_MISSING_CONST = "Missing constant from meta specification constant symbol declaration";
const string ErrorMessages::ERR_META_SPEC_CONST_DECL_MISSING_SORT = "Missing sort from meta specification constant symbol declaration";
const string ErrorMessages::ERR_FUN_SYM_DECL_MISSING_ID = "Missing identifier from function symbol declaration";
const string ErrorMessages::ERR_FUN_SYM_DECL_EMPTY_SIG = "Empty signature for function symbol declaration";
const string ErrorMessages::ERR_PARAM_FUN_SYM_DECL_EMPTY_PARAMS = "Empty parameter list for parametric function symbol declaration";
const string ErrorMessages::ERR_PARAM_FUN_SYM_DECL_MISSING_ID = "Missing identifier from parametric function symbol declaration";
const string ErrorMessages::ERR_PARAM_FUN_SYM_DECL_EMPTY_SIG = "Empty signature for parametric function declaration";
const string ErrorMessages::ERR_SORT_DECL_MISSING_SYMBOL = "Missing symbol from sort declaration";
const string ErrorMessages::ERR_SORT_DECL_MISSING_ARITY = "Missing arity from sort declaration";
const string ErrorMessages::ERR_SEL_DECL_MISSING_SYMBOL = "Missing symbol from selector declaration";
const string ErrorMessages::ERR_SEL_DECL_MISSING_SORT = "Missing sort from selector declaration";
const string ErrorMessages::ERR_CONS_DECL_MISSING_SYMBOL = "Missing symbol from constructor declaration";
const string ErrorMessages::ERR_DATATYPE_DECL_EMPTY_CONS = "Empty constructor list for datatype declaration";
const string ErrorMessages::ERR_PARAM_DATATYPE_DECL_EMPTY_PARAMS = "Empty parameter list for parametric datatype declaration";
const string ErrorMessages::ERR_PARAM_DATATYPE_DECL_EMPTY_CONS = "Empty constructor list for parametric datatype declaration";
const string ErrorMessages::ERR_QUAL_CONS_MISSING_SYMBOL = "Missing symbol from qualified constructor";
const string ErrorMessages::ERR_QUAL_CONS_MISSING_SORT = "Missing sort from qualified constructor";
const string ErrorMessages::ERR_QUAL_PATTERN_MISSING_CONS = "Missing constructor from qualified pattern";
const string ErrorMessages::ERR_QUAL_PATTERN_EMPTY_SYMS = "Empty symbol list for qualified pattern";
const string ErrorMessages::ERR_MATCH_CASE_MISSING_PATTERN = "Missing pattern from match case";
const string ErrorMessages::ERR_MATCH_CASE_MISSING_TERM = "Missing term from match case";
const string ErrorMessages::ERR_QUAL_TERM_MISSING_ID = "Missing identifier from qualified term";
const string ErrorMessages::ERR_QUAL_TERM_EMPTY_TERMS = "Empty term list for qualified term";
const string ErrorMessages::ERR_LET_TERM_MISSING_TERM = "Missing term from let term";
const string ErrorMessages::ERR_LET_TERM_EMPTY_VARS = "Empty variable binding list for let term";
const string ErrorMessages::ERR_FORALL_TERM_MISSING_TERM = "Missing term from forall term";
const string ErrorMessages::ERR_FORALL_TERM_EMPTY_VARS = "Empty variable binding list for forall term";
const string ErrorMessages::ERR_EXISTS_TERM_MISSING_TERM = "Missing term from exists term";
const string ErrorMessages::ERR_EXISTS_TERM_EMPTY_VARS = "Empty variable binding list for exists term";
const string ErrorMessages::ERR_MATCH_TERM_MISSING_TERM = "Missing term from match term";
const string ErrorMessages::ERR_MATCH_TERM_EMPTY_CASES = "Empty case list for match term";
const string ErrorMessages::ERR_ANNOT_TERM_MISSING_TERM = "Missing term from annotated term";
const string ErrorMessages::ERR_ANNOT_TERM_EMPTY_ATTRS = "Empty attribute list for annotated term";
const string ErrorMessages::ERR_SORTED_VAR_MISSING_SYMBOL = "Missing symbol from sorted variable";
const string ErrorMessages::ERR_SORTED_VAR_MISSING_SORT = "Missing sort from sorted variable";
const string ErrorMessages::ERR_VAR_BIND_MISSING_SYMBOL = "Missing symbol from variable binding";
const string ErrorMessages::ERR_VAR_BIND_MISSING_SORT = "Missing sort from variable binding";
const string ErrorMessages::ERR_UFLD_LVL_NEGATIVE = "Negative value for unfolding level";
const string ErrorMessages::ERR_UFLD_LVL_INVALID = "Invalid value for unfolding level";
const string ErrorMessages::ERR_OUT_PATH_INVALID = "Invalid value for unfolding output path";
const string ErrorMessages::ERR_UNSPECIFIED_LOC_SORT = "Emp term with unspecified location sort";
const string ErrorMessages::ERR_UNSPECIFIED_DATA_SORT = "Emp term with unspecified data sort";
const string ErrorMessages::ERR_UNSPECIFIED_NIL_SORT = "Nil term with unspecified location sort";
const string ErrorMessages::ERR_PTO_LEFT_NIL = "Points-to with nil as first argument";

string ErrorMessages::extractFirstN(const string& str, unsigned long n) {
    if (str.length() > n)
        return string(str, 0, n) + "[...]";
    else
        return str;
}

void ErrorMessages::printStringArray(stringstream& ss,
                                     const vector<string>& array,
                                     const string& separator) {
    bool first = true;
    for (const auto& item : array) {
        if (first) {
            first = false;
        } else {
            ss << separator;
        }
        ss << item;
    }
}

string ErrorMessages::buildTheoryUnloadable(const string& theory) {
    return "Cannot load theory '" + theory + "'";
}

string ErrorMessages::buildLogicUnloadable(const string& logic) {
    return "Cannot load logic '" + logic + "'";
}

string ErrorMessages::buildTheoryUnknown(const string& theory) {
    return "Unknown theory '" + theory + "'";
}

string ErrorMessages::buildLogicUnknown(const string& logic) {
    return "Unknown logic '" + logic + "'";
}

string ErrorMessages::buildSortUnknown(const string& name,
                                       int rowLeft, int colLeft,
                                       int rowRight, int colRight) {
    stringstream ss;
    ss << "Unknown sort '" << name << "'";

    if (rowLeft && colLeft && rowRight && colRight)
        ss << " (" << rowLeft << ":" << colLeft << " - " << rowRight << ":" << colRight << ")";

    return ss.str();
}

string ErrorMessages::buildSortArity(const string& name,
                                     unsigned long arity,
                                     size_t argCount,
                                     int rowLeft, int colLeft,
                                     int rowRight, int colRight) {
    stringstream ss;
    ss << "Sort '" << name << "' should have " << arity << " arguments, not " << argCount;

    if (rowLeft && colLeft && rowRight && colRight)
        ss << " (" << rowLeft << ":" << colLeft << " - " << rowRight << ":" << colRight << ")";

    return ss.str();
}

string ErrorMessages::buildSortParamArity(const string& sort,
                                          const string& sortName) {
    return sort + ": '" + sortName + "' is a sort parameter - it should have an arity of 0";
}

string ErrorMessages::buildAssertTermNotWellSorted(const string& term,
                                                   int rowLeft, int colLeft,
                                                   int rowRight, int colRight) {
    stringstream ss;
    ss << "Assertion term '" << extractFirstN(term, 50) << "'";

    if (rowLeft && colLeft && rowRight && colRight)
        ss << " (" << rowLeft << ":" << colLeft << " - " << rowRight << ":" << colRight << ")";

    ss << " is not well-sorted";
    return ss.str();
}

string ErrorMessages::buildAssertTermNotBool(const string& term,
                                             const string& termSort,
                                             int rowLeft, int colLeft,
                                             int rowRight, int colRight) {
    stringstream ss;
    ss << "Assertion term '" << extractFirstN(term, 50) << "'";

    if (rowLeft && colLeft && rowRight && colRight)
        ss << " (" << rowLeft << ":" << colLeft << " - " << rowRight << ":" << colRight << ")";

    ss << " is of type " << termSort << ", not Bool";
    return ss.str();
}

string ErrorMessages::buildConstAlreadyExists(const string& name) {
    return "Constant '" + name + "' already exists with same sort";
}

string ErrorMessages::buildConstUnknown(const string& name) {
    return "Unknown constant '" + name + "'";
}

string ErrorMessages::buildFunAlreadyExists(const string& name) {
    return "Function '" + name + "' already exists with the same signature";
}

string ErrorMessages::buildSortAlreadyExists(const string& name) {
    return "Sort symbol '" + name + "' already exists";
}

string ErrorMessages::buildSpecConstAlreadyExists(const string& name) {
    return "Specification constant '" + name + "' already exists";
}

string ErrorMessages::buildMetaSpecConstAlreadyExists(const string& name) {
    return "Sort for meta specification constant '" + name + "' already declared";
}

string ErrorMessages::buildRightAssocParamCount(const string& name) {
    return "Function '" + name +
           "' cannot be right associative - it does not have 2 parameters";
}

string ErrorMessages::buildRightAssocRetSort(const string& name) {
    return "Function '" + name +
           "' cannot be right associative - sort of second parameter not the same as return sort";
}

string ErrorMessages::buildLeftAssocParamCount(const string& name) {
    return "Function '" + name +
           "' cannot be left associative - it does not have 2 parameters";
}

string ErrorMessages::buildLeftAssocRetSort(const string& name) {
    return "Function '" + name +
           "' cannot be left associative - sort of first parameter not the same as return sort";
}

string ErrorMessages::buildChainableAndPairwise(const string& name) {
    return "Function '" + name +
           "' cannot be both chainable and pairwise";
}

string ErrorMessages::buildChainableParamCount(const string& name) {
    return "Function '" + name +
           "' cannot be chainable - it does not have 2 parameters";
}

string ErrorMessages::buildChainableParamSort(const string& name) {
    return "Function '" + name + "' cannot be chainable " + "- parameters do not have the same sort";
}

string ErrorMessages::buildChainableRetSort(const string& name) {
    return "Function '" + name + "' cannot be chainable " + "- return sort is not Bool";
}

string ErrorMessages::buildPairwiseParamCount(const string& name) {
    return "Function '" + name +
           "' cannot be chainable - it does not have 2 parameters";
}

string ErrorMessages::buildPairwiseParamSort(const string& name) {
    return "Function '" + name + "' cannot be pairwise " + "- parameters do not have the same sort";
}

string ErrorMessages::buildPairwiseRetSort(const string& name) {
    return "Function '" + name + "' cannot be pairwise " + "- return sort is not Bool";
}

string ErrorMessages::buildFunBodyWrongSort(const string& body,
                                            const string& wrongSort,
                                            const string& rightSort,
                                            int rowLeft, int colLeft,
                                            int rowRight, int colRight) {
    stringstream ss;
    ss << "Function body '" << extractFirstN(body, 50) << "'";

    if (rowLeft && colLeft && rowRight && colRight)
        ss << " (" << rowLeft << ":" << colLeft << " - " << rowRight << ":" << colRight << ")";

    ss << " is of type " << wrongSort << ", not " << rightSort;
    return ss.str();
}

string ErrorMessages::buildFunBodyWrongSort(const string& name,
                                            const string& body,
                                            const string& wrongSort,
                                            const string& rightSort,
                                            int rowLeft, int colLeft,
                                            int rowRight, int colRight) {
    stringstream ss;
    ss << "The body of function " << name << ", '" << extractFirstN(body, 50) << "'";

    if (rowLeft && colLeft && rowRight && colRight)
        ss << " (" << rowLeft << ":" << colLeft << " - " << rowRight << ":" << colRight << ")";

    ss << " is of type " << wrongSort << ", not " << rightSort;
    return ss.str();
}

string ErrorMessages::buildFunBodyNotWellSorted(const string& body,
                                                int rowLeft, int colLeft,
                                                int rowRight, int colRight) {
    stringstream ss;
    ss << "Function body '" << extractFirstN(body, 50) << "'";

    if (rowLeft && colLeft && rowRight && colRight)
        ss << " (" << rowLeft << ":" << colLeft << " - " << rowRight << ":" << colRight << ")";

    ss << " is not well-sorted";
    return ss.str();
}

string ErrorMessages::buildFunBodyNotWellSorted(const string& name,
                                                const string& body,
                                                int rowLeft, int colLeft,
                                                int rowRight, int colRight) {
    stringstream ss;
    ss << "The body of function '" << name << "', '" << extractFirstN(body, 50) << "'";

    if (rowLeft && colLeft && rowRight && colRight)
        ss << " (" << rowLeft << ":" << colLeft << " - " << rowRight << ":" << colRight << ")";

    ss << " is not well-sorted";
    return ss.str();
}

string ErrorMessages::buildTermNotWellSorted(const string& term,
                                             int rowLeft, int colLeft,
                                             int rowRight, int colRight) {
    stringstream ss;
    ss << "Term '" << extractFirstN(term, 50) << "'";

    if (rowLeft && colLeft && rowRight && colRight)
        ss << " (" << rowLeft << ":" << colLeft << " - " << rowRight << ":" << colRight << ")";

    ss << " is not well-sorted";
    return ss.str();
}

string ErrorMessages::buildStackUnpoppable(unsigned long levels) {
    stringstream ss;
    ss << "Stack not deep enough to pop " << levels;
    if (levels == 1)
        ss << " level";
    else
        ss << " levels";

    return ss.str();
}


string ErrorMessages::buildLogicAlreadySet(const string& logic) {
    return "Logic already set to '" + logic + "'";
}

string ErrorMessages::buildTheoryAlreadyLoaded(const string& theory) {
    return "Theory '" + theory + "' already loaded";
}

string ErrorMessages::buildConstNoSorts(const string& name) {
    return "No possible sorts for constant '" + name + "'";
}

string ErrorMessages::buildConstMultipleSorts(const string& name,
                                              const std::vector<SortPtr>& possibleSorts) {
    stringstream ss;
    ss << "Multiple possible sorts for constant '" << name << "': ";
    printArray(ss, possibleSorts, ", ");

    return ss.str();
}

string ErrorMessages::buildConstWrongSort(const string& name,
                                          const string& wrongSort,
                                          const std::vector<SortPtr>& possibleSorts) {
    stringstream ss;
    ss << "Constant '" << name << "' cannot be of sort " << wrongSort << ". Possible sorts: ";
    printArray(ss, possibleSorts, ", ");

    return ss.str();
}

string ErrorMessages::buildLiteralUnknownSort(const string& literalType) {
    return "No declared sort for " + literalType + " literals";
}

string ErrorMessages::buildLiteralMultipleSorts(const string& literalType,
                                                const std::vector<SortPtr>& possibleSorts) {
    stringstream ss;
    ss << "Multiple declared sorts for " + literalType + " literals: ";
    printArray(ss, possibleSorts, ", ");
    return ss.str();
}

string ErrorMessages::buildFunUnknownDecl(const string& name,
                                          const string& retSort) {
    stringstream ss;
    ss << "No known declaration for function '" << name << "' with return sort " << retSort;
    return ss.str();
}

string ErrorMessages::buildFunUnknownDecl(const string& name,
                                          size_t paramCount,
                                          const string& retSort) {
    stringstream ss;
    ss << "No known declaration for function '" << name << "' with "
       << paramCount << " parameters and return sort " << retSort;

    return ss.str();
}

string ErrorMessages::buildFunUnknownDecl(const string& name,
                                          const vector<string>& argSorts) {
    stringstream ss;
    ss << "No known declaration for function '" << name << "' with parameter list (";
    printStringArray(ss, argSorts, " ");
    ss << ")";

    return ss.str();
}

string ErrorMessages::buildFunUnknownDecl(const string& name,
                                          const vector<string>& argSorts,
                                          const string& retSort) {
    stringstream ss;
    ss << buildFunUnknownDecl(name, argSorts) << " and return sort " << retSort;

    return ss.str();
}

string ErrorMessages::buildFunMultipleDecls(const string& name,
                                            size_t paramCount,
                                            const string& retSort) {
    stringstream ss;
    ss << "Multiple declarations for function '" << name << "' with "
       << paramCount << " parameters and return sort " << retSort;

    return ss.str();
}

string ErrorMessages::buildFunMultipleDecls(const string& name,
                                            const vector<string>& argSorts,
                                            const vector<string>& retSorts) {
    stringstream ss;
    ss << "Multiple declarations for function '" << name << "' with parameter list (";
    printStringArray(ss, argSorts, " ");
    ss << "). Possible return sorts: ";
    printStringArray(ss, retSorts, ", ");

    return ss.str();
}

string ErrorMessages::buildQuantTermWrongSort(const string& term,
                                              const string& wrongSort,
                                              const string& rightSort,
                                              int rowLeft, int colLeft,
                                              int rowRight, int colRight) {
    stringstream ss;
    ss << "Quantified term '" << extractFirstN(term, 50) << "' ("
       << rowLeft << ":" << colLeft << " - " << rowRight << ":" << colRight
       << ") is of type " << wrongSort << ", not " << rightSort;

    return ss.str();
}

string ErrorMessages::buildPatternMismatch(const string& sort, const string& pattern) {
    stringstream ss;
    ss << "Cannot match term of sort " << sort << " with pattern " << pattern;

    return ss.str();
}

string ErrorMessages::buildCasesMismatch(const std::vector<SortPtr>& caseSorts) {
    stringstream ss;
    ss << "Cases have different sorts: ";
    printArray(ss, caseSorts, " ");

    return ss.str();
}

string ErrorMessages::buildParamFunDeclUnusedSortParams(const vector<string>& unusedParams) {
    long diff = unusedParams.size();

    stringstream ss;
    ss << "Sort parameter" << ((diff == 1) ? " " : "s ");
    printStringArray(ss, unusedParams, ", ");
    ss << ((diff == 1) ? " is " : " are ") << "not used in parametric function declaration";

    return ss.str();
}

string ErrorMessages::buildParamDatatypeDeclUnusedSortParams(const vector<string>& unusedParams) {
    long diff = unusedParams.size();

    stringstream ss;
    ss << "Sort parameter" << ((diff == 1) ? " " : "s ");
    printStringArray(ss, unusedParams, ", ");
    ss << ((diff == 1) ? " is " : " are ") << "not used in parametric datatype declaration";

    return ss.str();
}

string ErrorMessages::buildSortDefUnusedSortParams(const vector<string>& unusedParams) {
    long diff = unusedParams.size();

    stringstream ss;
    ss << "Sort parameter" << ((diff == 1) ? " " : "s ");
    printStringArray(ss, unusedParams, ", ");
    ss << ((diff == 1) ? " is " : " are ") << "not used in sort definition";

    return ss.str();
}

string ErrorMessages::buildAttrValueSortDecl(const string& attrValue) {
    return "Attribute value '" + attrValue + "' should be a sort symbol declaration";
}

string ErrorMessages::buildAttrValueFunDecl(const string& attrValue) {
    return "Attribute value '" + attrValue +"' should be a function symbol declaration";
}

string ErrorMessages::buildAttrValueSymbol(const string& attrValue) {
    return "Attribute value '" + attrValue + "' should be a symbol";
}

string ErrorMessages::buildDeclDatatypesCount(size_t sortDeclCount,
                                              size_t datatypeDeclCount) {
    stringstream ss;
    ss << "Number of sort declarations (" << sortDeclCount
       << ") is not equal to the number of datatype declarations ("
       << datatypeDeclCount << ") in declare-datatypes command";

    return ss.str();
}

string ErrorMessages::buildDeclDatatypeArity(const string& name,
                                             long arity,
                                             size_t paramCount) {
    stringstream ss;
    ss << "Datatype '" << name << "' has an arity of " << arity
       << " but its declaration has " << paramCount << " parameter"
       << (paramCount == 1 ? "" : "s");

    return ss.str();
}

string ErrorMessages::buildDefFunsRecCount(size_t declCount,
                                           size_t bodyCount) {
    stringstream ss;
    ss << "Number of function declarations (" << declCount
       << ") is not equal to the number of function bodies ("
       << bodyCount << ") in define-funs-rec command";

    return ss.str();
}

std::string ErrorMessages::buildLocDataPairUnaccepted(smtlib::sep::SortPtr loc,
                                                      smtlib::sep::SortPtr data,
                                                      const vector<string>& acceptedPairs) {
    stringstream ss;
    ss << "(" << loc->toString() << ", " << data->toString() << ") "
       << "is not an accepted pair of location and data sorts. "
       << "Accepted pairs are: ";
    printStringArray(ss, acceptedPairs, " ");
    return ss.str();
}

std::string ErrorMessages::buildLocSortUnaccepted(smtlib::sep::SortPtr loc,
                                                  const vector<string>& acceptedLoc) {
    stringstream ss;
    ss << loc->toString() << " is not an accepted location sort. "
       << "Accepted location sorts are: ";
    printStringArray(ss, acceptedLoc, " ");
    return ss.str();
}