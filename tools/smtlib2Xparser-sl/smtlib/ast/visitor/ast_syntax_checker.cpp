#include "ast_syntax_checker.h"

#include "ast/ast_attribute.h"
#include "ast/ast_command.h"
#include "ast/ast_logic.h"
#include "ast/ast_script.h"
#include "ast/ast_s_expr.h"
#include "ast/ast_symbol_decl.h"
#include "ast/ast_term.h"
#include "ast/ast_theory.h"
#include "util/error_messages.h"
#include "util/global_values.h"

#include <iostream>

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

SyntaxChecker::ErrorPtr SyntaxChecker::addError(const string& message, const NodePtr& node,
                                                SyntaxChecker::ErrorPtr& err) {
    if (!err) {
        err = make_shared<Error>(message, node);
        errors.push_back(err);
    } else {
        err->messages.push_back(message);
    }

    return err;
}

SyntaxChecker::ErrorPtr SyntaxChecker::checkParamUsage(const std::vector<SymbolPtr>& params,
                                                       unordered_map<string, bool>& paramUsage,
                                                       const SortPtr& sort, const NodePtr& source,
                                                       SyntaxChecker::ErrorPtr& err) {
    if (!sort)
        return err;

    string name = sort->identifier->toString();
    bool isParam = false;
    for (const auto& param : params) {
        if (name == param->toString())
            isParam = true;
    }

    if (isParam) {
        paramUsage[name] = true;

        if (!sort->arguments.empty()) {
            err = addError(ErrorMessages::buildSortParamArity(sort->toString(), name), source, err);
        }
    } else {
        std::vector<SortPtr>& argSorts = sort->arguments;
        for (const auto& arg : argSorts) {
            checkParamUsage(params, paramUsage, arg, source, err);
        }
    }

    return err;
}

void SyntaxChecker::visit(const AttributePtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->keyword) {
        err = addError(ErrorMessages::ERR_ATTR_MISSING_KEYWORD, node, err);
    } else {
        visit0(node->keyword);
    }

    visit0(node->value);
}

void SyntaxChecker::visit(const CompAttributeValuePtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    visit0(node->values);
}

void SyntaxChecker::visit(const SymbolPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!regex_match(node->value, regexSymbol)) {
        err = addError(ErrorMessages::ERR_SYMBOL_MALFORMED, node, err);
    }
}

void SyntaxChecker::visit(const KeywordPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!regex_match(node->value, regexKeyword)) {
        err = addError(ErrorMessages::ERR_KEYWORD_MALFORMED, node, err);
    }
}

void SyntaxChecker::visit(const MetaSpecConstantPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(const BooleanValuePtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(const PropLiteralPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_PROP_LIT_MISSING_SYMBOL, node, err);
    } else {
        visit0(node->symbol);
    }
}

void SyntaxChecker::visit(const AssertCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->term) {
        err = addError(ErrorMessages::ERR_ASSERT_MISSING_TERM, node, err);
    } else {
        visit0(node->term);
    }
}

void SyntaxChecker::visit(const CheckSatCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(const CheckUnsatCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(const CheckSatAssumCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    visit0(node->assumptions);
}

void SyntaxChecker::visit(const DeclareConstCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_DECL_CONST_MISSING_NAME, node, err);
    } else {
        visit0(node->symbol);
    }

    if (!node->sort) {
        err = addError(ErrorMessages::ERR_DECL_CONST_MISSING_SORT, node, err);
    } else {
        visit0(node->sort);
    }
}


void SyntaxChecker::visit(const DeclareDatatypeCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_DECL_DATATYPE_MISSING_NAME, node, err);
    } else {
        visit0(node->symbol);
    }

    if (!node->declaration) {
        err = addError(ErrorMessages::ERR_DECL_DATATYPE_MISSING_DECL, node, err);
    } else {
        visit0(node->declaration);
    }
}

void SyntaxChecker::visit(const DeclareDatatypesCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->sorts.empty()) {
        err = addError(ErrorMessages::ERR_DECL_DATATYPES_MISSING_SORTS, node, err);
    }

    if (node->declarations.empty()) {
        err = addError(ErrorMessages::ERR_DECL_DATATYPES_MISSING_DECLS, node, err);
    }

    size_t sortCount = node->sorts.size();
    size_t declCount = node->declarations.size();

    if (node->sorts.size() != node->declarations.size()) {
        err = addError(ErrorMessages::buildDeclDatatypesCount(sortCount, declCount), node, err);
    }

    size_t minCount = sortCount < declCount ? sortCount : declCount;
    for (size_t i = 0; i < minCount; i++) {
        long arity = node->sorts[i]->arity->value;
        size_t paramCount = 0;
        ParametricDatatypeDeclarationPtr decl =
                dynamic_pointer_cast<ParametricDatatypeDeclaration>(node->declarations[i]);
        if (decl) {
            paramCount = decl->parameters.size();
        }

        if (arity != paramCount) {
            err = addError(ErrorMessages::buildDeclDatatypeArity(
                    node->sorts[i]->symbol->toString(), arity, paramCount), node, err);
        }
    }

    visit0(node->sorts);

    visit0(node->declarations);
}

void SyntaxChecker::visit(const DeclareFunCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_DECL_FUN_MISSING_NAME, node, err);
    } else {
        visit0(node->symbol);
    }

    visit0(node->parameters);

    if (!node->sort) {
        err = addError(ErrorMessages::ERR_DECL_FUN_MISSING_RET, node, err);
    } else {
        visit0(node->sort);
    }
}

void SyntaxChecker::visit(const DeclareSortCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_DECL_SORT_MISSING_NAME, node, err);
    } else {
        visit0(node->symbol);
    }

    if (!node->arity) {
        err = addError(ErrorMessages::ERR_DECL_SORT_MISSING_ARITY, node, err);
    } else {
        visit0(node->arity);
    }
}

void SyntaxChecker::visit(const DeclareHeapCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    for(const auto& pair : node->locDataPairs) {
        if (!pair.first) {
            err = addError(ErrorMessages::ERR_DECL_HEAP_MISSING_LOC, node, err);
        } else {
            visit0(pair.first);
        }

        if (!pair.second) {
            err = addError(ErrorMessages::ERR_DECL_HEAP_MISSING_DATA, node, err);
        } else {
            visit0(pair.second);
        }
    }
}

void SyntaxChecker::visit(const DefineFunCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->definition) {
        err = addError(ErrorMessages::ERR_DEF_FUN_MISSING_DEF, node, err);
    } else {
        visit0(node->definition);
    }
}

void SyntaxChecker::visit(const DefineFunRecCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->definition) {
        err = addError(ErrorMessages::ERR_DEF_FUN_REC_MISSING_DEF, node, err);
    } else {
        visit0(node->definition);
    }
}

void SyntaxChecker::visit(const DefineFunsRecCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->declarations.empty()) {
        err = addError(ErrorMessages::ERR_DEF_FUNS_REC_EMPTY_DECLS, node, err);
    }

    if (node->bodies.empty()) {
        err = addError(ErrorMessages::ERR_DEF_FUNS_REC_EMPTY_BODIES, node, err);
    }

    size_t declCount = node->declarations.size();
    size_t bodyCount = node->bodies.size();

    if (declCount != bodyCount) {
        err = addError(ErrorMessages::buildDefFunsRecCount(declCount, bodyCount), node, err);
    }

    visit0(node->declarations);
    visit0(node->declarations);
}

void SyntaxChecker::visit(const DefineSortCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    // Check symbol
    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_DEF_SORT_MISSING_NAME, node, err);
    } else {
        visit0(node->symbol);
    }

    // Check parameter list
    visit0(node->parameters);

    // Check definition
    if (!node->sort) {
        err = addError(ErrorMessages::ERR_DEF_SORT_MISSING_DEF, node, err);
    } else {
        visit0(node->sort);
    }

    // Check parameter usage
    unordered_map<string, bool> paramUsage;
    err = checkParamUsage(node->parameters, paramUsage, node->sort, node, err);

    if (paramUsage.size() != node->parameters.size()) {
        vector<string> unusedParams;
        std::vector<SymbolPtr>& params = node->parameters;
        for (const auto& param : params) {
            string pname = param->toString();
            if (paramUsage.find(pname) == paramUsage.end()) {
                unusedParams.push_back("'" + pname + "'");
            }
        }
        err = addError(ErrorMessages::buildSortDefUnusedSortParams(unusedParams), node, err);
    }
}

void SyntaxChecker::visit(const EchoCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->message.empty()) {
        err = addError(ErrorMessages::ERR_ECHO_EMPTY_STRING, node, err);
    }

}

void SyntaxChecker::visit(const ExitCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(const GetAssertsCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(const GetAssignsCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(const GetInfoCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->flag) {
        err = addError(ErrorMessages::ERR_GET_INFO_MISSING_FLAG, node, err);
    } else {
        visit0(node->flag);
    }
}

void SyntaxChecker::visit(const GetModelCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(const GetOptionCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->option) {
        err = addError(ErrorMessages::ERR_GET_OPT_MISSING_OPT, node, err);
    } else {
        visit0(node->option);
    }
}

void SyntaxChecker::visit(const GetProofCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(const GetUnsatAssumsCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(const GetUnsatCoreCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(const GetValueCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->terms.empty()) {
        err = addError(ErrorMessages::ERR_GET_VALUE_EMPTY_TERMS, node, err);
    } else {
        visit0(node->terms);
    }
}

void SyntaxChecker::visit(const PopCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->numeral) {
        err = addError(ErrorMessages::ERR_POP_MISSING_NUMERAL, node, err);
    } else {
        visit0(node->numeral);
    }
}

void SyntaxChecker::visit(const PushCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->numeral) {
        err = addError(ErrorMessages::ERR_PUSH_MISSING_NUMERAL, node, err);
    } else {
        visit0(node->numeral);
    }
}

void SyntaxChecker::visit(const ResetCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(const ResetAssertsCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(const SetInfoCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->info) {
        err = addError(ErrorMessages::ERR_SET_INFO_MISSING_INFO, node, err);
    } else {
        visit0(node->info);
    }
}

void SyntaxChecker::visit(const SetLogicCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->logic) {
        err = addError(ErrorMessages::ERR_SET_LOGIC_MISSING_LOGIC, node, err);
    }
}

void SyntaxChecker::visit(const SetOptionCommandPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->option) {
        err = addError(ErrorMessages::ERR_SET_OPT_MISSING_OPT, node, err);
    } else {
        AttributePtr option = node->option;
        if ((option->keyword->value == KW_DIAG_OUTPUT_CHANNEL
             || option->keyword->value == KW_REGULAR_OUTPUT_CHANNEL)
            && !dynamic_pointer_cast<StringLiteral>(option->value)) {
            err = addError(ErrorMessages::ERR_OPT_VALUE_STRING, option, err);
        } else if ((option->keyword->value == KW_RANDOM_SEED
                    || option->keyword->value == KW_VERBOSITY
                    || option->keyword->value == KW_REPROD_RESOURCE_LIMIT)
                   && !dynamic_pointer_cast<NumeralLiteral>(option->value)) {
            err = addError(ErrorMessages::ERR_OPT_VALUE_NUMERAL, option, err);
        } else if ((option->keyword->value == KW_EXPAND_DEFS
                    || option->keyword->value == KW_GLOBAL_DECLS
                    || option->keyword->value == KW_INTERACTIVE_MODE
                    || option->keyword->value == KW_PRINT_SUCCESS
                    || option->keyword->value == KW_PROD_ASSERTS
                    || option->keyword->value == KW_PROD_ASSIGNS
                    || option->keyword->value == KW_PROD_MODELS
                    || option->keyword->value == KW_PROD_PROOFS
                    || option->keyword->value == KW_PROD_UNSAT_ASSUMS
                    || option->keyword->value == KW_PROD_UNSAT_CORES)) {
            if (!option->value || (option->value->toString() != CONST_TRUE
                                        && option->value->toString() != CONST_FALSE)) {
                err = addError(ErrorMessages::ERR_OPT_VALUE_BOOLEAN, option, err);
            }
        }

        visit0(node->option);
    }
}

void SyntaxChecker::visit(const FunctionDeclarationPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_FUN_DECL_MISSING_NAME, node, err);
    } else {
        visit0(node->symbol);
    }

    visit0(node->parameters);

    if (!node->sort) {
        err = addError(ErrorMessages::ERR_FUN_DECL_MISSING_RET, node, err);
    } else {
        visit0(node->sort);
    }
}

void SyntaxChecker::visit(const FunctionDefinitionPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->signature) {
        err = addError(ErrorMessages::ERR_FUN_DEF_MISSING_SIG, node, err);
    } else {
        visit0(node->signature);
    }

    if (!node->body) {
        err = addError(ErrorMessages::ERR_FUN_DEF_MISSING_BODY, node, err);
    } else {
        visit0(node->body);
    }
}

void SyntaxChecker::visit(const SimpleIdentifierPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_ID_MISSING_SYMBOL, node, err);
    } else {
        visit0(node->symbol);
    }

    if (node->isIndexed() && node->indices.empty()) {
        err = addError(ErrorMessages::ERR_ID_EMPTY_INDICES, node, err);
    }

    visit0(node->indices);
}

void SyntaxChecker::visit(const QualifiedIdentifierPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->identifier) {
        err = addError(ErrorMessages::ERR_QUAL_ID_MISSING_ID, node, err);
    } else {
        visit0(node->identifier);
    }

    if (!node->sort) {
        err = addError(ErrorMessages::ERR_QUAL_ID_MISSING_SORT, node, err);
    } else {
        visit0(node->sort);
    }
}

void SyntaxChecker::visit(const DecimalLiteralPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(const NumeralLiteralPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(const StringLiteralPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(const LogicPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    std::vector<AttributePtr>& attrs = node->attributes;

    if (!node->name) {
        err = addError(ErrorMessages::ERR_LOGIC_MISSING_NAME, node, err);
    }

    if (attrs.empty()) {
        err = addError(ErrorMessages::ERR_LOGIC_EMPTY_ATTRS, node, err);
    }

    for (const auto& attr : attrs) {
        if (!attr)
            continue;

        ErrorPtr attrerr;

        if (attr->keyword->value == KW_LANGUAGE
            || attr->keyword->value == KW_EXTENSIONS
            || attr->keyword->value == KW_VALUES
            || attr->keyword->value == KW_NOTES) {
            if (!dynamic_pointer_cast<StringLiteral>(attr->value)) {
                attrerr = addError(ErrorMessages::ERR_ATTR_VALUE_STRING, attr, attrerr);
            }
        } else if (attr->keyword->value == KW_THEORIES) {
            if (!dynamic_pointer_cast<CompAttributeValue>(attr->value)) {
                err = addError(ErrorMessages::ERR_ATTR_VALUE_THEORIES, attr, err);
            } else {
                auto val = dynamic_pointer_cast<CompAttributeValue>(attr->value);
                std::vector<AttributeValuePtr>& values = val->values;

                // Note: standard prohibits empty theory list, but there are logics that only use Core
                /*if (values.empty()) {
                    err = addError(ErrorMessages::ERR_ATTR_VALUE_THEORIES_EMPTY, attr, err);
                }*/

                for (const auto& value : values) {
                    if (value && !dynamic_pointer_cast<Symbol>(value)) {
                        attrerr = addError(ErrorMessages::buildAttrValueSymbol(value->toString()), attr, attrerr);
                    }
                }
            }
        }

        visit0(attr);
    }
}

void SyntaxChecker::visit(const TheoryPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    std::vector<AttributePtr>& attrs = node->attributes;

    if (!node->name) {
        err = addError(ErrorMessages::ERR_THEORY_MISSING_NAME, node, err);
    }

    if (attrs.empty()) {
        err = addError(ErrorMessages::ERR_THEORY_EMPTY_ATTRS, node, err);
    }

    for (const auto& attr : attrs) {
        if (!attr)
            continue;

        ErrorPtr attrerr;

        if (attr->keyword->value == KW_SORTS_DESC
            || attr->keyword->value == KW_FUNS_DESC
            || attr->keyword->value == KW_DEFINITION
            || attr->keyword->value == KW_VALUES
            || attr->keyword->value == KW_NOTES) {
            if (!dynamic_pointer_cast<StringLiteral>(attr->value)) {
                attrerr = addError(ErrorMessages::ERR_ATTR_VALUE_STRING, attr, attrerr);
            }
        } else if (attr->keyword->value == KW_SORTS) {
            if (!dynamic_pointer_cast<CompAttributeValue>(attr->value)) {
                attrerr = addError(ErrorMessages::ERR_ATTR_VALUE_SORTS, attr, attrerr);
            } else {
                auto val = dynamic_pointer_cast<CompAttributeValue>(attr->value);
                std::vector<AttributeValuePtr>& values = val->values;

                if (values.empty()) {
                    attrerr = addError(ErrorMessages::ERR_ATTR_VALUE_SORTS_EMPTY, attr, attrerr);
                }

                for (const auto& value : values) {
                    if (value && !dynamic_pointer_cast<SortSymbolDeclaration>(value)) {
                        attrerr = addError(
                                ErrorMessages::buildAttrValueSortDecl(value->toString()), attr, attrerr);
                    }
                }
            }
        } else if (attr->keyword->value == KW_FUNS) {
            if (!dynamic_pointer_cast<CompAttributeValue>(attr->value)) {
                attrerr = addError(ErrorMessages::ERR_ATTR_VALUE_FUNS, attr, attrerr);
            } else {
                auto val = dynamic_pointer_cast<CompAttributeValue>(attr->value);
                std::vector<AttributeValuePtr>& values = val->values;

                if (values.empty()) {
                    attrerr = addError(ErrorMessages::ERR_ATTR_VALUE_FUNS_EMPTY, attr, attrerr);
                }

                for (const auto& value : values) {
                    if (value && !dynamic_pointer_cast<FunSymbolDeclaration>(value)) {
                        attrerr = addError(ErrorMessages::buildAttrValueFunDecl(value->toString()), attr, attrerr);
                    }
                }
            }
        }

        visit0(attr);
    }
}

void SyntaxChecker::visit(const ScriptPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    visit0(node->commands);
}

void SyntaxChecker::visit(const SortPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->identifier) {
        err = addError(ErrorMessages::ERR_SORT_MISSING_ID, node, err);
    } else {
        visit0(node->identifier);
    }

    if (node->hasArgs() && node->arguments.empty()) {
        err = addError(ErrorMessages::ERR_SORT_EMPTY_ARGS, node, err);
    } else {
        visit0(node->arguments);
    }
}

void SyntaxChecker::visit(const CompSExpressionPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    visit0(node->expressions);
}

void SyntaxChecker::visit(const SortSymbolDeclarationPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->identifier) {
        err = addError(ErrorMessages::ERR_SORT_SYM_DECL_MISSING_ID, node, err);
    } else {
        visit0(node->identifier);
    }

    if (!node->arity) {
        err = addError(ErrorMessages::ERR_SORT_SYM_DECL_MISSING_ARITY, node, err);
    } else {
        visit0(node->arity);
    }

    visit0(node->attributes);
}

void SyntaxChecker::visit(const SpecConstFunDeclarationPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->constant) {
        err = addError(ErrorMessages::ERR_SPEC_CONST_DECL_MISSING_CONST, node, err);
    } else {
        visit0(node->constant);
    }

    if (!node->sort) {
        err = addError(ErrorMessages::ERR_SPEC_CONST_DECL_MISSING_SORT, node, err);
    } else {
        visit0(node->sort);
    }

    visit0(node->attributes);
}

void SyntaxChecker::visit(const MetaSpecConstFunDeclarationPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->constant) {
        err = addError(ErrorMessages::ERR_META_SPEC_CONST_DECL_MISSING_CONST, node, err);
    } else {
        visit0(node->constant);
    }

    if (!node->sort) {
        err = addError(ErrorMessages::ERR_META_SPEC_CONST_DECL_MISSING_SORT, node, err);
    } else {
        visit0(node->sort);
    }

    visit0(node->attributes);
}

void SyntaxChecker::visit(const SimpleFunDeclarationPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->identifier) {
        err = addError(ErrorMessages::ERR_FUN_SYM_DECL_MISSING_ID, node, err);
    } else {
        visit0(node->identifier);
    }

    if (node->signature.empty()) {
        err = addError(ErrorMessages::ERR_FUN_SYM_DECL_EMPTY_SIG, node, err);
    } else {
        visit0(node->signature);
    }

    visit0(node->attributes);
}

void SyntaxChecker::visit(const ParametricFunDeclarationPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    // Check parameter list
    if (node->parameters.empty()) {
        err = addError(ErrorMessages::ERR_PARAM_FUN_SYM_DECL_EMPTY_PARAMS, node, err);
    } else {
        visit0(node->parameters);
    }

    // Check identifier
    if (!node->identifier) {
        err = addError(ErrorMessages::ERR_PARAM_FUN_SYM_DECL_MISSING_ID, node, err);
    } else {
        visit0(node->identifier);
    }

    // Check signature
    if (node->signature.empty()) {
        err = addError(ErrorMessages::ERR_PARAM_FUN_SYM_DECL_EMPTY_SIG, node, err);
    } else {
        visit0(node->signature);
    }

    // Check parameter usage
    unordered_map<string, bool> paramUsage;
    std::vector<SortPtr>& sig = node->signature;
    for (const auto& sort : sig) {
        err = checkParamUsage(node->parameters, paramUsage, sort, node, err);
    }

    if (paramUsage.size() != node->parameters.size()) {
        vector<string> unusedParams;
        std::vector<SymbolPtr>& params = node->parameters;
        for (const auto& param : params) {
            string pname = param->toString();
            if (paramUsage.find(pname) == paramUsage.end()) {
                unusedParams.push_back("'" + pname + "'");
            }
        }

        err = addError(ErrorMessages::buildParamFunDeclUnusedSortParams(unusedParams), node, err);
    }

    // Check attribute list
    visit0(node->attributes);
}

void SyntaxChecker::visit(const SortDeclarationPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_SORT_DECL_MISSING_SYMBOL, node, err);
    } else {
        visit0(node->symbol);
    }

    if (!node->arity) {
        err = addError(ErrorMessages::ERR_SORT_DECL_MISSING_ARITY, node, err);
    } else {
        visit0(node->arity);
    }
}

void SyntaxChecker::visit(const SelectorDeclarationPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_SEL_DECL_MISSING_SYMBOL, node, err);
    } else {
        visit0(node->symbol);
    }

    if (!node->sort) {
        err = addError(ErrorMessages::ERR_SEL_DECL_MISSING_SORT, node, err);
    } else {
        visit0(node->sort);
    }
}

void SyntaxChecker::visit(const ConstructorDeclarationPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_CONS_DECL_MISSING_SYMBOL, node, err);
    } else {
        visit0(node->symbol);
    }

    std::vector<SelectorDeclarationPtr>& selectors = node->selectors;
    for (const auto& sel : selectors) {
        visit0(sel);
    }
}

void SyntaxChecker::visit(const SimpleDatatypeDeclarationPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->constructors.empty()) {
        err = addError(ErrorMessages::ERR_DATATYPE_DECL_EMPTY_CONS, node, err);
    } else {
        visit0(node->constructors);
    }

}

void SyntaxChecker::visit(const ParametricDatatypeDeclarationPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->parameters.empty()) {
        err = addError(ErrorMessages::ERR_PARAM_DATATYPE_DECL_EMPTY_PARAMS, node, err);
    } else {
        visit0(node->parameters);
    }

    if (node->constructors.empty()) {
        err = addError(ErrorMessages::ERR_PARAM_DATATYPE_DECL_EMPTY_CONS, node, err);
    } else {
        visit0(node->constructors);
    }

    unordered_map<string, bool> paramUsage;

    std::vector<ConstructorDeclarationPtr>& constructors = node->constructors;
    for (const auto& cons : constructors) {
        std::vector<SelectorDeclarationPtr>& selectors = cons->selectors;
        for (const auto& sel : selectors) {
            err = checkParamUsage(node->parameters, paramUsage, sel->sort, node, err);
        }
    }

    if (paramUsage.size() != node->parameters.size()) {
        vector<string> unusedParams;
        std::vector<SymbolPtr>& params = node->parameters;
        for (const auto& param : params) {
            string pname = param->toString();
            if (paramUsage.find(pname) == paramUsage.end()) {
                unusedParams.push_back("'" + pname + "'");
            }
        }
        err = addError(ErrorMessages::buildParamDatatypeDeclUnusedSortParams(unusedParams), node, err);
    }
}

void SyntaxChecker::visit(const QualifiedConstructorPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_QUAL_CONS_MISSING_SYMBOL, node, err);
    } else {
        visit0(node->symbol);
    }

    if (!node->sort) {
        err = addError(ErrorMessages::ERR_QUAL_CONS_MISSING_SORT, node, err);
    } else {
        visit0(node->sort);
    }
}

void SyntaxChecker::visit(const QualifiedPatternPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->constructor) {
        err = addError(ErrorMessages::ERR_QUAL_PATTERN_MISSING_CONS, node, err);
    } else {
        visit0(node->constructor);
    }

    if (node->symbols.empty()) {
        err = addError(ErrorMessages::ERR_QUAL_PATTERN_EMPTY_SYMS, node, err);
    } else {
        visit0(node->symbols);
    }
}

void SyntaxChecker::visit(const MatchCasePtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->pattern) {
        err = addError(ErrorMessages::ERR_MATCH_CASE_MISSING_PATTERN, node, err);
    } else {
        visit0(node->pattern);
    }

    if (!node->term) {
        err = addError(ErrorMessages::ERR_MATCH_CASE_MISSING_TERM, node, err);
    } else {
        visit0(node->term);
    }
}

void SyntaxChecker::visit(const QualifiedTermPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->identifier) {
        err = addError(ErrorMessages::ERR_QUAL_TERM_MISSING_ID, node, err);
    } else {
        visit0(node->identifier);
    }

    if (node->terms.empty()) {
        err = addError(ErrorMessages::ERR_QUAL_TERM_EMPTY_TERMS, node, err);
    } else {
        visit0(node->terms);
    }
}

void SyntaxChecker::visit(const LetTermPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->bindings.empty()) {
        err = addError(ErrorMessages::ERR_LET_TERM_EMPTY_VARS, node, err);
    } else {
        std::vector<VariableBindingPtr>& bindings = node->bindings;
        for (const auto& bind : bindings) {
            visit0(bind);
        }
    }

    if (!node->term) {
        err = addError(ErrorMessages::ERR_LET_TERM_MISSING_TERM, node, err);
    } else {
        visit0(node->term);
    }
}

void SyntaxChecker::visit(const ForallTermPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->bindings.empty()) {
        err = addError(ErrorMessages::ERR_FORALL_TERM_EMPTY_VARS, node, err);
    } else {
        std::vector<SortedVariablePtr>& bindings = node->bindings;
        for (const auto& bind : bindings) {
            visit0(bind);
        }
    }

    if (!node->term) {
        err = addError(ErrorMessages::ERR_FORALL_TERM_MISSING_TERM, node, err);
    } else {
        visit0(node->term);
    }
}

void SyntaxChecker::visit(const ExistsTermPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->bindings.empty()) {
        err = addError(ErrorMessages::ERR_EXISTS_TERM_EMPTY_VARS, node, err);
    } else {
        std::vector<SortedVariablePtr>& bindings = node->bindings;
        for (const auto& binding : bindings) {
            visit0(binding);
        }
    }

    if (!node->term) {
        err = addError(ErrorMessages::ERR_EXISTS_TERM_MISSING_TERM, node, err);
    } else {
        visit0(node->term);
    }
}

void SyntaxChecker::visit(const MatchTermPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->term) {
        err = addError(ErrorMessages::ERR_MATCH_TERM_MISSING_TERM, node, err);
    } else {
        visit0(node->term);
    }

    if (node->cases.empty()) {
        err = addError(ErrorMessages::ERR_MATCH_TERM_EMPTY_CASES, node, err);
    } else {
        std::vector<MatchCasePtr>& cases = node->cases;
        for (const auto& caseIt : cases) {
            visit0(caseIt);
        }
    }
}

void SyntaxChecker::visit(const AnnotatedTermPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->term) {
        err = addError(ErrorMessages::ERR_ANNOT_TERM_MISSING_TERM, node, err);
    } else {
        visit0(node->term);
    }

    if (node->attributes.empty()) {
        err = addError(ErrorMessages::ERR_ANNOT_TERM_EMPTY_ATTRS, node, err);
    } else {
        visit0(node->attributes);
    }
}

void SyntaxChecker::visit(const SortedVariablePtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_SORTED_VAR_MISSING_SYMBOL, node, err);
    } else {
        visit0(node->symbol);
    }

    if (!node->sort) {
        err = addError(ErrorMessages::ERR_SORTED_VAR_MISSING_SORT, node, err);
    } else {
        visit0(node->sort);
    }
}

void SyntaxChecker::visit(const VariableBindingPtr& node) {
    ErrorPtr err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->symbol) {
        err = addError(ErrorMessages::ERR_VAR_BIND_MISSING_SYMBOL, node, err);
    } else {
        visit0(node->symbol);
    }

    if (!node->term) {
        err = addError(ErrorMessages::ERR_VAR_BIND_MISSING_SORT, node, err);
    } else {
        visit0(node->term);
    }
}

bool SyntaxChecker::check(const NodePtr& node) {
    visit0(node);
    return errors.empty();
}

string SyntaxChecker::getErrors() {
    stringstream ss;
    for (const auto& err : errors) {
        if (err->node) {
            ss << err->node->rowLeft << ":" << err->node->colLeft
            << " - " << err->node->rowRight << ":" << err->node->colRight << "   ";

            string nodestr = err->node->toString();
            if (nodestr.length() > 100)
                ss << string(nodestr, 0, 100) << "[...]";
            else
                ss << nodestr;
        } else {
            ss << "NULL";
        }

        ss << endl;
        for (const auto& msg : err->messages) {
            ss << "\t" << msg << "." << endl;
        }

        ss << endl;
    }

    return ss.str();
}
