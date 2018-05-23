/**
 * \file ast_fun.h
 * \brief Function declaration and definition.
 */

#ifndef SLCOMP_PARSER_AST_FUN_H
#define SLCOMP_PARSER_AST_FUN_H

#include "ast_abstract.h"
#include "ast_basic.h"
#include "ast_interfaces.h"
#include "ast_sort.h"
#include "ast_variable.h"

#include "visitor/ast_visitor.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        /* =============================== FunctionDeclaration ================================ */
        /** A function declaration. */
        class FunctionDeclaration : public Node,
                                    public std::enable_shared_from_this<FunctionDeclaration> {
        public:
            SymbolPtr symbol;
            std::vector<SortedVariablePtr> parameters;
            SortPtr sort;

            /**
             * \param symbol        Name of the function
             * \param parameters    List of parameters
             * \param sort          Sort of the return value
             */
            inline FunctionDeclaration(SymbolPtr symbol,
                                       std::vector<SortedVariablePtr> parameters,
                                       SortPtr sort)
                    : symbol(std::move(symbol))
                    , sort(std::move(sort))
                    , parameters(std::move(parameters)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================ FunctionDefinition ================================ */
        /** A function definition. */
        class FunctionDefinition : public Node,
                                   public std::enable_shared_from_this<FunctionDefinition> {
        public:
            FunctionDeclarationPtr signature;
            TermPtr body;

            /**
             * \param signature    Function signature
             * \param body         Function body
             */
            inline FunctionDefinition(FunctionDeclarationPtr signature, TermPtr body)
                    : signature(std::move(signature))
                    , body(std::move(body)) {}

            /**
             * \param symbol        Name of the function
             * \param parameters    List of parameters
             * \param type          Sort of the return value
             * \param body          Function body
             */
            inline FunctionDefinition(SymbolPtr symbol,
                                      std::vector<SortedVariablePtr> parameters,
                                      SortPtr sort,
                                      TermPtr body)
                    : body(std::move(body))
                    , signature(std::make_shared<FunctionDeclaration>(std::move(symbol),
                                                                      std::move(parameters),
                                                                      std::move(sort))) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //SLCOMP_PARSER_AST_FUN_H
