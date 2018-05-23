/**
 * \file ast_variable.h
 * \brief SMT-LIB sorted variable and variable binding.
 */

#ifndef SLCOMP_PARSER_AST_VAR_H
#define SLCOMP_PARSER_AST_VAR_H

#include "ast_abstract.h"
#include "ast_basic.h"
#include "ast_interfaces.h"
#include "ast_sort.h"

#include <memory>

namespace smtlib {
    namespace ast {
        /* ================================== SortedVariable ================================== */
        /** A sorted variable. */
        struct SortedVariable : public Node,
                                public std::enable_shared_from_this<SortedVariable> {
            SymbolPtr symbol;
            SortPtr sort;

            /**
             * \param symbol    Variable name
             * \param sort      Variable sort
             */
            inline SortedVariable(SymbolPtr symbol, SortPtr sort)
                    : symbol(std::move(symbol))
                    , sort(std::move(sort)) {}

            void accept(Visitor0 *visitor) override;

            std::string toString() override;
        };

        /* ================================= VariableBinding ================================== */
        /** A variable binding. */
        struct VariableBinding : public Node,
                                 public std::enable_shared_from_this<VariableBinding> {
            SymbolPtr symbol;
            TermPtr term;

            /**
             * \param symbol    Variable name
             * \param term      Binding
             */
            VariableBinding(SymbolPtr symbol, TermPtr term)
                    : symbol(std::move(symbol))
                    , term(std::move(term)) {}

            void accept(Visitor0 *visitor) override;

            std::string toString() override;
        };
    }
}

#endif //SLCOMP_PARSER_AST_VAR_H
