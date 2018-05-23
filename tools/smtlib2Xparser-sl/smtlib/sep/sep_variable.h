/**
 * \file ast_variable.h
 * \brief SMT-LIB sorted variable and variable binding.
 */

#ifndef SLCOMP_PARSER_SEP_VAR_H
#define SLCOMP_PARSER_SEP_VAR_H

#include "sep_abstract.h"
#include "sep_basic.h"
#include "sep_interfaces.h"
#include "sep_sort.h"

#include <memory>

namespace smtlib {
    namespace sep {
        /* ================================== SortedVariable ================================== */
        /** A sorted variable. */
        class SortedVariable : public Node,
                               public std::enable_shared_from_this<SortedVariable> {
        public:
            std::string name;
            SortPtr sort;

            /**
             * \param name      Variable name
             * \param sort      Variable sort
             */
            inline SortedVariable(std::string name, SortPtr sort)
                    : name(std::move(name))
                    , sort(std::move(sort)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ==================================== VariableBinding ==================================== */
        /** A variable binding. */
        class VariableBinding : public Node,
                                public std::enable_shared_from_this<VariableBinding> {
        public:
            std::string name;
            TermPtr term;

            /**
             * \param name      Variable name
             * \param term      Binding
             */
            inline VariableBinding(std::string name, TermPtr term)
                    : name(std::move(name))
                    , term(std::move(term)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //SLCOMP_PARSER_SEP_VAR_H
