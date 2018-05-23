/**
 * \file ast_sort.h
 * \brief SMT-LIB sort.
 */

#ifndef SLCOMP_PARSER_AST_SORT_H
#define SLCOMP_PARSER_AST_SORT_H

#include "ast_abstract.h"
#include "ast_basic.h"
#include "ast_identifier.h"
#include "ast_interfaces.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        /** An SMT-LIB sort. */
        class Sort : public Index,
                     public std::enable_shared_from_this<Sort> {
        public:
            SimpleIdentifierPtr identifier;
            std::vector<SortPtr> arguments;

            /**
             * Constructor for a simple sort
             * \param identifier    Sort name
             */
            inline explicit Sort(SimpleIdentifierPtr identifier)
                    : identifier(std::move(identifier)) {}

            /**
             * Constructor for a sort with arguments
             * \param identifier    Sort name
             * \param arguments     Sort arguments
             */
            inline Sort(SimpleIdentifierPtr identifier, std::vector<SortPtr> arguments)
                    : identifier(std::move(identifier))
                    , arguments(std::move(arguments)) {}

            /** Checks whether the sort has arguments */
            bool hasArgs();

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //SLCOMP_PARSER_AST_SORT_H
