/**
 * \file ast_identif.h
 * \brief SMT-LIB identifiers.
 */

#ifndef SLCOMP_PARSER_AST_IDENTIFIER_H
#define SLCOMP_PARSER_AST_IDENTIFIER_H

#include "ast_abstract.h"
#include "ast_basic.h"
#include "ast_interfaces.h"
#include "ast_sort.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        class Sort;

        /* ==================================== SimpleIdentifier ==================================== */
        /** Simple identifier (e.g. "Real", "|John Brown|", "_ BitVec 32"). */
        class SimpleIdentifier : public Identifier,
                                 public std::enable_shared_from_this<SimpleIdentifier> {
        public:
            SymbolPtr symbol;
            std::vector<IndexPtr> indices;

            /**
             * Constuctor for unindexed identifier.
             * \param symbol    Identifier symbol
             */
            inline explicit SimpleIdentifier(SymbolPtr symbol)
                    : symbol(std::move(symbol)) {}

            /**
             * Constuctor for indexed identifier.
             * \param symbol    Identifier symbol
             * \param indices   Identifier indices
             */
            inline SimpleIdentifier(SymbolPtr symbol, std::vector<IndexPtr> indices)
                    : symbol(std::move(symbol))
                    , indices(std::move(indices)) {}

            /**
             * Checks whether the identifier is indexed (i.e. the list of indices is not empty).
             */
            bool isIndexed();

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =============================== QualifiedIdentifier ================================ */
        /** Qualified identifier (e.g. "(as f Sigma)"). */
        class QualifiedIdentifier : public Identifier,
                                    public std::enable_shared_from_this<QualifiedIdentifier> {
        public:
            SimpleIdentifierPtr identifier;
            SortPtr sort;

            /**
             * \param identifier    SimpleIdentifier
             * \param sort          Result sort
             */
            inline QualifiedIdentifier(SimpleIdentifierPtr identifier, SortPtr sort)
                    : identifier(std::move(identifier))
                    , sort(std::move(sort)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //SLCOMP_PARSER_AST_IDENTIFIER_H
