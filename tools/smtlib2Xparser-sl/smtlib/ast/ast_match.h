/**
 * \file ast_match.h
 * \brief Data structures for match terms.
 */

#ifndef SLCOMP_PARSER_AST_MATCH_H
#define SLCOMP_PARSER_AST_MATCH_H

#include "ast_abstract.h"
#include "ast_basic.h"
#include "ast_interfaces.h"

#include <vector>

namespace smtlib {
    namespace ast {
        /* =============================== QualifiedConstructor =============================== */
        /** A qualified constructor for match terms */
        class QualifiedConstructor : public Constructor,
                                     public std::enable_shared_from_this<QualifiedConstructor> {
        public:
            SymbolPtr symbol;
            SortPtr sort;

            inline QualifiedConstructor(SymbolPtr symbol, SortPtr sort)
                    : symbol(std::move(symbol))
                    , sort(std::move(sort)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================= QualifiedPattern ================================= */
        /** A qualified pattern for match terms */
        class QualifiedPattern : public Pattern,
                                 public std::enable_shared_from_this<QualifiedPattern> {
        public:
            ConstructorPtr constructor;
            std::vector<SymbolPtr> symbols;

            inline QualifiedPattern(ConstructorPtr constructor, std::vector<SymbolPtr> symbols)
                    : constructor(std::move(constructor))
                    , symbols(std::move(symbols)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ===================================== MatchCase ==================================== */
        /** A match case for match terms */
        class MatchCase : public Node,
                          public std::enable_shared_from_this<MatchCase> {
        public:
            PatternPtr pattern;
            TermPtr term;

            inline MatchCase(PatternPtr pattern, TermPtr term)
                    : pattern(std::move(pattern))
                    , term(std::move(term)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //SLCOMP_PARSER_AST_MATCH_H
