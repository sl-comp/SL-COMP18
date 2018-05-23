/**
 * \file sep_match.h
 * \brief Data structures for match terms.
 */

#ifndef SLCOMP_PARSER_SEP_MATCH_H
#define SLCOMP_PARSER_SEP_MATCH_H

#include "sep_abstract.h"
#include "sep_sort.h"

#include <vector>

namespace smtlib {
    namespace sep {
        /* =============================== QualifiedConstructor =============================== */
        /** A qualified constructor for match terms */
        class QualifiedConstructor : public Constructor,
                                     public std::enable_shared_from_this<QualifiedConstructor> {
        public:
            std::string name;
            SortPtr sort;

            inline QualifiedConstructor(std::string name, SortPtr sort)
                    : name(std::move(name))
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
            std::vector<std::string> arguments;

            inline QualifiedPattern(ConstructorPtr constructor,
                                    std::vector<std::string> args)
                    : constructor(std::move(constructor))
                    , arguments(std::move(args)) {}

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

#endif //SLCOMP_PARSER_SEP_MATCH_H
