/**
 * \file ast_term.h
 * \brief SMT-LIB terms.
 */

#ifndef SLCOMP_PARSER_AST_TERM_H
#define SLCOMP_PARSER_AST_TERM_H

#include "ast_abstract.h"
#include "ast_attribute.h"
#include "ast_interfaces.h"
#include "ast_match.h"
#include "ast_variable.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        /* ================================== QualifiedTerm =================================== */
        /** A list of terms preceded by a qualified identifier. */
        class QualifiedTerm : public Term,
                              public std::enable_shared_from_this<QualifiedTerm> {
        public:
            IdentifierPtr identifier;
            std::vector<TermPtr> terms;

            /**
             * \param identifier    Qualified identifier
             * \param terms         List of terms
             */
            inline QualifiedTerm(IdentifierPtr identifier, std::vector<TermPtr> terms)
                    : identifier(std::move(identifier))
                    , terms(std::move(terms)) {}

            void accept(Visitor0 *visitor) override;

            std::string toString() override;
        };

        /* ===================================== LetTerm ====================================== */
        /** A term preceded by a 'let' binder. */
        class LetTerm : public Term,
                        public std::enable_shared_from_this<LetTerm> {
        public:
            std::vector<VariableBindingPtr> bindings;
            TermPtr term;

            /**
             * \param bindings  List of bound variables
             * \param term      Inner term
             */
            inline LetTerm(std::vector<VariableBindingPtr> bindings, TermPtr term)
                    : bindings(std::move(bindings))
                    , term(std::move(term)) {}

            void accept(Visitor0 *visitor) override;

            std::string toString() override;
        };

        /* ==================================== ForallTerm ==================================== */
        /** A term preceded by a 'forall' binder. */
        class ForallTerm : public Term,
                           public std::enable_shared_from_this<ForallTerm> {
        public:
            std::vector<SortedVariablePtr> bindings;
            TermPtr term;

            /**
             * \param bindings  List of bound variables
             * \param term      Inner term
             */
            inline ForallTerm(std::vector<SortedVariablePtr> bindings, TermPtr term)
                    : bindings(std::move(bindings))
                    , term(std::move(term)) {}

            void accept(Visitor0 *visitor) override;

            std::string toString() override;
        };

        /* ==================================== ExistsTerm ==================================== */
        /** A term preceded by an 'exists' binder. */
        class ExistsTerm : public Term,
                           public std::enable_shared_from_this<ExistsTerm> {
        public:
            std::vector<SortedVariablePtr> bindings;
            TermPtr term;

            /**
             * \param bindings  List of bound variables
             * \param term      Inner term
             */
            inline ExistsTerm(std::vector<SortedVariablePtr> bindings, TermPtr term)
                    : bindings(std::move(bindings))
                    , term(std::move(term)) {}

            void accept(Visitor0 *visitor) override;

            std::string toString() override;
        };

        /* ==================================== MatchTerm ===================================== */
        /** A 'match' term */
        class MatchTerm : public Term,
                          public std::enable_shared_from_this<MatchTerm> {
        public:
            TermPtr term;
            std::vector<MatchCasePtr> cases;

            /**
             * @param term      Term to be matched
             * @param cases     Match cases
             */
            inline MatchTerm(TermPtr term, std::vector<MatchCasePtr> cases)
                    : term(std::move(term))
                    , cases(std::move(cases)) {}

            void accept(Visitor0 *visitor) override;

            std::string toString() override;
        };

        /* ================================== AnnotatedTerm =================================== */
        /** An annotated term. */
        class AnnotatedTerm : public Term,
                              public std::enable_shared_from_this<AnnotatedTerm> {
        public:
            TermPtr term;
            std::vector<AttributePtr> attributes;

            /**
             * \param term  Inner term
             * \param attr  Attributes
             */
            inline AnnotatedTerm(TermPtr term, std::vector<AttributePtr> attributes)
                    : term(std::move(term))
                    , attributes(std::move(attributes)) {}

            void accept(Visitor0 *visitor) override;

            std::string toString() override;
        };
    }
}

#endif //SLCOMP_PARSER_AST_TERM_H
