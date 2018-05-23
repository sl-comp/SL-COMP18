/**
 * \file sep_term.h
 * \brief SMT-LIB+SEPLOG terms.
 */

#ifndef SLCOMP_PARSER_SEP_TERM_H
#define SLCOMP_PARSER_SEP_TERM_H

#include "sep_abstract.h"
#include "sep_attribute.h"
#include "sep_interfaces.h"
#include "sep_match.h"
#include "sep_variable.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace sep {
        /* ================================== QualifiedTerm =================================== */
        /** A list of terms preceded by a qualified identifier. */
        class QualifiedTerm : public Term,
                              public std::enable_shared_from_this<QualifiedTerm> {
        public:
            IdentifierPtr identifier;
            std::vector<TermPtr> terms;

            inline explicit QualifiedTerm(IdentifierPtr identifier)
                    : identifier(std::move(identifier)) {}

            /**
             * \param identifier    Qualified identifier
             * \param terms         List of terms
             */
            inline QualifiedTerm(IdentifierPtr identifier, std::vector<TermPtr> terms)
                    : identifier(std::move(identifier))
                    , terms(std::move(terms)) {}

            void accept(Visitor0* visitor) override;

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

            void accept(Visitor0* visitor) override;

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

            void accept(Visitor0* visitor) override;

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

            void accept(Visitor0* visitor) override;

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

            void accept(Visitor0* visitor) override;

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

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ===================================== TrueTerm ===================================== */
        /** A 'true' term */
        class TrueTerm : public Term,
                         public std::enable_shared_from_this<TrueTerm> {
        public:
            inline TrueTerm() = default;

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ==================================== FalseTerm ===================================== */
        /** A 'false' term */
        class FalseTerm : public Term,
                          public std::enable_shared_from_this<FalseTerm> {
        public:
            inline FalseTerm() = default;

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ===================================== NotTerm ====================================== */
        /** A negation term */
        class NotTerm : public Term,
                        public std::enable_shared_from_this<NotTerm> {
        public:
            TermPtr term;

            /**
             * @param term  Inner term
             */
            inline explicit NotTerm(TermPtr term)
                    : term(std::move(term)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =================================== ImpliesTerm ==================================== */
        /** An implication term */
        class ImpliesTerm : public Term,
                            public std::enable_shared_from_this<ImpliesTerm> {
        public:
            std::vector<TermPtr> terms;

            /**
             * @param terms Inner terms
             */
            inline explicit ImpliesTerm(std::vector<TermPtr> terms)
                    : terms(std::move(terms)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ===================================== AndTerm ====================================== */
        /** A conjunction term */
        class AndTerm : public Term,
                        public std::enable_shared_from_this<AndTerm> {
        public:
            std::vector<TermPtr> terms;

            /** Default constructor */
            inline AndTerm() = default;

            /**
             * @param terms Inner terms
             */
            inline explicit AndTerm(std::vector<TermPtr> terms)
                    : terms(std::move(terms)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ====================================== OrTerm ====================================== */
        /** A disjunction term */
        class OrTerm : public Term,
                       public std::enable_shared_from_this<OrTerm> {
        public:
            std::vector<TermPtr> terms;

            /**
             * @param terms Inner terms
             */
            inline explicit OrTerm(std::vector<TermPtr> terms)
                    : terms(std::move(terms)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;

        };

        /* ===================================== XorTerm ====================================== */
        /** An exclusive disjunction term */
        class XorTerm : public Term,
                        public std::enable_shared_from_this<XorTerm> {
        public:
            std::vector<TermPtr> terms;

            /**
             * @param terms Inner terms
             */
            inline explicit XorTerm(std::vector<TermPtr> terms)
                    : terms(std::move(terms)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ==================================== EqualsTerm ==================================== */
        /** An '=' term */
        class EqualsTerm : public Term,
                           public std::enable_shared_from_this<EqualsTerm> {
        public:
            std::vector<TermPtr> terms;

            /**
             * @param terms Inner terms
             */
            inline explicit EqualsTerm(std::vector<TermPtr> terms)
                    : terms(std::move(terms)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =================================== DistinctTerm =================================== */
        /** A 'distinct' term */
        class DistinctTerm : public Term,
                             public std::enable_shared_from_this<DistinctTerm> {
        public:
            std::vector<TermPtr> terms;

            /**
             * @param terms Inner terms
             */
            inline explicit DistinctTerm(std::vector<TermPtr> terms)
                    : terms(std::move(terms)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ===================================== IteTerm ====================================== */
        /** An 'if-then-else' term */
        class IteTerm : public Term,
                        public std::enable_shared_from_this<IteTerm> {
        public:
            TermPtr testTerm;
            TermPtr thenTerm;
            TermPtr elseTerm;

            /**
             * @param testTerm  Test condition
             * @param thenTerm  Term for 'then' branch
             * @param elseTerm  Term for 'else' branch
             */
            inline IteTerm(TermPtr testTerm, TermPtr thenTerm, TermPtr elseTerm)
                    : testTerm(std::move(testTerm))
                    , thenTerm(std::move(thenTerm))
                    , elseTerm(std::move(elseTerm)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ===================================== EmpTerm ====================================== */
        /** An 'emp' term */
        class EmpTerm : public Term,
                        public std::enable_shared_from_this<EmpTerm> {
        public:
            SortPtr locSort;
            SortPtr dataSort;

            inline EmpTerm(SortPtr locSort, SortPtr dataSort)
                    : locSort(std::move(locSort))
                    , dataSort(std::move(dataSort)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ===================================== SepTerm ====================================== */
        /** A separating conjunction term */
        class SepTerm : public Term,
                        public std::enable_shared_from_this<SepTerm> {
        public:
            std::vector<TermPtr> terms;

            /** Default constructor */
            inline SepTerm() = default;

            /**
             * @param terms Inner terms
             */
            inline explicit SepTerm(std::vector<TermPtr> terms)
                    : terms(std::move(terms)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ===================================== WandTerm ===================================== */
        /** A magic wand term */
        class WandTerm : public Term,
                         public std::enable_shared_from_this<WandTerm> {
        public:
            std::vector<TermPtr> terms;

            explicit WandTerm(std::vector<TermPtr> terms)
                    : terms(std::move(terms)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ===================================== PtoTerm ====================================== */
        /** A 'points-to' term */
        class PtoTerm : public Term,
                        public std::enable_shared_from_this<PtoTerm> {
        public:
            TermPtr leftTerm;
            TermPtr rightTerm;

            /**
             * @param leftTerm      Left-hand side of the 'points-to'
             * @param rightTerm     Right-hand side of the 'points-to'
             */
            inline PtoTerm(TermPtr leftTerm, TermPtr rightTerm)
                    : leftTerm(std::move(leftTerm))
                    , rightTerm(std::move(rightTerm)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ===================================== NilTerm ====================================== */
        /** A 'nil' term */
        class NilTerm : public Term,
                        public std::enable_shared_from_this<NilTerm> {
        public:
            SortPtr sort;

            /** Default constructor */
            inline NilTerm() = default;

            /**
             * @param sort  Sort of the 'nil' predicate
             */
            inline explicit NilTerm(SortPtr sort)
                    : sort(std::move(sort)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //SLCOMP_PARSER_SEP_TERM_H
