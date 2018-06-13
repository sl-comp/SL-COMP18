/**
 * \file sep_visitor.h
 * \brief Abstract visitor classes the smtlib::sep hierarchy.
 */

#ifndef SLCOMP_PARSER_SEP_VISITOR_H
#define SLCOMP_PARSER_SEP_VISITOR_H

#include "sep/sep_abstract.h"
#include "sep/sep_classes.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace sep {
        /* ===================================== Visitor0 ===================================== */
        /** A visitor for the smtlib::sep hierarchy */
        class Visitor0 {
        protected:
            virtual void visit0(const NodePtr& node);
            template<class T>
            void visit0(std::vector<std::shared_ptr<T>>& arr) {
                for (const auto& item : arr) {
                    visit0(item);
                }
            }

            template<class T1, class T2>
            void visit0(const std::vector<std::pair<std::shared_ptr<T1>, std::shared_ptr<T2>>>& arr) {
                for (const auto pair : arr) {
                    visit0(pair.first);
                    visit0(pair.second);
                }
            }
        public:
            virtual void visit(const SimpleAttributePtr& node) = 0;
            virtual void visit(const SExpressionAttributePtr& node) = 0;
            virtual void visit(const SymbolAttributePtr& node) = 0;
            virtual void visit(const BooleanAttributePtr& node) = 0;
            virtual void visit(const NumeralAttributePtr& node) = 0;
            virtual void visit(const DecimalAttributePtr& node) = 0;
            virtual void visit(const StringAttributePtr& node) = 0;
            virtual void visit(const TheoriesAttributePtr& node) = 0;
            virtual void visit(const SortsAttributePtr& node) = 0;
            virtual void visit(const FunsAttributePtr& node) = 0;

            virtual void visit(const SymbolPtr& node) = 0;
            virtual void visit(const KeywordPtr& node) = 0;
            virtual void visit(const MetaSpecConstantPtr& node) = 0;
            virtual void visit(const BooleanValuePtr& node) = 0;
            virtual void visit(const PropLiteralPtr& node) = 0;

            virtual void visit(const AssertCommandPtr& node) = 0;
            virtual void visit(const CheckSatCommandPtr& node) = 0;
            virtual void visit(const CheckSatAssumCommandPtr& node) = 0;
            virtual void visit(const DeclareConstCommandPtr& node) = 0;
            virtual void visit(const DeclareDatatypeCommandPtr& node) = 0;
            virtual void visit(const DeclareDatatypesCommandPtr& node) = 0;
            virtual void visit(const DeclareFunCommandPtr& node) = 0;
            virtual void visit(const DeclareSortCommandPtr& node) = 0;
            virtual void visit(const DeclareHeapCommandPtr& node) = 0;
            virtual void visit(const DefineFunCommandPtr& node) = 0;
            virtual void visit(const DefineFunRecCommandPtr& node) = 0;
            virtual void visit(const DefineFunsRecCommandPtr& node) = 0;
            virtual void visit(const DefineSortCommandPtr& node) = 0;
            virtual void visit(const EchoCommandPtr& node) = 0;
            virtual void visit(const ExitCommandPtr& node) = 0;
            virtual void visit(const GetAssertsCommandPtr& node) = 0;
            virtual void visit(const GetAssignsCommandPtr& node) = 0;
            virtual void visit(const GetInfoCommandPtr& node) = 0;
            virtual void visit(const GetModelCommandPtr& node) = 0;
            virtual void visit(const GetOptionCommandPtr& node) = 0;
            virtual void visit(const GetProofCommandPtr& node) = 0;
            virtual void visit(const GetUnsatAssumsCommandPtr& node) = 0;
            virtual void visit(const GetUnsatCoreCommandPtr& node) = 0;
            virtual void visit(const GetValueCommandPtr& node) = 0;
            virtual void visit(const PopCommandPtr& node) = 0;
            virtual void visit(const PushCommandPtr& node) = 0;
            virtual void visit(const ResetCommandPtr& node) = 0;
            virtual void visit(const ResetAssertsCommandPtr& node) = 0;
            virtual void visit(const SetInfoCommandPtr& node) = 0;
            virtual void visit(const SetLogicCommandPtr& node) = 0;
            virtual void visit(const SetOptionCommandPtr& node) = 0;

            virtual void visit(const SortDeclarationPtr& node) = 0;
            virtual void visit(const SelectorDeclarationPtr& node) = 0;
            virtual void visit(const ConstructorDeclarationPtr& node) = 0;
            virtual void visit(const SimpleDatatypeDeclarationPtr& node) = 0;
            virtual void visit(const ParametricDatatypeDeclarationPtr& node) = 0;

            virtual void visit(const FunctionDeclarationPtr& node) = 0;
            virtual void visit(const FunctionDefinitionPtr& node) = 0;

            virtual void visit(const SimpleIdentifierPtr& node) = 0;
            virtual void visit(const QualifiedIdentifierPtr& node) = 0;

            virtual void visit(const NumeralLiteralPtr& node) = 0;
            virtual void visit(const DecimalLiteralPtr& node) = 0;
            virtual void visit(const StringLiteralPtr& node) = 0;

            virtual void visit(const LogicPtr& node) = 0;
            virtual void visit(const TheoryPtr& node) = 0;
            virtual void visit(const ScriptPtr& node) = 0;

            virtual void visit(const QualifiedConstructorPtr& node) = 0;
            virtual void visit(const QualifiedPatternPtr& node) = 0;
            virtual void visit(const MatchCasePtr& node) = 0;

            virtual void visit(const CompSExpressionPtr& node) = 0;

            virtual void visit(const SortPtr& node) = 0;

            virtual void visit(const SortSymbolDeclarationPtr& node) = 0;
            virtual void visit(const SpecConstFunDeclarationPtr& node) = 0;
            virtual void visit(const MetaSpecConstFunDeclarationPtr& node) = 0;
            virtual void visit(const SimpleFunDeclarationPtr& node) = 0;
            virtual void visit(const ParametricFunDeclarationPtr& node) = 0;

            virtual void visit(const QualifiedTermPtr& node) = 0;
            virtual void visit(const LetTermPtr& node) = 0;
            virtual void visit(const ForallTermPtr& node) = 0;
            virtual void visit(const ExistsTermPtr& node) = 0;
            virtual void visit(const MatchTermPtr& node) = 0;
            virtual void visit(const AnnotatedTermPtr& node) = 0;

            virtual void visit(const TrueTermPtr& node) = 0;
            virtual void visit(const FalseTermPtr& node) = 0;
            virtual void visit(const NotTermPtr& node) = 0;
            virtual void visit(const ImpliesTermPtr& node) = 0;
            virtual void visit(const AndTermPtr& node) = 0;
            virtual void visit(const OrTermPtr& node) = 0;
            virtual void visit(const XorTermPtr& node) = 0;
            virtual void visit(const EqualsTermPtr& node) = 0;
            virtual void visit(const DistinctTermPtr& node) = 0;
            virtual void visit(const IteTermPtr& node) = 0;

            virtual void visit(const EmpTermPtr& node) = 0;
            virtual void visit(const SepTermPtr& node) = 0;
            virtual void visit(const WandTermPtr& node) = 0;
            virtual void visit(const PtoTermPtr& node) = 0;
            virtual void visit(const NilTermPtr& node) = 0;

            virtual void visit(const SortedVariablePtr& node) = 0;
            virtual void visit(const VariableBindingPtr& node) = 0;
        };

        /* ================================== DummyVisitor0 =================================== */
        /** A dummy (empty) implementation of Visitor0 */
        class DummyVisitor0 : public virtual Visitor0 {
        public:
            void visit(const SimpleAttributePtr& node) override;
            void visit(const SExpressionAttributePtr& node) override;
            void visit(const SymbolAttributePtr& node) override;
            void visit(const BooleanAttributePtr& node) override;
            void visit(const NumeralAttributePtr& node) override;
            void visit(const DecimalAttributePtr& node) override;
            void visit(const StringAttributePtr& node) override;
            void visit(const TheoriesAttributePtr& node) override;
            void visit(const SortsAttributePtr& node) override;
            void visit(const FunsAttributePtr& node) override;

            void visit(const SymbolPtr& node) override;
            void visit(const KeywordPtr& node) override;
            void visit(const MetaSpecConstantPtr& node) override;
            void visit(const BooleanValuePtr& node) override;
            void visit(const PropLiteralPtr& node) override;

            void visit(const AssertCommandPtr& node) override;
            void visit(const CheckSatCommandPtr& node) override;
            void visit(const CheckSatAssumCommandPtr& node) override;
            void visit(const DeclareConstCommandPtr& node) override;
            void visit(const DeclareDatatypeCommandPtr& node) override;
            void visit(const DeclareDatatypesCommandPtr& node) override;
            void visit(const DeclareFunCommandPtr& node) override;
            void visit(const DeclareSortCommandPtr& node) override;
            void visit(const DeclareHeapCommandPtr& node) override;
            void visit(const DefineFunCommandPtr& node) override;
            void visit(const DefineFunRecCommandPtr& node) override;
            void visit(const DefineFunsRecCommandPtr& node) override;
            void visit(const DefineSortCommandPtr& node) override;
            void visit(const EchoCommandPtr& node) override;
            void visit(const ExitCommandPtr& node) override;
            void visit(const GetAssertsCommandPtr& node) override;
            void visit(const GetAssignsCommandPtr& node) override;
            void visit(const GetInfoCommandPtr& node) override;
            void visit(const GetModelCommandPtr& node) override;
            void visit(const GetOptionCommandPtr& node) override;
            void visit(const GetProofCommandPtr& node) override;
            void visit(const GetUnsatAssumsCommandPtr& node) override;
            void visit(const GetUnsatCoreCommandPtr& node) override;
            void visit(const GetValueCommandPtr& node) override;
            void visit(const PopCommandPtr& node) override;
            void visit(const PushCommandPtr& node) override;
            void visit(const ResetCommandPtr& node) override;
            void visit(const ResetAssertsCommandPtr& node) override;
            void visit(const SetInfoCommandPtr& node) override;
            void visit(const SetLogicCommandPtr& node) override;
            void visit(const SetOptionCommandPtr& node) override;

            void visit(const SortDeclarationPtr& node) override;
            void visit(const SelectorDeclarationPtr& node) override;
            void visit(const ConstructorDeclarationPtr& node) override;
            void visit(const SimpleDatatypeDeclarationPtr& node) override;
            void visit(const ParametricDatatypeDeclarationPtr& node) override;

            void visit(const FunctionDeclarationPtr& node) override;
            void visit(const FunctionDefinitionPtr& node) override;

            void visit(const SimpleIdentifierPtr& node) override;
            void visit(const QualifiedIdentifierPtr& node) override;

            void visit(const NumeralLiteralPtr& node) override;
            void visit(const DecimalLiteralPtr& node) override;
            void visit(const StringLiteralPtr& node) override;

            void visit(const LogicPtr& node) override;
            void visit(const TheoryPtr& node) override;
            void visit(const ScriptPtr& node) override;

            void visit(const QualifiedConstructorPtr& node) override;
            void visit(const QualifiedPatternPtr& node) override;
            void visit(const MatchCasePtr& node) override;

            void visit(const CompSExpressionPtr& node) override;

            void visit(const SortPtr& node) override;

            void visit(const SortSymbolDeclarationPtr& node) override;
            void visit(const SpecConstFunDeclarationPtr& node) override;
            void visit(const MetaSpecConstFunDeclarationPtr& node) override;
            void visit(const SimpleFunDeclarationPtr& node) override;
            void visit(const ParametricFunDeclarationPtr& node) override;

            void visit(const QualifiedTermPtr& node) override;
            void visit(const LetTermPtr& node) override;
            void visit(const ForallTermPtr& node) override;
            void visit(const ExistsTermPtr& node) override;
            void visit(const MatchTermPtr& node) override;
            void visit(const AnnotatedTermPtr& node) override;

            void visit(const TrueTermPtr& node) override;
            void visit(const FalseTermPtr& node) override;
            void visit(const NotTermPtr& node) override;
            void visit(const ImpliesTermPtr& node) override;
            void visit(const AndTermPtr& node) override;
            void visit(const OrTermPtr& node) override;
            void visit(const XorTermPtr& node) override;
            void visit(const EqualsTermPtr& node) override;
            void visit(const DistinctTermPtr& node) override;
            void visit(const IteTermPtr& node) override;

            void visit(const EmpTermPtr& node) override;
            void visit(const SepTermPtr& node) override;
            void visit(const WandTermPtr& node) override;
            void visit(const PtoTermPtr& node) override;
            void visit(const NilTermPtr& node) override;

            void visit(const SortedVariablePtr& node) override;
            void visit(const VariableBindingPtr& node) override;
        };
    }
}

#endif //SLCOMP_PARSER_SEP_VISITOR_H
