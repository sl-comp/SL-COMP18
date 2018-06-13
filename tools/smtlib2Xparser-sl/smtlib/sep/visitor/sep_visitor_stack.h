#ifndef SLCOMP_PARSER_SEP_VISITOR_STACK_H
#define SLCOMP_PARSER_SEP_VISITOR_STACK_H

#include "sep_term_sorter.h"
#include "sep_visitor.h"
#include "sep_visitor_extra.h"

#include "stack/sep_symbol_stack.h"
#include "util/configuration.h"

namespace smtlib {
    namespace sep {
        /* ================================ VisitorWithStack0 ================================= */
        /**
         * A visitor for the smtlib::sep hierarchy, equipped with a symbol stack.
         * The regular `visit()` methods build the stack and are final.
         * When inheriting, add functionality by overriding the `visitWithStack()` methods.
         */
        class VisitorWithStack0 : public virtual Visitor0 {
        protected:
            SymbolStackPtr stack;
            std::vector<std::string> currentTheories;
            std::string currentLogic;
            ConfigurationPtr config;

            SortEntryPtr buildEntry(const SortSymbolDeclarationPtr& node);
            SortEntryPtr buildEntry(const DeclareSortCommandPtr& node);
            SortEntryPtr buildEntry(const DefineSortCommandPtr& node);

            FunEntryPtr buildEntry(const SpecConstFunDeclarationPtr& node);
            FunEntryPtr buildEntry(const MetaSpecConstFunDeclarationPtr& node);
            FunEntryPtr buildEntry(const SimpleFunDeclarationPtr& node);
            FunEntryPtr buildEntry(const ParametricFunDeclarationPtr& node);

            FunEntryPtr buildEntry(const DeclareConstCommandPtr& node);
            FunEntryPtr buildEntry(const DeclareFunCommandPtr& node);
            FunEntryPtr buildEntry(const DefineFunCommandPtr& node);
            FunEntryPtr buildEntry(const DefineFunRecCommandPtr& node);

            std::vector<FunEntryPtr> buildEntry(const DefineFunsRecCommandPtr& node);

            DatatypeEntryPtr buildEntry(const DeclareDatatypeCommandPtr& node);
            std::vector<DatatypeEntryPtr> buildEntry(const DeclareDatatypesCommandPtr& node);

            void loadTheory(const std::string& theory);
            void loadLogic(const std::string& logic);
        public:
            VisitorWithStack0()
                    : stack(std::make_shared<SymbolStack>())
                    , config(std::make_shared<Configuration>()) {}

            void visit(const SimpleAttributePtr& node) final;
            void visit(const SExpressionAttributePtr& node) final;
            void visit(const SymbolAttributePtr& node) final;
            void visit(const BooleanAttributePtr& node) final;
            void visit(const NumeralAttributePtr& node) final;
            void visit(const DecimalAttributePtr& node) final;
            void visit(const StringAttributePtr& node) final;
            void visit(const TheoriesAttributePtr& node) final;
            void visit(const SortsAttributePtr& node) final;
            void visit(const FunsAttributePtr& node) final;

            void visit(const SymbolPtr& node) final;
            void visit(const KeywordPtr& node) final;
            void visit(const MetaSpecConstantPtr& node) final;
            void visit(const BooleanValuePtr& node) final;
            void visit(const PropLiteralPtr& node) final;

            void visit(const AssertCommandPtr& node) final;
            void visit(const CheckSatCommandPtr& node) final;
            void visit(const CheckSatAssumCommandPtr& node) final;
            void visit(const DeclareConstCommandPtr& node) final;
            void visit(const DeclareDatatypeCommandPtr& node) final;
            void visit(const DeclareDatatypesCommandPtr& node) final;
            void visit(const DeclareFunCommandPtr& node) final;
            void visit(const DeclareSortCommandPtr& node) final;
            void visit(const DeclareHeapCommandPtr& node) final;
            void visit(const DefineFunCommandPtr& node) final;
            void visit(const DefineFunRecCommandPtr& node) final;
            void visit(const DefineFunsRecCommandPtr& node) final;
            void visit(const DefineSortCommandPtr& node) final;
            void visit(const EchoCommandPtr& node) final;
            void visit(const ExitCommandPtr& node) final;
            void visit(const GetAssertsCommandPtr& node) final;
            void visit(const GetAssignsCommandPtr& node) final;
            void visit(const GetInfoCommandPtr& node) final;
            void visit(const GetModelCommandPtr& node) final;
            void visit(const GetOptionCommandPtr& node) final;
            void visit(const GetProofCommandPtr& node) final;
            void visit(const GetUnsatAssumsCommandPtr& node) final;
            void visit(const GetUnsatCoreCommandPtr& node) final;
            void visit(const GetValueCommandPtr& node) final;
            void visit(const PopCommandPtr& node) final;
            void visit(const PushCommandPtr& node) final;
            void visit(const ResetCommandPtr& node) final;
            void visit(const ResetAssertsCommandPtr& node) final;
            void visit(const SetInfoCommandPtr& node) final;
            void visit(const SetLogicCommandPtr& node) final;
            void visit(const SetOptionCommandPtr& node) final;

            void visit(const SortDeclarationPtr& node) final;
            void visit(const SelectorDeclarationPtr& node) final;
            void visit(const ConstructorDeclarationPtr& node) final;
            void visit(const SimpleDatatypeDeclarationPtr& node) final;
            void visit(const ParametricDatatypeDeclarationPtr& node) final;

            void visit(const FunctionDeclarationPtr& node) final;
            void visit(const FunctionDefinitionPtr& node) final;

            void visit(const SimpleIdentifierPtr& node) final;
            void visit(const QualifiedIdentifierPtr& node) final;

            void visit(const NumeralLiteralPtr& node) final;
            void visit(const DecimalLiteralPtr& node) final;
            void visit(const StringLiteralPtr& node) final;

            void visit(const LogicPtr& node) final;
            void visit(const TheoryPtr& node) final;
            void visit(const ScriptPtr& node) final;

            void visit(const QualifiedConstructorPtr& node) final;
            void visit(const QualifiedPatternPtr& node) final;
            void visit(const MatchCasePtr& node) final;

            void visit(const CompSExpressionPtr& node) final;

            void visit(const SortPtr& node) final;

            void visit(const SortSymbolDeclarationPtr& node) final;
            void visit(const SpecConstFunDeclarationPtr& node) final;
            void visit(const MetaSpecConstFunDeclarationPtr& node) final;
            void visit(const SimpleFunDeclarationPtr& node) final;
            void visit(const ParametricFunDeclarationPtr& node) final;

            void visit(const QualifiedTermPtr& node) final;
            void visit(const LetTermPtr& node) final;
            void visit(const ForallTermPtr& node) final;
            void visit(const ExistsTermPtr& node) final;
            void visit(const MatchTermPtr& node) final;
            void visit(const AnnotatedTermPtr& node) final;

            void visit(const TrueTermPtr& node) final;
            void visit(const FalseTermPtr& node) final;
            void visit(const NotTermPtr& node) final;
            void visit(const ImpliesTermPtr& node) final;
            void visit(const AndTermPtr& node) final;
            void visit(const OrTermPtr& node) final;
            void visit(const XorTermPtr& node) final;
            void visit(const EqualsTermPtr& node) final;
            void visit(const DistinctTermPtr& node) final;
            void visit(const IteTermPtr& node) final;

            void visit(const EmpTermPtr& node) final;
            void visit(const SepTermPtr& node) final;
            void visit(const WandTermPtr& node) final;
            void visit(const PtoTermPtr& node) final;
            void visit(const NilTermPtr& node) final;

            void visit(const SortedVariablePtr& node) final;
            void visit(const VariableBindingPtr& node) final;

            virtual void visitWithStack(const SimpleAttributePtr& node) = 0;
            virtual void visitWithStack(const SExpressionAttributePtr& node) = 0;
            virtual void visitWithStack(const SymbolAttributePtr& node) = 0;
            virtual void visitWithStack(const BooleanAttributePtr& node) = 0;
            virtual void visitWithStack(const NumeralAttributePtr& node) = 0;
            virtual void visitWithStack(const DecimalAttributePtr& node) = 0;
            virtual void visitWithStack(const StringAttributePtr& node) = 0;
            virtual void visitWithStack(const TheoriesAttributePtr& node) = 0;
            virtual void visitWithStack(const SortsAttributePtr& node) = 0;
            virtual void visitWithStack(const FunsAttributePtr& node) = 0;

            virtual void visitWithStack(const SymbolPtr& node) = 0;
            virtual void visitWithStack(const KeywordPtr& node) = 0;
            virtual void visitWithStack(const MetaSpecConstantPtr& node) = 0;
            virtual void visitWithStack(const BooleanValuePtr& node) = 0;
            virtual void visitWithStack(const PropLiteralPtr& node) = 0;

            virtual void visitWithStack(const AssertCommandPtr& node) = 0;
            virtual void visitWithStack(const CheckSatCommandPtr& node) = 0;
            virtual void visitWithStack(const CheckSatAssumCommandPtr& node) = 0;
            virtual void visitWithStack(const DeclareConstCommandPtr& node) = 0;
            virtual void visitWithStack(const DeclareDatatypeCommandPtr& node) = 0;
            virtual void visitWithStack(const DeclareDatatypesCommandPtr& node) = 0;
            virtual void visitWithStack(const DeclareFunCommandPtr& node) = 0;
            virtual void visitWithStack(const DeclareSortCommandPtr& node) = 0;
            virtual void visitWithStack(const DeclareHeapCommandPtr& node) = 0;
            virtual void visitWithStack(const DefineFunCommandPtr& node) = 0;
            virtual void visitWithStack(const DefineFunRecCommandPtr& node) = 0;
            virtual void visitWithStack(const DefineFunsRecCommandPtr& node) = 0;
            virtual void visitWithStack(const DefineSortCommandPtr& node) = 0;
            virtual void visitWithStack(const EchoCommandPtr& node) = 0;
            virtual void visitWithStack(const ExitCommandPtr& node) = 0;
            virtual void visitWithStack(const GetAssertsCommandPtr& node) = 0;
            virtual void visitWithStack(const GetAssignsCommandPtr& node) = 0;
            virtual void visitWithStack(const GetInfoCommandPtr& node) = 0;
            virtual void visitWithStack(const GetModelCommandPtr& node) = 0;
            virtual void visitWithStack(const GetOptionCommandPtr& node) = 0;
            virtual void visitWithStack(const GetProofCommandPtr& node) = 0;
            virtual void visitWithStack(const GetUnsatAssumsCommandPtr& node) = 0;
            virtual void visitWithStack(const GetUnsatCoreCommandPtr& node) = 0;
            virtual void visitWithStack(const GetValueCommandPtr& node) = 0;
            virtual void visitWithStack(const PopCommandPtr& node) = 0;
            virtual void visitWithStack(const PushCommandPtr& node) = 0;
            virtual void visitWithStack(const ResetCommandPtr& node) = 0;
            virtual void visitWithStack(const ResetAssertsCommandPtr& node) = 0;
            virtual void visitWithStack(const SetInfoCommandPtr& node) = 0;
            virtual void visitWithStack(const SetLogicCommandPtr& node) = 0;
            virtual void visitWithStack(const SetOptionCommandPtr& node) = 0;

            virtual void visitWithStack(const SortDeclarationPtr& node) = 0;
            virtual void visitWithStack(const SelectorDeclarationPtr& node) = 0;
            virtual void visitWithStack(const ConstructorDeclarationPtr& node) = 0;
            virtual void visitWithStack(const SimpleDatatypeDeclarationPtr& node) = 0;
            virtual void visitWithStack(const ParametricDatatypeDeclarationPtr& node) = 0;

            virtual void visitWithStack(const FunctionDeclarationPtr& node) = 0;
            virtual void visitWithStack(const FunctionDefinitionPtr& node) = 0;

            virtual void visitWithStack(const SimpleIdentifierPtr& node) = 0;
            virtual void visitWithStack(const QualifiedIdentifierPtr& node) = 0;

            virtual void visitWithStack(const NumeralLiteralPtr& node) = 0;
            virtual void visitWithStack(const DecimalLiteralPtr& node) = 0;
            virtual void visitWithStack(const StringLiteralPtr& node) = 0;

            virtual void visitWithStack(const LogicPtr& node) = 0;
            virtual void visitWithStack(const TheoryPtr& node) = 0;
            virtual void visitWithStack(const ScriptPtr& node) = 0;

            virtual void visitWithStack(const QualifiedConstructorPtr& node) = 0;
            virtual void visitWithStack(const QualifiedPatternPtr& node) = 0;
            virtual void visitWithStack(const MatchCasePtr& node) = 0;

            virtual void visitWithStack(const CompSExpressionPtr& node) = 0;

            virtual void visitWithStack(const SortPtr& node) = 0;

            virtual void visitWithStack(const SortSymbolDeclarationPtr& node) = 0;
            virtual void visitWithStack(const SpecConstFunDeclarationPtr& node) = 0;
            virtual void visitWithStack(const MetaSpecConstFunDeclarationPtr& node) = 0;
            virtual void visitWithStack(const SimpleFunDeclarationPtr& node) = 0;
            virtual void visitWithStack(const ParametricFunDeclarationPtr& node) = 0;

            virtual void visitWithStack(const QualifiedTermPtr& node) = 0;
            virtual void visitWithStack(const LetTermPtr& node) = 0;
            virtual void visitWithStack(const ForallTermPtr& node) = 0;
            virtual void visitWithStack(const ExistsTermPtr& node) = 0;
            virtual void visitWithStack(const MatchTermPtr& node) = 0;
            virtual void visitWithStack(const AnnotatedTermPtr& node) = 0;

            virtual void visitWithStack(const TrueTermPtr& node) = 0;
            virtual void visitWithStack(const FalseTermPtr& node) = 0;
            virtual void visitWithStack(const NotTermPtr& node) = 0;
            virtual void visitWithStack(const ImpliesTermPtr& node) = 0;
            virtual void visitWithStack(const AndTermPtr& node) = 0;
            virtual void visitWithStack(const OrTermPtr& node) = 0;
            virtual void visitWithStack(const XorTermPtr& node) = 0;
            virtual void visitWithStack(const EqualsTermPtr& node) = 0;
            virtual void visitWithStack(const DistinctTermPtr& node) = 0;
            virtual void visitWithStack(const IteTermPtr& node) = 0;

            virtual void visitWithStack(const EmpTermPtr& node) = 0;
            virtual void visitWithStack(const SepTermPtr& node) = 0;
            virtual void visitWithStack(const WandTermPtr& node) = 0;
            virtual void visitWithStack(const PtoTermPtr& node) = 0;
            virtual void visitWithStack(const NilTermPtr& node) = 0;

            virtual void visitWithStack(const SortedVariablePtr& node) = 0;
            virtual void visitWithStack(const VariableBindingPtr& node) = 0;

        };

        /* ============================== DummyVisitorWithStack0 ============================== */
        /**
         * A dummy (empty) implementation for VisitorWithStack0.
         * When inheriting, add functionality by overriding only the needed visitWithStack() methods.
         */
        class DummyVisitorWithStack0 : public virtual VisitorWithStack0 {
        public:
            void visitWithStack(const SimpleAttributePtr& node) override;
            void visitWithStack(const SExpressionAttributePtr& node) override;
            void visitWithStack(const SymbolAttributePtr& node) override;
            void visitWithStack(const BooleanAttributePtr& node) override;
            void visitWithStack(const NumeralAttributePtr& node) override;
            void visitWithStack(const DecimalAttributePtr& node) override;
            void visitWithStack(const StringAttributePtr& node) override;
            void visitWithStack(const TheoriesAttributePtr& node) override;
            void visitWithStack(const SortsAttributePtr& node) override;
            void visitWithStack(const FunsAttributePtr& node) override;

            void visitWithStack(const SymbolPtr& node) override;
            void visitWithStack(const KeywordPtr& node) override;
            void visitWithStack(const MetaSpecConstantPtr& node) override;
            void visitWithStack(const BooleanValuePtr& node) override;
            void visitWithStack(const PropLiteralPtr& node) override;

            void visitWithStack(const AssertCommandPtr& node) override;
            void visitWithStack(const CheckSatCommandPtr& node) override;
            void visitWithStack(const CheckSatAssumCommandPtr& node) override;
            void visitWithStack(const DeclareConstCommandPtr& node) override;
            void visitWithStack(const DeclareDatatypeCommandPtr& node) override;
            void visitWithStack(const DeclareDatatypesCommandPtr& node) override;
            void visitWithStack(const DeclareFunCommandPtr& node) override;
            void visitWithStack(const DeclareSortCommandPtr& node) override;
            void visitWithStack(const DeclareHeapCommandPtr& node) override;
            void visitWithStack(const DefineFunCommandPtr& node) override;
            void visitWithStack(const DefineFunRecCommandPtr& node) override;
            void visitWithStack(const DefineFunsRecCommandPtr& node) override;
            void visitWithStack(const DefineSortCommandPtr& node) override;
            void visitWithStack(const EchoCommandPtr& node) override;
            void visitWithStack(const ExitCommandPtr& node) override;
            void visitWithStack(const GetAssertsCommandPtr& node) override;
            void visitWithStack(const GetAssignsCommandPtr& node) override;
            void visitWithStack(const GetInfoCommandPtr& node) override;
            void visitWithStack(const GetModelCommandPtr& node) override;
            void visitWithStack(const GetOptionCommandPtr& node) override;
            void visitWithStack(const GetProofCommandPtr& node) override;
            void visitWithStack(const GetUnsatAssumsCommandPtr& node) override;
            void visitWithStack(const GetUnsatCoreCommandPtr& node) override;
            void visitWithStack(const GetValueCommandPtr& node) override;
            void visitWithStack(const PopCommandPtr& node) override;
            void visitWithStack(const PushCommandPtr& node) override;
            void visitWithStack(const ResetCommandPtr& node) override;
            void visitWithStack(const ResetAssertsCommandPtr& node) override;
            void visitWithStack(const SetInfoCommandPtr& node) override;
            void visitWithStack(const SetLogicCommandPtr& node) override;
            void visitWithStack(const SetOptionCommandPtr& node) override;

            void visitWithStack(const SortDeclarationPtr& node) override;
            void visitWithStack(const SelectorDeclarationPtr& node) override;
            void visitWithStack(const ConstructorDeclarationPtr& node) override;
            void visitWithStack(const SimpleDatatypeDeclarationPtr& node) override;
            void visitWithStack(const ParametricDatatypeDeclarationPtr& node) override;

            void visitWithStack(const FunctionDeclarationPtr& node) override;
            void visitWithStack(const FunctionDefinitionPtr& node) override;

            void visitWithStack(const SimpleIdentifierPtr& node) override;
            void visitWithStack(const QualifiedIdentifierPtr& node) override;

            void visitWithStack(const NumeralLiteralPtr& node) override;
            void visitWithStack(const DecimalLiteralPtr& node) override;
            void visitWithStack(const StringLiteralPtr& node) override;

            void visitWithStack(const LogicPtr& node) override;
            void visitWithStack(const TheoryPtr& node) override;
            void visitWithStack(const ScriptPtr& node) override;

            void visitWithStack(const QualifiedConstructorPtr& node) override;
            void visitWithStack(const QualifiedPatternPtr& node) override;
            void visitWithStack(const MatchCasePtr& node) override;

            void visitWithStack(const CompSExpressionPtr& node) override;

            void visitWithStack(const SortPtr& node) override;

            void visitWithStack(const SortSymbolDeclarationPtr& node) override;
            void visitWithStack(const SpecConstFunDeclarationPtr& node) override;
            void visitWithStack(const MetaSpecConstFunDeclarationPtr& node) override;
            void visitWithStack(const SimpleFunDeclarationPtr& node) override;
            void visitWithStack(const ParametricFunDeclarationPtr& node) override;

            void visitWithStack(const QualifiedTermPtr& node) override;
            void visitWithStack(const LetTermPtr& node) override;
            void visitWithStack(const ForallTermPtr& node) override;
            void visitWithStack(const ExistsTermPtr& node) override;
            void visitWithStack(const MatchTermPtr& node) override;
            void visitWithStack(const AnnotatedTermPtr& node) override;

            void visitWithStack(const TrueTermPtr& node) override;
            void visitWithStack(const FalseTermPtr& node) override;
            void visitWithStack(const NotTermPtr& node) override;
            void visitWithStack(const ImpliesTermPtr& node) override;
            void visitWithStack(const AndTermPtr& node) override;
            void visitWithStack(const OrTermPtr& node) override;
            void visitWithStack(const XorTermPtr& node) override;
            void visitWithStack(const EqualsTermPtr& node) override;
            void visitWithStack(const DistinctTermPtr& node) override;
            void visitWithStack(const IteTermPtr& node) override;

            void visitWithStack(const EmpTermPtr& node) override;
            void visitWithStack(const SepTermPtr& node) override;
            void visitWithStack(const WandTermPtr& node) override;
            void visitWithStack(const PtoTermPtr& node) override;
            void visitWithStack(const NilTermPtr& node) override;

            void visitWithStack(const SortedVariablePtr& node) override;
            void visitWithStack(const VariableBindingPtr& node) override;
        };
    }
}

#endif //SLCOMP_PARSER_SEP_VISITOR_STACK_H
