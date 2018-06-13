#ifndef SLCOMP_PARSER_SEP_PP_SLCOMP14_H
#define SLCOMP_PARSER_SEP_PP_SLCOMP14_H

#include "visitor/sep_visitor.h"
#include "visitor/sep_visitor_extra.h"

#include <unordered_map>

namespace smtlib {
    namespace sep {

        /* ==================================== TermSorter ==================================== */

        /** Determines the sort of a term */
        class Pp_SLCOMP14 : public DummyVisitor1<bool> {
        private:
            // inherited field 'ret'
            /** stores constructors declared in datatypes to
                translate 'pto' terms
             */
            std::unordered_map<std::string, std::vector<SelectorDeclarationPtr> >
                    map_cons = {}; 
            /** stores the name of the defined sort in datatypes,
                used to translate fields
             */
            std::string sortname = ""; 
            /** trigger for type of term (Bool or Space) */
            bool inspace = false; 
            /** trigger for visibility of variables (local or global) */
            bool inpred = false; 
            /** used for pretty printing */
            size_t nesting = 0;

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

            bool run(const NodePtr& node) override {
                return wrappedVisit(node);
            }
        };

        typedef std::shared_ptr<Pp_SLCOMP14> Pp_SLCOMP14Ptr;
    }
}

#endif //SLCOMP_PARSER_SEP_PP_SLCOMP14_H
