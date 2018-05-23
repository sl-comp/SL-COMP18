#ifndef SLCOMP_PARSER_SEP_TRANSLATOR_H
#define SLCOMP_PARSER_SEP_TRANSLATOR_H

#include "ast/ast_abstract.h"
#include "ast/ast_classes.h"
#include "ast/ast_interfaces.h"
#include "sep/sep_abstract.h"
#include "sep/sep_classes.h"
#include "sep/sep_interfaces.h"

#include <memory>
#include <string>

namespace smtlib {
    namespace sep {
        class Translator {
        private:
            template<class astT1, class astT2, class smtT>
            std::vector<std::shared_ptr<smtT>> translateToSmtCast(const std::vector<std::shared_ptr<astT1>>& vec) {
                std::vector<std::shared_ptr<smtT>> newVec;

                for (const auto elem : vec) {
                    auto temp = std::dynamic_pointer_cast<astT2>(elem);
                    if (temp) {
                        newVec.push_back(translate(temp));
                    }
                }

                return newVec;
            }

            template<class astT, class smtT>
            std::vector<std::shared_ptr<smtT>> translateToSmt(const std::vector<std::shared_ptr<astT>>& vec) {
                std::vector<std::shared_ptr<smtT>> newVec;

                for (const auto elem : vec) {
                    newVec.push_back(translate(elem));
                }

                return newVec;
            }

            template<class astT1, class astT2, class smtT1, class smtT2>
            std::vector<std::pair<std::shared_ptr<smtT1>, std::shared_ptr<smtT2>>>
            translateToSmt(const std::vector<std::pair<std::shared_ptr<astT1>, std::shared_ptr<astT1>>>& vec) {
                std::vector<std::pair<std::shared_ptr<smtT1>, std::shared_ptr<smtT2>>> newVec;

                for (const auto pair : vec) {
                    newVec.push_back(std::make_pair(translate(pair.first), translate(pair.second)));
                }

                return newVec;
            }

            template<class T>
            std::vector<std::string> translateToString(const std::vector<std::shared_ptr<T>>& vec) {
                std::vector<std::string> newVec;

                for (const auto elem : vec) {
                    newVec.push_back(elem->toString());
                }

                return newVec;
            }

            void setFileLocation(const sep::NodePtr& output, const ast::NodePtr& source);

        public:
            sep::AttributePtr translate(const ast::AttributePtr&);

            sep::SymbolPtr translate(const ast::SymbolPtr&);
            sep::KeywordPtr translate(const ast::KeywordPtr&);
            sep::MetaSpecConstantPtr translate(const ast::MetaSpecConstantPtr&);
            sep::BooleanValuePtr translate(const ast::BooleanValuePtr&);
            sep::PropLiteralPtr translate(const ast::PropLiteralPtr&);

            sep::LogicPtr translate(const ast::LogicPtr&);
            sep::ScriptPtr translate(const ast::ScriptPtr&);
            sep::TheoryPtr translate(const ast::TheoryPtr&);

            sep::CommandPtr translate(const ast::CommandPtr&);
            sep::AssertCommandPtr translate(const ast::AssertCommandPtr&);
            sep::CheckSatCommandPtr translate(const ast::CheckSatCommandPtr&);
            sep::CheckUnsatCommandPtr translate(const ast::CheckUnsatCommandPtr&);
            sep::CheckSatAssumCommandPtr translate(const ast::CheckSatAssumCommandPtr&);
            sep::DeclareConstCommandPtr translate(const ast::DeclareConstCommandPtr&);
            sep::DeclareDatatypeCommandPtr translate(const ast::DeclareDatatypeCommandPtr&);
            sep::DeclareDatatypesCommandPtr translate(const ast::DeclareDatatypesCommandPtr&);
            sep::DeclareFunCommandPtr translate(const ast::DeclareFunCommandPtr&);
            sep::DeclareSortCommandPtr translate(const ast::DeclareSortCommandPtr&);
            sep::DeclareHeapCommandPtr translate(const ast::DeclareHeapCommandPtr&);
            sep::DefineFunCommandPtr translate(const ast::DefineFunCommandPtr&);
            sep::DefineFunRecCommandPtr translate(const ast::DefineFunRecCommandPtr&);
            sep::DefineFunsRecCommandPtr translate(const ast::DefineFunsRecCommandPtr&);
            sep::DefineSortCommandPtr translate(const ast::DefineSortCommandPtr&);
            sep::EchoCommandPtr translate(const ast::EchoCommandPtr&);
            sep::ExitCommandPtr translate(const ast::ExitCommandPtr&);
            sep::GetAssertsCommandPtr translate(const ast::GetAssertsCommandPtr&);
            sep::GetAssignsCommandPtr translate(const ast::GetAssignsCommandPtr&);
            sep::GetInfoCommandPtr translate(const ast::GetInfoCommandPtr&);
            sep::GetModelCommandPtr translate(const ast::GetModelCommandPtr&);
            sep::GetOptionCommandPtr translate(const ast::GetOptionCommandPtr&);
            sep::GetProofCommandPtr translate(const ast::GetProofCommandPtr&);
            sep::GetUnsatAssumsCommandPtr translate(const ast::GetUnsatAssumsCommandPtr&);
            sep::GetUnsatCoreCommandPtr translate(const ast::GetUnsatCoreCommandPtr&);
            sep::GetValueCommandPtr translate(const ast::GetValueCommandPtr&);
            sep::PopCommandPtr translate(const ast::PopCommandPtr&);
            sep::PushCommandPtr translate(const ast::PushCommandPtr&);
            sep::ResetCommandPtr translate(const ast::ResetCommandPtr&);
            sep::ResetAssertsCommandPtr translate(const ast::ResetAssertsCommandPtr&);
            sep::SetInfoCommandPtr translate(const ast::SetInfoCommandPtr&);
            sep::SetLogicCommandPtr translate(const ast::SetLogicCommandPtr&);
            sep::SetOptionCommandPtr translate(const ast::SetOptionCommandPtr&);

            sep::SortDeclarationPtr translate(const ast::SortDeclarationPtr&);
            sep::SelectorDeclarationPtr translate(const ast::SelectorDeclarationPtr&);
            sep::ConstructorDeclarationPtr translate(const ast::ConstructorDeclarationPtr&);
            sep::DatatypeDeclarationPtr translate(const ast::DatatypeDeclarationPtr&);

            sep::SimpleDatatypeDeclarationPtr translate(
                    const ast::SimpleDatatypeDeclarationPtr& decl);

            sep::ParametricDatatypeDeclarationPtr translate(
                    const ast::ParametricDatatypeDeclarationPtr& decl);

            sep::FunctionDeclarationPtr translate(const ast::FunctionDeclarationPtr&);
            sep::FunctionDefinitionPtr translate(const ast::FunctionDefinitionPtr&);

            sep::IndexPtr translate(const ast::IndexPtr&);

            sep::IdentifierPtr translate(const ast::IdentifierPtr&);
            sep::SimpleIdentifierPtr translate(const ast::SimpleIdentifierPtr&);
            sep::QualifiedIdentifierPtr translate(const ast::QualifiedIdentifierPtr&);

            sep::SpecConstantPtr translate(const ast::SpecConstantPtr&);
            sep::DecimalLiteralPtr translate(const ast::DecimalLiteralPtr&);
            sep::NumeralLiteralPtr translate(const ast::NumeralLiteralPtr&);
            sep::StringLiteralPtr translate(const ast::StringLiteralPtr&);

            sep::SortPtr translate(const ast::SortPtr&);

            sep::SExpressionPtr translate(const ast::SExpressionPtr&);
            sep::CompSExpressionPtr translate(const ast::CompSExpressionPtr&);

            sep::SortSymbolDeclarationPtr translate(const ast::SortSymbolDeclarationPtr&);
            sep::FunSymbolDeclarationPtr translate(const ast::FunSymbolDeclarationPtr&);
            sep::SpecConstFunDeclarationPtr translate(const ast::SpecConstFunDeclarationPtr&);

            sep::MetaSpecConstFunDeclarationPtr translate(
                    const ast::MetaSpecConstFunDeclarationPtr& decl);

            sep::SimpleFunDeclarationPtr translate(const ast::SimpleFunDeclarationPtr&);

            sep::ParametricFunDeclarationPtr translate(
                    const ast::ParametricFunDeclarationPtr& decl);

            sep::ConstructorPtr translate(const ast::ConstructorPtr&);
            sep::QualifiedConstructorPtr translate(const ast::QualifiedConstructorPtr&);
            sep::PatternPtr translate(const ast::PatternPtr&);
            sep::QualifiedPatternPtr translate(const ast::QualifiedPatternPtr&);
            sep::MatchCasePtr translate(const ast::MatchCasePtr&);

            sep::TermPtr translate(const ast::TermPtr&);
            sep::QualifiedTermPtr translate(const ast::QualifiedTermPtr&);
            sep::LetTermPtr translate(const ast::LetTermPtr&);
            sep::ForallTermPtr translate(const ast::ForallTermPtr&);
            sep::ExistsTermPtr translate(const ast::ExistsTermPtr&);
            sep::MatchTermPtr translate(const ast::MatchTermPtr&);
            sep::AnnotatedTermPtr translate(const ast::AnnotatedTermPtr&);

            sep::SortedVariablePtr translate(const ast::SortedVariablePtr&);
            sep::VariableBindingPtr translate(const ast::VariableBindingPtr&);
        };

        typedef std::shared_ptr<Translator> TranslatorPtr;
    }
}

#endif //SLCOMP_PARSER_SEP_TRANSLATOR_H
