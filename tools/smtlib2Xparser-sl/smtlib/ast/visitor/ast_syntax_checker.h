#ifndef SLCOMP_PARSER_AST_SYNTAX_CHECKER_H
#define SLCOMP_PARSER_AST_SYNTAX_CHECKER_H

#include "ast_visitor.h"

#include <regex>
#include <string>
#include <unordered_map>
#include <vector>

namespace smtlib {
    namespace ast {
        class SyntaxChecker : public DummyVisitor0 {
        private:
            struct Error {
                std::vector<std::string> messages;
                NodePtr node;

                inline Error() = default;

                inline Error(std::string message, NodePtr node)
                        : node(std::move(node)) {
                    messages.push_back(std::move(message));
                }

                inline Error(std::vector<std::string> messages, NodePtr node)
                        : node(std::move(node))
                        , messages(std::move(messages)) {}
            };

            typedef std::shared_ptr<Error> ErrorPtr;

            std::vector<ErrorPtr> errors;

            const std::regex regexSymbol = std::regex(
                    "^([a-zA-Z+\\-/*=%?!.$_~&^<>@][a-zA-Z0-9+\\-/*=%?!.$_~&^<>@]*)"
                            "|(\\|[\\x20-\\x5B\\x5D-\\x7B\\x7D\\x7E\\xA0-\\xFF\\x09\\r\\n \\xA0]*\\|)$"
            );
            const std::regex regexKeyword = std::regex(
                    "^:([a-zA-Z+\\-/*=%?!.$_~&^<>@][a-zA-Z0-9+\\-/*=%?!.$_~&^<>@]*)"
                            "|(\\|[\\x20-\\x5B\\x5D-\\x7B\\x7D\\x7E\\xA0-\\xFF\\x09\\r\\n \\xA0]*\\|)$"
            );

            ErrorPtr addError(const std::string& message, const NodePtr& node, ErrorPtr& err);

            ErrorPtr checkParamUsage(const std::vector<SymbolPtr>& params,
                                     std::unordered_map<std::string, bool>& paramUsage,
                                     const SortPtr& sort, const NodePtr& source, ErrorPtr& err);
        public:
            void visit(const AttributePtr& node) override;
            void visit(const CompAttributeValuePtr& node) override;

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

            void visit(const FunctionDeclarationPtr& node) override;
            void visit(const FunctionDefinitionPtr& node) override;

            void visit(const SimpleIdentifierPtr& node) override;
            void visit(const QualifiedIdentifierPtr& node) override;

            void visit(const DecimalLiteralPtr& node) override;
            void visit(const NumeralLiteralPtr& node) override;
            void visit(const StringLiteralPtr& node) override;

            void visit(const LogicPtr& node) override;
            void visit(const TheoryPtr& node) override;
            void visit(const ScriptPtr& node) override;

            void visit(const SortPtr& node) override;

            void visit(const CompSExpressionPtr& node) override;

            void visit(const SortSymbolDeclarationPtr& node) override;
            void visit(const SortDeclarationPtr& node) override;
            void visit(const SelectorDeclarationPtr& node) override;
            void visit(const ConstructorDeclarationPtr& node) override;
            void visit(const SimpleDatatypeDeclarationPtr& node) override;
            void visit(const ParametricDatatypeDeclarationPtr& node) override;

            void visit(const QualifiedConstructorPtr& node) override;
            void visit(const QualifiedPatternPtr& node) override;
            void visit(const MatchCasePtr& node) override;

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

            void visit(const SortedVariablePtr& node) override;
            void visit(const VariableBindingPtr& node) override;

            bool check(const NodePtr& node);

            std::string getErrors();
        };

        typedef std::shared_ptr<SyntaxChecker> SyntaxCheckerPtr;
    }
}

#endif //SLCOMP_PARSER_AST_SYNTAX_CHECKER_H
