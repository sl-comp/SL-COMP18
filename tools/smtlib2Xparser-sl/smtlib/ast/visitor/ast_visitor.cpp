#include "ast_visitor.h"

#include "ast/ast_attribute.h"
#include "ast/ast_command.h"
#include "ast/ast_logic.h"
#include "ast/ast_s_expr.h"
#include "ast/ast_script.h"
#include "ast/ast_symbol_decl.h"
#include "ast/ast_term.h"
#include "ast/ast_theory.h"

using namespace smtlib::ast;

void Visitor0::visit0(const NodePtr& node) {
    if (node == nullptr) {
        return;
    }
    node->accept(this);
}

void DummyVisitor0::visit(const AttributePtr& node) {
    visit0(node->keyword);
    visit0(node->value);
}

void DummyVisitor0::visit(const CompAttributeValuePtr& node) {
    visit0(node->values);
}

void DummyVisitor0::visit(const SymbolPtr& node) {}

void DummyVisitor0::visit(const KeywordPtr& node) {}

void DummyVisitor0::visit(const MetaSpecConstantPtr& node) {}

void DummyVisitor0::visit(const BooleanValuePtr& node) {}

void DummyVisitor0::visit(const PropLiteralPtr& node) {}

void DummyVisitor0::visit(const AssertCommandPtr& node) {
    visit0(node->term);
}

void DummyVisitor0::visit(const CheckSatCommandPtr& node) {}

void DummyVisitor0::visit(const CheckUnsatCommandPtr& node) {}

void DummyVisitor0::visit(const CheckSatAssumCommandPtr& node) {
    visit0(node->assumptions);
}

void DummyVisitor0::visit(const DeclareConstCommandPtr& node) {
    visit0(node->symbol);
    visit0(node->sort);
}

void DummyVisitor0::visit(const DeclareDatatypeCommandPtr& node) {
    visit0(node->symbol);
    visit0(node->declaration);
}

void DummyVisitor0::visit(const DeclareDatatypesCommandPtr& node) {
    visit0(node->declarations);
}

void DummyVisitor0::visit(const DeclareFunCommandPtr& node) {
    visit0(node->symbol);
    visit0(node->parameters);
    visit0(node->sort);
}

void DummyVisitor0::visit(const DeclareSortCommandPtr& node) {
    visit0(node->symbol);
}

void DummyVisitor0::visit(const DeclareHeapCommandPtr& node) {
    visit0(node->locDataPairs);
}

void DummyVisitor0::visit(const DefineFunCommandPtr& node) {
    visit0(node->definition);
}

void DummyVisitor0::visit(const DefineFunRecCommandPtr& node) {
    visit0(node->definition);
}

void DummyVisitor0::visit(const DefineFunsRecCommandPtr& node) {
    visit0(node->declarations);
    visit0(node->bodies);
}

void DummyVisitor0::visit(const DefineSortCommandPtr& node) {
    visit0(node->symbol);
    visit0(node->parameters);
    visit0(node->sort);
}

void DummyVisitor0::visit(const EchoCommandPtr& node) {}

void DummyVisitor0::visit(const ExitCommandPtr& node) {}

void DummyVisitor0::visit(const GetAssertsCommandPtr& node) {}

void DummyVisitor0::visit(const GetAssignsCommandPtr& node) {}

void DummyVisitor0::visit(const GetInfoCommandPtr& node) {
    visit0(node->flag);
}

void DummyVisitor0::visit(const GetModelCommandPtr& node) {}

void DummyVisitor0::visit(const GetOptionCommandPtr& node) {
    visit0(node->option);
}

void DummyVisitor0::visit(const GetProofCommandPtr& node) {}

void DummyVisitor0::visit(const GetUnsatAssumsCommandPtr& node) {}

void DummyVisitor0::visit(const GetUnsatCoreCommandPtr& node) {}

void DummyVisitor0::visit(const GetValueCommandPtr& node) {
    visit0(node->terms);
}

void DummyVisitor0::visit(const PopCommandPtr& node) {
    visit0(node->numeral);
}

void DummyVisitor0::visit(const PushCommandPtr& node) {
    visit0(node->numeral);
}

void DummyVisitor0::visit(const ResetCommandPtr& node) {}

void DummyVisitor0::visit(const ResetAssertsCommandPtr& node) {}

void DummyVisitor0::visit(const SetInfoCommandPtr& node) {
    visit0(node->info);
}

void DummyVisitor0::visit(const SetLogicCommandPtr& node) {
    visit0(node->logic);
}

void DummyVisitor0::visit(const SetOptionCommandPtr& node) {
    visit0(node->option);
}

void DummyVisitor0::visit(const FunctionDeclarationPtr& node) {
    visit0(node->symbol);
    visit0(node->parameters);
    visit0(node->sort);
}

void DummyVisitor0::visit(const FunctionDefinitionPtr& node) {
    visit0(node->signature);
    visit0(node->body);
}

void DummyVisitor0::visit(const SimpleIdentifierPtr& node) {
    visit0(node->symbol);
}

void DummyVisitor0::visit(const QualifiedIdentifierPtr& node) {
    visit0(node->identifier);
    visit0(node->sort);
}

void DummyVisitor0::visit(const DecimalLiteralPtr& node) {}

void DummyVisitor0::visit(const NumeralLiteralPtr& node) {}

void DummyVisitor0::visit(const StringLiteralPtr& node) {}

void DummyVisitor0::visit(const LogicPtr& node) {
    visit0(node->name);
    visit0(node->attributes);
}

void DummyVisitor0::visit(const TheoryPtr& node) {
    visit0(node->name);
    visit0(node->attributes);
}

void DummyVisitor0::visit(const ScriptPtr& node) {
    visit0(node->commands);
}

void DummyVisitor0::visit(const SortPtr& node) {
    visit0(node->identifier);
    visit0(node->arguments);
}

void DummyVisitor0::visit(const CompSExpressionPtr& node) {
    visit0(node->expressions);
}

void DummyVisitor0::visit(const SortSymbolDeclarationPtr& node) {
    visit0(node->identifier);
    visit0(node->arity);
    visit0(node->attributes);
}

void DummyVisitor0::visit(const SortDeclarationPtr& node) {
    visit0(node->symbol);
    visit0(node->arity);
}

void DummyVisitor0::visit(const SelectorDeclarationPtr& node) {
    visit0(node->symbol);
    visit0(node->sort);
}

void DummyVisitor0::visit(const ConstructorDeclarationPtr& node) {
    visit0(node->symbol);
    visit0(node->selectors);
}

void DummyVisitor0::visit(const SimpleDatatypeDeclarationPtr& node) {
    visit0(node->constructors);
}

void DummyVisitor0::visit(const ParametricDatatypeDeclarationPtr& node) {
    visit0(node->constructors);
    visit0(node->parameters);
}

void DummyVisitor0::visit(const QualifiedConstructorPtr& node) {
    visit0(node->symbol);
    visit0(node->sort);
}

void DummyVisitor0::visit(const QualifiedPatternPtr& node) {
    visit0(node->constructor);
    visit0(node->symbols);
}

void DummyVisitor0::visit(const MatchCasePtr& node) {
    visit0(node->pattern);
    visit0(node->term);
}

void DummyVisitor0::visit(const SpecConstFunDeclarationPtr& node) {
    visit0(node->constant);
    visit0(node->sort);
    visit0(node->attributes);
}

void DummyVisitor0::visit(const MetaSpecConstFunDeclarationPtr& node) {
    visit0(node->constant);
    visit0(node->sort);
    visit0(node->attributes);
}

void DummyVisitor0::visit(const SimpleFunDeclarationPtr& node) {
    visit0(node->identifier);
    visit0(node->signature);
    visit0(node->attributes);
}

void DummyVisitor0::visit(const ParametricFunDeclarationPtr& node) {
    visit0(node->parameters);
    visit0(node->identifier);
    visit0(node->signature);
    visit0(node->attributes);
}

void DummyVisitor0::visit(const QualifiedTermPtr& node) {
    visit0(node->identifier);
    visit0(node->terms);
}

void DummyVisitor0::visit(const LetTermPtr& node) {
    visit0(node->bindings);
    visit0(node->term);
}

void DummyVisitor0::visit(const ForallTermPtr& node) {
    visit0(node->bindings);
    visit0(node->term);
}

void DummyVisitor0::visit(const ExistsTermPtr& node) {
    visit0(node->bindings);
    visit0(node->term);
}

void DummyVisitor0::visit(const MatchTermPtr& node) {
    visit0(node->term);
    visit0(node->cases);
}

void DummyVisitor0::visit(const AnnotatedTermPtr& node) {
    visit0(node->term);
    visit0(node->attributes);
}

void DummyVisitor0::visit(const SortedVariablePtr& node) {
    visit0(node->symbol);
    visit0(node->sort);
}

void DummyVisitor0::visit(const VariableBindingPtr& node) {
    visit0(node->symbol);
    visit0(node->term);
}
