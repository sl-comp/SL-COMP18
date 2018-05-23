#include "sep_visitor.h"

#include "sep/sep_attribute.h"
#include "sep/sep_command.h"
#include "sep/sep_logic.h"
#include "sep/sep_s_expr.h"
#include "sep/sep_script.h"
#include "sep/sep_symbol_decl.h"
#include "sep/sep_term.h"
#include "sep/sep_theory.h"

using namespace smtlib::sep;

void Visitor0::visit0(const NodePtr& node) {
    if (!node) {
        return;
    }
    node->accept(this);
}

void DummyVisitor0::visit(const SimpleAttributePtr& node) {}

void DummyVisitor0::visit(const SExpressionAttributePtr& node) {
    visit0(node->value);
}

void DummyVisitor0::visit(const SymbolAttributePtr& node) {}

void DummyVisitor0::visit(const BooleanAttributePtr& node) {}

void DummyVisitor0::visit(const NumeralAttributePtr& node) {
    visit0(node->value);
}

void DummyVisitor0::visit(const DecimalAttributePtr& node) {
    visit0(node->value);
}

void DummyVisitor0::visit(const StringAttributePtr& node) {
    visit0(node->value);
}

void DummyVisitor0::visit(const TheoriesAttributePtr& node) {}

void DummyVisitor0::visit(const SortsAttributePtr& node) {
    visit0(node->declarations);
}

void DummyVisitor0::visit(const FunsAttributePtr& node) {
    visit0(node->declarations);
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
    visit0(node->sort);
}

void DummyVisitor0::visit(const DeclareDatatypeCommandPtr& node) {
    visit0(node->declaration);
}

void DummyVisitor0::visit(const DeclareDatatypesCommandPtr& node) {
    visit0(node->sorts);
    visit0(node->declarations);
}

void DummyVisitor0::visit(const DeclareFunCommandPtr& node) {
    visit0(node->parameters);
    visit0(node->sort);
}

void DummyVisitor0::visit(const DeclareSortCommandPtr& node) {}

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
    visit0(node->sort);
}

void DummyVisitor0::visit(const EchoCommandPtr& node) {}

void DummyVisitor0::visit(const ExitCommandPtr& node) {}

void DummyVisitor0::visit(const GetAssertsCommandPtr& node) {}

void DummyVisitor0::visit(const GetAssignsCommandPtr& node) {}

void DummyVisitor0::visit(const GetInfoCommandPtr& node) {}

void DummyVisitor0::visit(const GetModelCommandPtr& node) {}

void DummyVisitor0::visit(const GetOptionCommandPtr& node) {}

void DummyVisitor0::visit(const GetProofCommandPtr& node) {}

void DummyVisitor0::visit(const GetUnsatAssumsCommandPtr& node) {}

void DummyVisitor0::visit(const GetUnsatCoreCommandPtr& node) {}

void DummyVisitor0::visit(const GetValueCommandPtr& node) {
    visit0(node->terms);
}

void DummyVisitor0::visit(const PopCommandPtr& node) {}

void DummyVisitor0::visit(const PushCommandPtr& node) {}

void DummyVisitor0::visit(const ResetCommandPtr& node) {}

void DummyVisitor0::visit(const ResetAssertsCommandPtr& node) {}

void DummyVisitor0::visit(const SetInfoCommandPtr& node) {
    visit0(node->info);
}

void DummyVisitor0::visit(const SetLogicCommandPtr& node) {}

void DummyVisitor0::visit(const SetOptionCommandPtr& node) {
    visit0(node->option);
}

void DummyVisitor0::visit(const SortDeclarationPtr& node) {}

void DummyVisitor0::visit(const SelectorDeclarationPtr& node) {
    visit0(node->sort);
}

void DummyVisitor0::visit(const ConstructorDeclarationPtr& node) {
    visit0(node->selectors);
}

void DummyVisitor0::visit(const SimpleDatatypeDeclarationPtr& node) {
    visit0(node->constructors);
}

void DummyVisitor0::visit(const ParametricDatatypeDeclarationPtr& node) {
    visit0(node->constructors);
}

void DummyVisitor0::visit(const FunctionDeclarationPtr& node) {
    visit0(node->parameters);
    visit0(node->sort);
}

void DummyVisitor0::visit(const FunctionDefinitionPtr& node) {
    visit0(node->signature);
    visit0(node->body);
}

void DummyVisitor0::visit(const SimpleIdentifierPtr& node) {
    visit0(node->indices);
}

void DummyVisitor0::visit(const QualifiedIdentifierPtr& node) {
    visit0(node->identifier);
    visit0(node->sort);
}

void DummyVisitor0::visit(const NumeralLiteralPtr& node) {}

void DummyVisitor0::visit(const DecimalLiteralPtr& node) {}

void DummyVisitor0::visit(const StringLiteralPtr& node) {}

void DummyVisitor0::visit(const LogicPtr& node) {
    visit0(node->attributes);
}

void DummyVisitor0::visit(const TheoryPtr& node) {
    visit0(node->attributes);
}

void DummyVisitor0::visit(const ScriptPtr& node) {
    visit0(node->commands);
}

void DummyVisitor0::visit(const QualifiedConstructorPtr& node) {
    visit0(node->sort);
}

void DummyVisitor0::visit(const QualifiedPatternPtr& node) {
    visit0(node->constructor);
}

void DummyVisitor0::visit(const MatchCasePtr& node) {
    visit0(node->pattern);
    visit0(node->term);
}

void DummyVisitor0::visit(const CompSExpressionPtr& node) {
    visit0(node->expressions);
}

void DummyVisitor0::visit(const SortPtr& node) {
    visit0(node->arguments);
}

void DummyVisitor0::visit(const SortSymbolDeclarationPtr& node) {
    visit0(node->identifier);
       visit0(node->attributes);
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

void DummyVisitor0::visit(const TrueTermPtr& node) {}

void DummyVisitor0::visit(const FalseTermPtr& node) {}

void DummyVisitor0::visit(const NotTermPtr& node) {
    visit0(node->term);
}

void DummyVisitor0::visit(const ImpliesTermPtr& node) {
    visit0(node->terms);
}

void DummyVisitor0::visit(const AndTermPtr& node) {
    visit0(node->terms);
}

void DummyVisitor0::visit(const OrTermPtr& node) {
    visit0(node->terms);
}

void DummyVisitor0::visit(const XorTermPtr& node) {
    visit0(node->terms);
}

void DummyVisitor0::visit(const EqualsTermPtr& node) {
    visit0(node->terms);
}

void DummyVisitor0::visit(const DistinctTermPtr& node) {
    visit0(node->terms);
}

void DummyVisitor0::visit(const IteTermPtr& node) {
    visit0(node->testTerm);
    visit0(node->thenTerm);
    visit0(node->elseTerm);
}

void DummyVisitor0::visit(const EmpTermPtr& node) {}

void DummyVisitor0::visit(const SepTermPtr& node) {
    visit0(node->terms);
}

void DummyVisitor0::visit(const WandTermPtr& node) {
    visit0(node->terms);
}

void DummyVisitor0::visit(const PtoTermPtr& node) {
    visit0(node->leftTerm);
    visit0(node->rightTerm);
}

void DummyVisitor0::visit(const NilTermPtr& node) {
    visit0(node->sort);
}

void DummyVisitor0::visit(const SortedVariablePtr& node) {
    visit0(node->sort);
}

void DummyVisitor0::visit(const VariableBindingPtr& node) {
    visit0(node->term);
}

