#include "sep_pp_slcomp14.h"

#include "sep/sep_identifier.h"
#include "sep/sep_term.h"
#include "sep/sep_command.h"
#include "sep/sep_script.h"
#include "sep/sep_s_expr.h"
#include "util/global_values.h"
#include "util/error_messages.h"

#include <iostream>
#include <unordered_map>

#define TAB 4

using namespace std;
using namespace smtlib::sep;

void Pp_SLCOMP14::visit(const SimpleAttributePtr& node) {
    // NB: not used
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored SimpleAttribute");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const SExpressionAttributePtr& node) {
    visit0(node->value);
    this->ret = true;
}

void Pp_SLCOMP14::visit(const SymbolAttributePtr& node) {
    // NB: not used
    // TRANSLATED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored SymbolAttribute");
    std::cout << node->value;
    this->ret = false;
}

void Pp_SLCOMP14::visit(const BooleanAttributePtr& node) {
    // NB: not used
    // TRANSLATED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored BooleanAttribute");
    std::cout << node->toString();
    this->ret = false;
}

void Pp_SLCOMP14::visit(const NumeralAttributePtr& node) {
    // NB: not used in SL-COMP'14
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored NumeralAttribute");
    std::cout << node->toString();
    this->ret = false;
}

void Pp_SLCOMP14::visit(const DecimalAttributePtr& node) {
    // NB: not used in SL-COMP'14
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored DecimalAttribute");
    std::cout << node->toString();
    this->ret = false;
}

void Pp_SLCOMP14::visit(const StringAttributePtr& node) {
    // NB: not used in SL-COMP'14
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored DecimalAttribute");
    std::cout << node->toString();
    this->ret = false;
}

void Pp_SLCOMP14::visit(const TheoriesAttributePtr& node) {
    // NB: not used in SL-COMP'14
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored TheoriesAttribute");
    std::cout << ";; Ignored " << node->toString();
    this->ret = false;
}

void Pp_SLCOMP14::visit(const SortsAttributePtr& node) {
    visit0(node->declarations);
    this->ret = true;
}

void Pp_SLCOMP14::visit(const FunsAttributePtr& node) {
    visit0(node->declarations);
    this->ret = true;
}

void Pp_SLCOMP14::visit(const SymbolPtr& node) {
    std::cout << node->value;
    this->ret = true;
}

void Pp_SLCOMP14::visit(const KeywordPtr& node) {
    std::cout << node->value;
    this->ret = true;
}

void Pp_SLCOMP14::visit(const MetaSpecConstantPtr& node) {
    // NB: not used in SL-COMP'14
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored MetaSpecConstant");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const BooleanValuePtr& node) {
    // NB: not used in SL-COMP'14
    // Translated
    Logger::error("Sep::Pp_slcomp14::visit()", "Not supported BooleanValue");
    std::cout << node->toString();
    this->ret = false;
}

void Pp_SLCOMP14::visit(const PropLiteralPtr& node) {
    // NB: not used in SL-COMP'14
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored PropLiteral");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const AssertCommandPtr& node) {
    std::cout << std::endl << "(assert ";
    this->nesting++;
    visit0(node->term);
    this->nesting--;
    std::cout << std::endl << " )" << std::endl;
    this->ret = true;
}

void Pp_SLCOMP14::visit(const CheckSatCommandPtr& node) {
    std::cout << node->toString() << std::endl;
    this->ret = true;
}

void Pp_SLCOMP14::visit(const CheckSatAssumCommandPtr& node) {
    // NB: not used in SL-COMP'14
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored CheckSatAssum");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const DeclareConstCommandPtr& node) {
    // NB: Constant declaration is SL-COMP'18 corresponds to 
    // null-ary function declaration in SL-COMP'14
    std::cout << "(declare-fun " << node->name << " () ";
    std::cout << node->sort->toString() << ")" << std::endl;
    this->ret = true;
}

void Pp_SLCOMP14::visit(const DeclareDatatypeCommandPtr& node) {
    // NB: declare-datatype used for heap cells
    // translate only declaration to extract selectors and 
    // register constructors
    std::cout << ";; Datatype " << node->name << std::endl;
    this->sortname = node->name;
    this->nesting = 0;
    visit0(node->declaration);
    this->sortname = "";
    this->nesting = 0;
    this->ret = true;
}

void Pp_SLCOMP14::visit(const DeclareDatatypesCommandPtr& node) {
    // NB: declare-datatypes used for heap cells
    // translate only declaration, but set sort name before it
    for (int i = 0; i < node->sorts.size(); i++) {
        this->sortname = node->sorts.at(i)->name;
        std::cout << ";; Declare cell type " << this->sortname << std::endl;
        visit0(node->declarations.at(i));
        std::cout << std::endl;
    }
    this->ret = true;
}

void Pp_SLCOMP14::visit(const DeclareFunCommandPtr& node) {
    // NB: function declaration is not useful for SL-COMP'18
    // IGNORE
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored DeclareFun");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const DeclareSortCommandPtr& node) {
    // NB: used for references, translated as it is
    if (node->arity == 0
            && node->name.compare(0, 3, std::string{"Ref"}) != 0) {
        Logger::error("Sep::Pp_slcomp14::visit()", "Ignored DeclareSort");
        std::cout << ";; IGNORE sort declaration " << node->name << std::endl;
    } else
        std::cout << node->toString() << std::endl;
    this->ret = true;
}

void Pp_SLCOMP14::visit(const DeclareHeapCommandPtr& node) {
    // IGNORE this command
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored DeclareHeap");
    std::cout << ";; IGNORE declare-heap " << std::endl;
    this->ret = false;
}

void Pp_SLCOMP14::visit(const DefineFunCommandPtr& node) {
    // NB: not used, only recursive functions
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored DefineFun");
    std::cout << ";; IGNORE define-fun " << std::endl;
    this->ret = false;
}

void Pp_SLCOMP14::visit(const DefineFunRecCommandPtr& node) {
    // NB: used to define predicates in SL-COMP'18
    this->nesting = 0;
    visit0(node->definition);
    this->nesting = 0;
    this->ret = true;
}

void Pp_SLCOMP14::visit(const DefineFunsRecCommandPtr& node) {
    // NB: used to define predicates in SL-COMP'18
    bool oldArg = this->inpred;
    this->inpred = true;
    // print in any order
    for (int i = 0; i < node->declarations.size(); i++) {
        // TODO: factorize with above   
        this->nesting = 0;
        std::cout << "(define-fun ";
        // - print declare signature without return type
        visit0(node->declarations.at(i));
        // - print return type
        std::cout << " Space " << std::endl;
        this->nesting++;
        // - print body
        std::cout << std::string(this->nesting * TAB, ' ') << "(tospace ";
        this->nesting++;
        visit0(node->bodies.at(i));
        this->nesting--;
        std::cout << std::endl;
        std::cout << std::string(this->nesting * TAB, ' ') << ")" << std::endl;
        std::cout << ")" << std::endl;
    }
    this->nesting = 0;
    this->inpred = oldArg;
    this->ret = true;
}

void Pp_SLCOMP14::visit(const DefineSortCommandPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored DefineSort");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const EchoCommandPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored Echo");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const ExitCommandPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored Exit");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const GetAssertsCommandPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored GetAsserts");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const GetAssignsCommandPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored GetAssigns");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const GetInfoCommandPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored GetInfo");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const GetModelCommandPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored GetModel");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const GetOptionCommandPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored GetOption");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const GetProofCommandPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored GetProof");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const GetUnsatAssumsCommandPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored GetUnsatAssums");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const GetUnsatCoreCommandPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored GetUnsatCore");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const GetValueCommandPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored GetValue");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const PopCommandPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored Pop");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const PushCommandPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored Push");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const ResetCommandPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored Reset");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const ResetAssertsCommandPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored ResetAsserts");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const SetInfoCommandPtr& node) {
    std::cout << node->toString() << std::endl;
    this->ret = true;
}

void Pp_SLCOMP14::visit(const SetLogicCommandPtr& node) {
std:
    string logic = node->logic;
    if ((logic.compare(std::string{"QF_SHLS"}) == 0)
        || (logic.compare(std::string{"QF_SHLID"}) == 0)
        || (logic.compare(std::string{"QF_SHID"}) == 0)) {
        std::cout << "(set-logic QF_S)" << std::endl;
        this->ret = true;
    } else {
        Logger::error("Sep::Pp_slcomp14::visit()", "Ignore SetLogic");
        std::cerr << logic << std::endl;
        this->ret = false;
    }
}

void Pp_SLCOMP14::visit(const SetOptionCommandPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored SetOption");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const SortDeclarationPtr& node) {
    // NB: used in SL-COMP'18 to define datatypes
    // do not translate into a sort by use instead Ref to this sort
    // introduced by declare-sort
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignore SortDeclaration");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const SelectorDeclarationPtr& node) {
    // NB: used in SL-COMP'18 to define datatypes
    // visit to translate fields as functions
    // We suppose that the selector belongs to this->sortname
    std::cout << "(declare-fun " << node->name << " () ";
    std::cout << "(Field Ref" << this->sortname << " " << node->sort->toString();
    std::cout << ") )" << std::endl;
    this->ret = true;
}

void Pp_SLCOMP14::visit(const ConstructorDeclarationPtr& node) {
    // NB: the constructor is not used in SL-COMP'14 format,
    // but shall be kept for translation of 'pto' terms
    map_cons[node->name] = node->selectors;
    visit0(node->selectors);
    this->ret = true;
}

void Pp_SLCOMP14::visit(const SimpleDatatypeDeclarationPtr& node) {
    visit0(node->constructors);
    this->ret = true;
}

void Pp_SLCOMP14::visit(const ParametricDatatypeDeclarationPtr& node) {
    // NB: not used in SL-COMP'18 to define datatypes
    // do not translate into a sort by use instead Ref to this sort
    // introduced by declare-sort
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignore ParametricDatatypeDeclaration");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const FunctionDeclarationPtr& node) {
    // TODO: check node->sort is Bool
    // - print name
    std::cout << node->name;
    // - print parameters
    std::cout << " (";
    this->nesting++;
    visit0(node->parameters);
    this->nesting--;
    std::cout << ") " << std::endl;
    this->ret = true;
}

void Pp_SLCOMP14::visit(const FunctionDefinitionPtr& node) {
    bool oldArg = this->inpred;
    this->inpred = true;
    this->nesting = 0;
    std::cout << "(define-fun ";
    // - print declare signature without return type
    visit0(node->signature);
    // - print return type
    std::cout << std::string(2 * TAB, ' ') << "Space " << std::endl;
    // - print body
    this->nesting += 1;
    std::cout << std::string(this->nesting*TAB, ' ') << "(tospace ";
    this->nesting++;
    visit0(node->body);
    this->nesting--;
    std::cout << std::endl << std::string(this->nesting*TAB, ' ') << ")";
    std::cout << std::endl << ")" << std::endl;
    this->inpred = oldArg;
    this->ret = true;
}

void Pp_SLCOMP14::visit(const SimpleIdentifierPtr& node) {
    if (this->inpred)
        std::cout << "?";
    std::cout << node->toString();
    this->ret = true;
}

void Pp_SLCOMP14::visit(const QualifiedIdentifierPtr& node) {
    if (this->inpred) // inpred
        std::cout << "?";
    std::cout << node->toString();
    this->ret = true;
}

void Pp_SLCOMP14::visit(const DecimalLiteralPtr& node) {
    // NB: not used, but translated
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored decimal");
    std::cout << node->toString();
    this->ret = false;
}

void Pp_SLCOMP14::visit(const NumeralLiteralPtr& node) {
    // NB: not used, but translated
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored numeral");
    std::cout << node->toString();
    this->ret = false;
}

void Pp_SLCOMP14::visit(const StringLiteralPtr& node) {
    // NB: not used, but translated
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored string");
    std::cout << node->toString();
    this->ret = false;
}

void Pp_SLCOMP14::visit(const LogicPtr& node) {
}

void Pp_SLCOMP14::visit(const TheoryPtr& node) {
}

void Pp_SLCOMP14::visit(const ScriptPtr& node) {
    visit0(node->commands);
    this->ret = true;
}

void Pp_SLCOMP14::visit(const QualifiedConstructorPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored QualifiedConstructor");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const QualifiedPatternPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored QualifiedPattern");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const MatchCasePtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored MatchCasePtr");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const CompSExpressionPtr& node) {
    // TODO
    visit0(node->expressions);
    this->ret = true;
}

void Pp_SLCOMP14::visit(const SortPtr& node) {
    // NB translated when needed
    this->ret = true;
}

void Pp_SLCOMP14::visit(const SortSymbolDeclarationPtr& node) {
    // NB: used in SL-COMP'18 for references
    // check arity 0 and start with 'Ref'
    if ((node->arity == 0) &&
            (node->identifier->name.compare(0, 3, std::string{"Ref"}) == 0)) {
        std::cout << node->toString() << std::endl;
        this->ret = true;
    } else {
        Logger::error("Sep::Pp_slcomp14::visit()", "Ignored SortSymbolDeclaration");
        std::cout << ";; " << node->toString() << std::endl;
        this->ret = false;
    }
}

void Pp_SLCOMP14::visit(const SpecConstFunDeclarationPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored SpecConstFunDeclaration");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const MetaSpecConstFunDeclarationPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored MetaSpecConstFunDeclaration");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const SimpleFunDeclarationPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored SimpleFunDeclaration");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const ParametricFunDeclarationPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored ParametricFunDeclaration");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const QualifiedTermPtr& node) {
    std::string id = node->identifier->toString();
    std::vector<TermPtr>& terms = node->terms;
    // if empty list of terms, then direct translation
    if (terms.size() == 0) {
        std::cout << id;
        this->ret = true;
        return;
    }
    // if id is a constructor, change to a ref (if unary constructor) or sref
    auto search = map_cons.find(id);
    if (search != map_cons.end()) {
        // it is a constructor 
        auto flist = search->second;
        if (flist.size() > 1)
            std::cout << "(sref ";
        for (int i = 0; i < flist.size(); i++) {
            std::cout << "(ref " << flist.at(i)->name << " ";
            visit0(terms.at(i));
            std::cout << ") ";
        }
        if (flist.size() > 1)
            std::cout << ") ";
        this->ret = true;
        return;
    }

    // it is a simple term
    std::cout << "(" << id;
    for (const auto& term : terms) {
        std::cout << " ";
        visit0(term);
    }
    std::cout << ") ";
    this->ret = true;
}

void Pp_SLCOMP14::visit(const LetTermPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored LetTerm");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const ForallTermPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored ForallTerm");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const ExistsTermPtr& node) {
    // NB: exists is in predicate definition and in formulas
    // only if inpred the biders are prefixed with '?'
    bool inspace = this->inspace;
    //std::cout << std::string(TAB*this->nesting, ' ');
    if (this->inspace) {
        std::cout << "(tobool ";
        this->inspace = false;
    }
    std::cout << "(exists (";
    visit0(node->bindings);
    std::cout << ") " << std::endl;
    this->nesting++;
    std::cout << std::string(TAB * this->nesting, ' ');
    visit0(node->term);
    this->nesting--;
    std::cout << std::endl << std::string(TAB * this->nesting, ' ');
    std::cout << ") ";
    if (inspace) {
        std::cout << ") ";
    }
    this->inspace = inspace;
}

void Pp_SLCOMP14::visit(const MatchTermPtr& node) {
    // NB: not used in SL-COMP'18
    // IGNORED
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored MatchTerm");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const AnnotatedTermPtr& node) {
    visit0(node->term);
    this->ret = true;
}

void Pp_SLCOMP14::visit(const TrueTermPtr& node) {
    // NB: no boolean values in SL-COMP'14
    // but accepted if !inspace
    if (this->inspace)
        std::cout << "junk ";
    else
        std::cout << "true ";
    this->ret = true;
}

void Pp_SLCOMP14::visit(const FalseTermPtr& node) {
    // NB: no boolean values in SL-COMP'14
    // but accepted if !inspace
    if (this->inspace)
        Logger::error("Sep::Pp_slcomp14::visit()", "Ignored FalseTerm");
    std::cout << "false ";
    this->ret = true;
}

void Pp_SLCOMP14::visit(const NotTermPtr& node) {
    // NB: 'not' used at any level in SL-COMP'18 
    // and only at upper level in SL-COMP'14
    if (this->inspace) {
        Logger::error("Sep::Pp_slcomp14::visit()", "Ignored NotTerm in Space");
        this->ret = false;
        return;
    }
    // !inspace
    std::cout << "(not ";
    visit0(node->term);
    std::cout << " )";
    this->ret = true;
    this->inspace = false;
}

void Pp_SLCOMP14::visit(const ImpliesTermPtr& node) {
    // NB: 'implies' used at any level in SL-COMP'18 
    // and not used in SL-COMP'14
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored ImpliesTerm");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const AndTermPtr& node) {
    // NB: 'and' shall be used in boolean mode in SL-COMP'14
    bool inspace = this->inspace;
    // std::cout << std::string(TAB*this->nesting, ' ');
    if (inspace) {
        this->inspace = false;
        std::cout << "(tospace ";
    }
    std::cout << "(and ";
    this->nesting++;
    for (const auto& term : node->terms) {
        std::cout << std::endl << std::string(TAB * this->nesting, ' ');
        visit0(term);
    }
    this->nesting--;
    std::cout << std::endl << std::string(TAB * this->nesting, ' ');
    std::cout << ")";
    if (inspace)
        std::cout << ") ";
    this->inspace = inspace;
    this->ret = true;
}

void Pp_SLCOMP14::visit(const OrTermPtr& node) {
    // NB: 'or' shall be used in boolean mode in SL-COMP'14
    // and inpred only!
    bool inpred = this->inpred;
    // std::cout << std::string(TAB*this->nesting, ' ');
    if (!inpred) {
        Logger::error("Sep::Pp_slcomp14::visit()", "Ignored OrTerm not in predicate");
        this->ret = false;
        return;
    }
    bool inspace = this->inspace;
    if (inspace) {
        this->inspace = false;
        std::cout << "(tospace ";
    }
    std::cout << "(or ";
    this->nesting++;
    for (const auto& term : node->terms) {
        std::cout << std::endl << std::string(TAB * this->nesting, ' ');
        visit0(term);
    }
    this->nesting--;
    std::cout << std::endl << std::string(TAB * this->nesting, ' ');
    std::cout << ") ";
    if (inspace)
        std::cout << ") ";
    this->inspace = inspace;
    this->ret = true;
}

void Pp_SLCOMP14::visit(const XorTermPtr& node) {
    // NB: 'xor' used at any level in SL-COMP'18 
    // and not used in SL-COMP'14
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored XorTerm");
    this->ret = false;
    bool sorted = true;
}

void Pp_SLCOMP14::visit(const EqualsTermPtr& node) {
    // NB: '=' shall be used in boolean mode in SL-COMP'14
    bool inspace = this->inspace;
    if (inspace) {
        this->inspace = false;
        std::cout << "(tospace ";
    }
    std::cout << "(= ";
    for (const auto& term : node->terms) {
        visit0(term);
        std::cout << " "; // << std::endl;
    }
    std::cout << " )";
    if (inspace)
        std::cout << ") ";
    this->inspace = inspace;
    this->ret = true;
}

void Pp_SLCOMP14::visit(const DistinctTermPtr& node) {
    // NB: '=' shall be used in boolean mode in SL-COMP'14
    bool inspace = this->inspace;
    if (inspace) {
        this->inspace = false;
        std::cout << "(tospace ";
    }
    std::cout << "(distinct ";
    for (const auto& term : node->terms) {
        visit0(term);
        std::cout << " "; // << std::endl;
    }
    std::cout << " )";
    if (inspace)
        std::cout << ") ";
    this->inspace = inspace;
    this->ret = true;
}

void Pp_SLCOMP14::visit(const IteTermPtr& node) {
    // NB: 'ite' used at any level in SL-COMP'18 
    // and not used in SL-COMP'14
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored IteTerm");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const EmpTermPtr& node) {
    // NB: 'emp' used inspace only
    if (!this->inspace) {
        std::cout << "(tobool ";
    }
    std::cout << "emp ";
    if (!this->inspace) {
        std::cout << ") ";
    }
    this->ret = true;
}

void Pp_SLCOMP14::visit(const SepTermPtr& node) {
    // NB: 'sep' used inspace only
    bool inspace = this->inspace;
    if (!inspace) {
        std::cout << "(tobool ";
        this->inspace = true;
    }
    std::cout << "(ssep ";
    this->nesting++;
    for (const auto& term : node->terms) {
        std::cout << std::endl << std::string(TAB * this->nesting, ' ');
        visit0(term);
    }
    this->nesting--;
    std::cout << std::endl << std::string(TAB * this->nesting, ' ') << ") ";
    if (!inspace) {
        std::cout << ") ";
    }
    this->inspace = inspace;
    this->ret = true;
}

void Pp_SLCOMP14::visit(const WandTermPtr& node) {
    // NB: 'wand' not used in SL-COMP'14
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored WandTerm");
    this->ret = false;
}

void Pp_SLCOMP14::visit(const PtoTermPtr& node) {
    // NB: 'pto' used inspace only
    bool inspace = this->inspace;
    if (!inspace) {
        std::cout << "(tobool ";
        this->inspace = true;
    }
    std::cout << "(pto ";

    visit0(node->leftTerm);
    std::cout << std::endl << std::string(TAB * (this->nesting + 1), ' ');
    visit0(node->rightTerm);
    std::cout << std::endl << std::string(TAB * this->nesting, ' ') << ") ";

    if (!inspace) {
        std::cout << ") ";
    }
    this->inspace = inspace;
    this->ret = true;
}

void Pp_SLCOMP14::visit(const NilTermPtr& node) {
    // NB: 'nil' not need to be typed in SL-COMP'14
    std::cout << "nil ";
    this->ret = true;
}

void Pp_SLCOMP14::visit(const SortedVariablePtr& node) {
    // NB: used in predicate parameters and exists
    // require '?' prefix
    std::cout << "(?" << node->name << " " << node->sort->toString() << ") ";
    this->ret = true;
}

void Pp_SLCOMP14::visit(const VariableBindingPtr& node) {
    // NB: 'let' not used in SL-COMP'14
    Logger::error("Sep::Pp_slcomp14::visit()", "Ignored VariableBinding");
    this->ret = false;
}

