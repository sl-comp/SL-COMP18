#include "smtlib-glue.h"

#include "ast/ast_attribute.h"
#include "ast/ast_basic.h"
#include "ast/ast_command.h"
#include "ast/ast_datatype.h"
#include "ast/ast_fun.h"
#include "ast/ast_identifier.h"
#include "ast/ast_interfaces.h"
#include "ast/ast_literal.h"
#include "ast/ast_logic.h"
#include "ast/ast_match.h"
#include "ast/ast_s_expr.h"
#include "ast/ast_script.h"
#include "ast/ast_sort.h"
#include "ast/ast_symbol_decl.h"
#include "ast/ast_term.h"
#include "ast/ast_theory.h"
#include "ast/ast_variable.h"
#include "parser/smtlib_parser.h"

#include <iostream>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

unordered_map<smtlib::ast::Node*, smtlib::ast::NodePtr> smtlib_nodemap;

template<class T>
shared_ptr<T> share(AstPtr nakedPtr) {
    return dynamic_pointer_cast<T>(smtlib_nodemap[nakedPtr]);
}

template<>
SpecConstantPtr share(AstPtr nakedPtr) {
    NumeralLiteralPtr option1 = dynamic_pointer_cast<NumeralLiteral>(smtlib_nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    DecimalLiteralPtr option2 = dynamic_pointer_cast<DecimalLiteral>(smtlib_nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    StringLiteralPtr option3 = dynamic_pointer_cast<StringLiteral>(smtlib_nodemap[nakedPtr]);
    if (option3) {
        return option3->shared_from_this();
    }

    throw;
}

template<>
CommandPtr share(AstPtr nakedPtr) {
    AssertCommandPtr option1 = dynamic_pointer_cast<AssertCommand>(smtlib_nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    CheckSatCommandPtr option2 = dynamic_pointer_cast<CheckSatCommand>(smtlib_nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    CheckUnsatCommandPtr option2b = dynamic_pointer_cast<CheckUnsatCommand>(smtlib_nodemap[nakedPtr]);
    if (option2b) {
        return option2b->shared_from_this();
    }

    CheckSatAssumCommandPtr option3 = dynamic_pointer_cast<CheckSatAssumCommand>(smtlib_nodemap[nakedPtr]);
    if (option3) {
        return option3->shared_from_this();
    }

    DeclareConstCommandPtr option4 = dynamic_pointer_cast<DeclareConstCommand>(smtlib_nodemap[nakedPtr]);
    if (option4) {
        return option4->shared_from_this();
    }

    DeclareFunCommandPtr option5 = dynamic_pointer_cast<DeclareFunCommand>(smtlib_nodemap[nakedPtr]);
    if (option5) {
        return option5->shared_from_this();
    }

    DeclareSortCommandPtr option6 = dynamic_pointer_cast<DeclareSortCommand>(smtlib_nodemap[nakedPtr]);
    if (option6) {
        return option6->shared_from_this();
    }

    DeclareHeapCommandPtr option6b = dynamic_pointer_cast<DeclareHeapCommand>(smtlib_nodemap[nakedPtr]);
    if (option6b) {
        return option6b->shared_from_this();
    }

    DefineFunCommandPtr option7 = dynamic_pointer_cast<DefineFunCommand>(smtlib_nodemap[nakedPtr]);
    if (option7) {
        return option7->shared_from_this();
    }

    DefineFunRecCommandPtr option8 = dynamic_pointer_cast<DefineFunRecCommand>(smtlib_nodemap[nakedPtr]);
    if (option8) {
        return option8->shared_from_this();
    }

    DefineFunsRecCommandPtr option9 = dynamic_pointer_cast<DefineFunsRecCommand>(smtlib_nodemap[nakedPtr]);
    if (option9) {
        return option9->shared_from_this();
    }

    DefineSortCommandPtr option10 = dynamic_pointer_cast<DefineSortCommand>(smtlib_nodemap[nakedPtr]);
    if (option10) {
        return option10->shared_from_this();
    }

    EchoCommandPtr option11 = dynamic_pointer_cast<EchoCommand>(smtlib_nodemap[nakedPtr]);
    if (option11) {
        return option11->shared_from_this();
    }

    ExitCommandPtr option12 = dynamic_pointer_cast<ExitCommand>(smtlib_nodemap[nakedPtr]);
    if (option12) {
        return option12->shared_from_this();
    }

    SetOptionCommandPtr option13 = dynamic_pointer_cast<SetOptionCommand>(smtlib_nodemap[nakedPtr]);
    if (option13) {
        return option13->shared_from_this();
    }

    GetAssertsCommandPtr option14 = dynamic_pointer_cast<GetAssertsCommand>(smtlib_nodemap[nakedPtr]);
    if (option14) {
        return option14->shared_from_this();
    }

    GetAssignsCommandPtr option15 = dynamic_pointer_cast<GetAssignsCommand>(smtlib_nodemap[nakedPtr]);
    if (option15) {
        return option15->shared_from_this();
    }

    GetInfoCommandPtr option16 = dynamic_pointer_cast<GetInfoCommand>(smtlib_nodemap[nakedPtr]);
    if (option16) {
        return option16->shared_from_this();
    }

    GetModelCommandPtr option17 = dynamic_pointer_cast<GetModelCommand>(smtlib_nodemap[nakedPtr]);
    if (option17) {
        return option17->shared_from_this();
    }

    GetOptionCommandPtr option18 = dynamic_pointer_cast<GetOptionCommand>(smtlib_nodemap[nakedPtr]);
    if (option18) {
        return option18->shared_from_this();
    }

    GetProofCommandPtr option19 = dynamic_pointer_cast<GetProofCommand>(smtlib_nodemap[nakedPtr]);
    if (option19) {
        return option19->shared_from_this();
    }

    GetUnsatAssumsCommandPtr option20 = dynamic_pointer_cast<GetUnsatAssumsCommand>(smtlib_nodemap[nakedPtr]);
    if (option20) {
        return option20->shared_from_this();
    }

    GetUnsatCoreCommandPtr option21 = dynamic_pointer_cast<GetUnsatCoreCommand>(smtlib_nodemap[nakedPtr]);
    if (option21) {
        return option21->shared_from_this();
    }

    GetValueCommandPtr option22 = dynamic_pointer_cast<GetValueCommand>(smtlib_nodemap[nakedPtr]);
    if (option22) {
        return option22->shared_from_this();
    }

    PopCommandPtr option23 = dynamic_pointer_cast<PopCommand>(smtlib_nodemap[nakedPtr]);
    if (option23) {
        return option23->shared_from_this();
    }

    PushCommandPtr option24 = dynamic_pointer_cast<PushCommand>(smtlib_nodemap[nakedPtr]);
    if (option24) {
        return option24->shared_from_this();
    }

    ResetCommandPtr option25 = dynamic_pointer_cast<ResetCommand>(smtlib_nodemap[nakedPtr]);
    if (option25) {
        return option25->shared_from_this();
    }

    ResetAssertsCommandPtr option26 = dynamic_pointer_cast<ResetAssertsCommand>(smtlib_nodemap[nakedPtr]);
    if (option26) {
        return option26->shared_from_this();
    }

    SetInfoCommandPtr option27 = dynamic_pointer_cast<SetInfoCommand>(smtlib_nodemap[nakedPtr]);
    if (option27) {
        return option27->shared_from_this();
    }

    SetLogicCommandPtr option28 = dynamic_pointer_cast<SetLogicCommand>(smtlib_nodemap[nakedPtr]);
    if (option28) {
        return option28->shared_from_this();
    }

    DeclareDatatypeCommandPtr option29 = dynamic_pointer_cast<DeclareDatatypeCommand>(smtlib_nodemap[nakedPtr]);
    if (option29) {
        return option29->shared_from_this();
    }

    DeclareDatatypesCommandPtr option30 = dynamic_pointer_cast<DeclareDatatypesCommand>(smtlib_nodemap[nakedPtr]);
    if (option30) {
        return option30->shared_from_this();
    }

    throw;
}

template<>
FunSymbolDeclarationPtr share(AstPtr nakedPtr) {
    SpecConstFunDeclarationPtr option6 = dynamic_pointer_cast<SpecConstFunDeclaration>(smtlib_nodemap[nakedPtr]);
    if (option6) {
        return option6->shared_from_this();
    }

    MetaSpecConstFunDeclarationPtr option7 = dynamic_pointer_cast<MetaSpecConstFunDeclaration>(
            smtlib_nodemap[nakedPtr]);
    if (option7) {
        return option7->shared_from_this();
    }

    SimpleFunDeclarationPtr option8 = dynamic_pointer_cast<SimpleFunDeclaration>(smtlib_nodemap[nakedPtr]);
    if (option8) {
        return option8->shared_from_this();
    }

    ParametricFunDeclarationPtr option9 = dynamic_pointer_cast<ParametricFunDeclaration>(smtlib_nodemap[nakedPtr]);
    if (option9) {
        return option9->shared_from_this();
    }

    throw;
}

template<>
ConstructorPtr share(AstPtr nakedPtr) {
    SymbolPtr option1 = dynamic_pointer_cast<Symbol>(smtlib_nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    QualifiedConstructorPtr option2 = dynamic_pointer_cast<QualifiedConstructor>(smtlib_nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    throw;
}

template<>
PatternPtr share(AstPtr nakedPtr) {
    if (dynamic_cast<Constructor*>(nakedPtr)) {
        return share<Constructor>(nakedPtr);
    }

    SymbolPtr option1 = dynamic_pointer_cast<Symbol>(smtlib_nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    QualifiedPatternPtr option2 = dynamic_pointer_cast<QualifiedPattern>(smtlib_nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    throw;
}

template<>
DatatypeDeclarationPtr share(AstPtr nakedPtr) {
    SimpleDatatypeDeclarationPtr option1 =
            dynamic_pointer_cast<SimpleDatatypeDeclaration>(smtlib_nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    ParametricDatatypeDeclarationPtr option2 =
            dynamic_pointer_cast<ParametricDatatypeDeclaration>(smtlib_nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    throw;
}

template<>
AttributeValuePtr share(AstPtr nakedPtr) {
    BooleanValuePtr option1 = dynamic_pointer_cast<BooleanValue>(smtlib_nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    if (dynamic_cast<SpecConstant*>(nakedPtr)) {
        return share<SpecConstant>(nakedPtr);
    }

    SortSymbolDeclarationPtr option5 = dynamic_pointer_cast<SortSymbolDeclaration>(smtlib_nodemap[nakedPtr]);
    if (option5) {
        return option5->shared_from_this();
    }

    if (dynamic_cast<FunSymbolDeclaration*>(nakedPtr)) {
        return share<FunSymbolDeclaration>(nakedPtr);
    }

    SymbolPtr option10 = dynamic_pointer_cast<Symbol>(smtlib_nodemap[nakedPtr]);
    if (option10) {
        return option10->shared_from_this();
    }

    CompSExpressionPtr option11 = dynamic_pointer_cast<CompSExpression>(smtlib_nodemap[nakedPtr]);
    if (option11) {
        return option11->shared_from_this();
    }

    CompAttributeValuePtr option12 = dynamic_pointer_cast<CompAttributeValue>(smtlib_nodemap[nakedPtr]);
    if (option12) {
        return option12->shared_from_this();
    }

    throw;
}

template<>
SExpressionPtr share(AstPtr nakedPtr) {
    if (dynamic_cast<SpecConstant*>(nakedPtr)) {
        return share<SpecConstant>(nakedPtr);
    }

    SymbolPtr option4 = dynamic_pointer_cast<Symbol>(smtlib_nodemap[nakedPtr]);
    if (option4) {
        return option4->shared_from_this();
    }

    KeywordPtr option5 = dynamic_pointer_cast<Keyword>(smtlib_nodemap[nakedPtr]);
    if (option5) {
        return option5->shared_from_this();
    }

    CompSExpressionPtr option6 = dynamic_pointer_cast<CompSExpression>(smtlib_nodemap[nakedPtr]);
    if (option6) {
        return option6->shared_from_this();
    }

    throw;
}

template<>
IdentifierPtr share(AstPtr nakedPtr) {
    SimpleIdentifierPtr option1 = dynamic_pointer_cast<SimpleIdentifier>(smtlib_nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    QualifiedIdentifierPtr option2 = dynamic_pointer_cast<QualifiedIdentifier>(smtlib_nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    throw;
}

template<>
TermPtr share(AstPtr nakedPtr) {
    if (dynamic_cast<SpecConstant*>(nakedPtr)) {
        return share<SpecConstant>(nakedPtr);
    }

    if (dynamic_cast<Identifier*>(nakedPtr)) {
        return share<Identifier>(nakedPtr);
    }

    AnnotatedTermPtr option6 = dynamic_pointer_cast<AnnotatedTerm>(smtlib_nodemap[nakedPtr]);
    if (option6) {
        return option6->shared_from_this();
    }

    ExistsTermPtr option7 = dynamic_pointer_cast<ExistsTerm>(smtlib_nodemap[nakedPtr]);
    if (option7) {
        return option7->shared_from_this();
    }

    ForallTermPtr option8 = dynamic_pointer_cast<ForallTerm>(smtlib_nodemap[nakedPtr]);
    if (option8) {
        return option8->shared_from_this();
    }

    LetTermPtr option9 = dynamic_pointer_cast<LetTerm>(smtlib_nodemap[nakedPtr]);
    if (option9) {
        return option9->shared_from_this();
    }

    QualifiedTermPtr option10 = dynamic_pointer_cast<QualifiedTerm>(smtlib_nodemap[nakedPtr]);
    if (option10) {
        return option10->shared_from_this();
    }

    MatchTermPtr option11 = dynamic_pointer_cast<MatchTerm>(smtlib_nodemap[nakedPtr]);
    if (option11) {
        return option11->shared_from_this();
    }

    throw;
}

template<>
IndexPtr share(AstPtr nakedPtr) {
    NumeralLiteralPtr option1 = dynamic_pointer_cast<NumeralLiteral>(smtlib_nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    SymbolPtr option2 = dynamic_pointer_cast<Symbol>(smtlib_nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    throw;
}

//namespace smtlib {
//namespace ast {

class ParserInternalList {
private:
    vector<AstPtr> v;
public:
    template<class T>
    vector<shared_ptr<T>> unwrap() {
        vector<shared_ptr<T>> result;
        for (const auto& elem : v) {
            shared_ptr<T> ptr = share<T>(elem);
            result.push_back(ptr);
        }
        v.clear();
        return result;
    };

    inline void add(AstPtr item) {
        v.push_back(item);
    }
};

class ParserInternalPairList {
private:
    vector<pair<AstPtr, AstPtr>> v;
public:
    template<class T1, class T2>
    vector<pair<shared_ptr<T1>, shared_ptr<T2>>> unwrap() {
        vector<pair<shared_ptr<T1>, shared_ptr<T2>>> result;
        for (const auto& pair : v) {
            shared_ptr<T1> ptr1 = share<T1>(pair.first);
            shared_ptr<T1> ptr2 = share<T2>(pair.second);
            result.push_back(make_pair(ptr1, ptr2));
        }
        v.clear();
        return result;
    };

    inline void add(AstPtr item1, AstPtr item2) {
        v.push_back(make_pair(item1, item2));
    }
};
//}
//}

AstList ast_listCreate() {
    return new ParserInternalList();
}

void ast_listAdd(AstList list, AstPtr item) {
    list->add(item);
}

void ast_listDelete(AstList list) {
    delete list;
}

AstPairList ast_pairListCreate() {
    return new ParserInternalPairList();
}

void ast_pairListAdd(AstPairList list, AstPtr item1, AstPtr item2) {
    list->add(item1, item2);
}

void ast_pairListDelete(AstList list) {
    delete list;
}

void ast_print(AstPtr ptr) {
    cout << ptr->toString();
}

void ast_setAst(SmtPrsr parser, AstPtr ast) {
    if (parser && ast) {
        parser->setAst(smtlib_nodemap[ast]);
        smtlib_nodemap.clear();
    }
}

void ast_reportError(SmtPrsr parser,
                     int rowLeft, int colLeft,
                     int rowRight, int colRight,
                     const char* msg) {
    if (parser && msg) {
        parser->reportError(rowLeft, colLeft, rowRight, colRight, msg);
    }
}

void ast_setLocation(SmtPrsr parser, AstPtr ptr,
                     int rowLeft, int colLeft,
                     int rowRight, int colRight) {
    ptr->filename = parser->getFilename();
    ptr->rowLeft = rowLeft;
    ptr->colLeft = colLeft;
    ptr->rowRight = rowRight;
    ptr->colRight = colRight;
}

int ast_bool_value(AstPtr ptr) {
    BooleanValuePtr val = share<BooleanValue>(ptr);
    if (val) {
        return val->value;
    } else {
        return 2;
    }
}

// ast_attribute.h
AstPtr ast_newAttribute1(AstPtr keyword) {
    AttributePtr ptr = make_shared<Attribute>(std::move(share<Keyword>(keyword)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newAttribute2(AstPtr keyword, AstPtr attr_value) {
    AttributePtr ptr = make_shared<Attribute>(std::move(share<Keyword>(keyword)),
                                              std::move(share<AttributeValue>(attr_value)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newCompAttributeValue(AstList values) {
    CompAttributeValuePtr ptr =
            make_shared<CompAttributeValue>(std::move(values->unwrap<AttributeValue>()));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_basic.h
AstPtr ast_newSymbol(char const* value) {
    SymbolPtr ptr = make_shared<Symbol>(value);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newKeyword(char const* value) {
    KeywordPtr ptr = make_shared<Keyword>(value);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newMetaSpecConstant(int value) {
    MetaSpecConstantPtr ptr =
            make_shared<MetaSpecConstant>(static_cast<MetaSpecConstant::Type>(value));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newBooleanValue(int value) {
    BooleanValuePtr ptr = make_shared<BooleanValue>((bool) value);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newPropLiteral(AstPtr symbol, int negated) {
    PropLiteralPtr ptr =
            make_shared<PropLiteral>(std::move(share<Symbol>(symbol)), (bool) negated);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_command.h
AstPtr ast_newAssertCommand(AstPtr term) {
    AssertCommandPtr ptr = make_shared<AssertCommand>(share<Term>(term));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newCheckSatCommand() {
    CheckSatCommandPtr ptr = make_shared<CheckSatCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newCheckUnsatCommand() {
    CheckUnsatCommandPtr ptr = make_shared<CheckUnsatCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newCheckSatAssumCommand(AstList assumptions) {
    CheckSatAssumCommandPtr ptr =
            make_shared<CheckSatAssumCommand>(std::move(assumptions->unwrap<PropLiteral>()));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDeclareConstCommand(AstPtr symbol, AstPtr sort) {
    DeclareConstCommandPtr ptr =
            make_shared<DeclareConstCommand>(std::move(share<Symbol>(symbol)),
                                             std::move(share<Sort>(sort)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDeclareDatatypeCommand(AstPtr symbol, AstPtr declaration) {
    DeclareDatatypeCommandPtr ptr =
            make_shared<DeclareDatatypeCommand>(std::move(share<Symbol>(symbol)),
                                                std::move(share<DatatypeDeclaration>(declaration)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDeclareDatatypesCommand(AstList sorts, AstList declarations) {
    DeclareDatatypesCommandPtr ptr =
            make_shared<DeclareDatatypesCommand>(std::move(sorts->unwrap<SortDeclaration>()),
                                                 std::move(declarations->unwrap<DatatypeDeclaration>()));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDeclareFunCommand(AstPtr symbol, AstList params, AstPtr sort) {
    DeclareFunCommandPtr ptr = make_shared<DeclareFunCommand>(std::move(share<Symbol>(symbol)),
                                                              std::move(params->unwrap<Sort>()),
                                                              std::move(share<Sort>(sort)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDeclareSortCommand(AstPtr symbol, AstPtr arity) {
    DeclareSortCommandPtr ptr =
            make_shared<DeclareSortCommand>(std::move(share<Symbol>(symbol)),
                                            std::move(share<NumeralLiteral>(arity)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDeclareHeapCommand(AstPairList pairs) {
    DeclareHeapCommandPtr ptr =
            make_shared<DeclareHeapCommand>(std::move(pairs->unwrap<Sort, Sort>()));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDefineFunCommand(AstPtr definition) {
    DefineFunCommandPtr ptr =
            make_shared<DefineFunCommand>(std::move(share<FunctionDefinition>(definition)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDefineFunRecCommand(AstPtr definition) {
    DefineFunRecCommandPtr ptr =
            make_shared<DefineFunRecCommand>(std::move(share<FunctionDefinition>(definition)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDefineFunsRecCommand(AstList declarations, AstList bodies) {
    DefineFunsRecCommandPtr ptr =
            make_shared<DefineFunsRecCommand>(std::move(declarations->unwrap<FunctionDeclaration>()),
                                              std::move(bodies->unwrap<Term>()));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDefineSortCommand(AstPtr symbol, AstList params, AstPtr sort) {
    DefineSortCommandPtr ptr = make_shared<DefineSortCommand>(std::move(share<Symbol>(symbol)),
                                                              std::move(params->unwrap<Symbol>()),
                                                              std::move(share<Sort>(sort)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newEchoCommand(AstPtr msg) {
    EchoCommandPtr ptr = make_shared<EchoCommand>(share<StringLiteral>(msg)->value);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newExitCommand() {
    ExitCommandPtr ptr = make_shared<ExitCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetAssertsCommand() {
    GetAssertsCommandPtr ptr = make_shared<GetAssertsCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetAssignsCommand() {
    GetAssignsCommandPtr ptr = make_shared<GetAssignsCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetInfoCommand(AstPtr keyword) {
    GetInfoCommandPtr ptr = make_shared<GetInfoCommand>(std::move(share<Keyword>(keyword)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetModelCommand() {
    GetModelCommandPtr ptr = make_shared<GetModelCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetOptionCommand(AstPtr keyword) {
    GetOptionCommandPtr ptr = make_shared<GetOptionCommand>(std::move(share<Keyword>(keyword)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetProofCommand() {
    GetProofCommandPtr ptr = make_shared<GetProofCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetUnsatAssumsCommand() {
    GetUnsatAssumsCommandPtr ptr = make_shared<GetUnsatAssumsCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetUnsatCoreCommand() {
    GetUnsatCoreCommandPtr ptr = make_shared<GetUnsatCoreCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newGetValueCommand(AstList terms) {
    GetValueCommandPtr ptr = make_shared<GetValueCommand>(std::move(terms->unwrap<Term>()));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newPopCommand(AstPtr numeral) {
    PopCommandPtr ptr = make_shared<PopCommand>(std::move(share<NumeralLiteral>(numeral)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newPushCommand(AstPtr numeral) {
    PushCommandPtr ptr = make_shared<PushCommand>(std::move(share<NumeralLiteral>(numeral)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newResetCommand() {
    ResetCommandPtr ptr = make_shared<ResetCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newResetAssertsCommand() {
    ResetAssertsCommandPtr ptr = make_shared<ResetAssertsCommand>();
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSetInfoCommand(AstPtr info) {
    SetInfoCommandPtr ptr = make_shared<SetInfoCommand>(std::move(share<Attribute>(info)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSetLogicCommand(AstPtr logic) {
    SetLogicCommandPtr ptr = make_shared<SetLogicCommand>(std::move(share<Symbol>(logic)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSetOptionCommand(AstPtr option) {
    SetOptionCommandPtr ptr = make_shared<SetOptionCommand>(std::move(share<Attribute>(option)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

//ast_datatype.h
AstPtr ast_newSortDeclaration(AstPtr symbol, AstPtr numeral) {
    SortDeclarationPtr ptr =
            make_shared<SortDeclaration>(std::move(share<Symbol>(symbol)),
                                         std::move(share<NumeralLiteral>(numeral)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSelectorDeclaration(AstPtr symbol, AstPtr sort) {
    SelectorDeclarationPtr ptr =
            make_shared<SelectorDeclaration>(std::move(share<Symbol>(symbol)),
                                             std::move(share<Sort>(sort)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newConstructorDeclaration(AstPtr symbol, AstList selectors) {
    ConstructorDeclarationPtr ptr =
            make_shared<ConstructorDeclaration>(std::move(share<Symbol>(symbol)),
                                                std::move(selectors->unwrap<SelectorDeclaration>()));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSimpleDatatypeDeclaration(AstList constructors) {
    SimpleDatatypeDeclarationPtr ptr =
            make_shared<SimpleDatatypeDeclaration>(std::move(constructors->unwrap<ConstructorDeclaration>()));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newParametricDatatypeDeclaration(AstList params, AstList constructors) {
    ParametricDatatypeDeclarationPtr ptr =
            make_shared<ParametricDatatypeDeclaration>(std::move(params->unwrap<Symbol>()),
                                                       std::move(constructors->unwrap<ConstructorDeclaration>()));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_fun.h
AstPtr ast_newFunctionDeclaration(AstPtr symbol, AstList params, AstPtr sort) {
    FunctionDeclarationPtr ptr =
            make_shared<FunctionDeclaration>(std::move(share<Symbol>(symbol)),
                                             std::move(params->unwrap<SortedVariable>()),
                                             std::move(share<Sort>(sort)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newFunctionDefinition(AstPtr signature, AstPtr body) {
    FunctionDefinitionPtr ptr =
            make_shared<FunctionDefinition>(std::move(share<FunctionDeclaration>(signature)),
                                            std::move(share<Term>(body)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_identifier.h
AstPtr ast_newSimpleIdentifier1(AstPtr symbol) {
    SimpleIdentifierPtr ptr = make_shared<SimpleIdentifier>(std::move(share<Symbol>(symbol)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSimpleIdentifier2(AstPtr symbol, AstList indices) {
    SimpleIdentifierPtr ptr = make_shared<SimpleIdentifier>(std::move(share<Symbol>(symbol)),
                                                            std::move(indices->unwrap<Index>()));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newQualifiedIdentifier(AstPtr identifier, AstPtr sort) {
    QualifiedIdentifierPtr ptr =
            make_shared<QualifiedIdentifier>(std::move(share<SimpleIdentifier>(identifier)),
                                             std::move(share<Sort>(sort)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_literal.h
AstPtr ast_newNumeralLiteral(long value, unsigned int base) {
    NumeralLiteralPtr ptr = make_shared<NumeralLiteral>(value, base);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newDecimalLiteral(double value) {
    DecimalLiteralPtr ptr = make_shared<DecimalLiteral>(value);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newStringLiteral(char const* value) {
    StringLiteralPtr ptr = make_shared<StringLiteral>(value);
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_logic.h
AstPtr ast_newLogic(AstPtr name, AstList attributes) {
    LogicPtr ptr = make_shared<Logic>(std::move(share<Symbol>(name)),
                                      std::move(attributes->unwrap<Attribute>()));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_match.h
AstPtr ast_newQualifiedConstructor(AstPtr symbol, AstPtr sort) {
    QualifiedConstructorPtr ptr =
            make_shared<QualifiedConstructor>(std::move(share<Symbol>(symbol)),
                                              std::move(share<Sort>(sort)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newQualifiedPattern(AstPtr constructor, AstList symbols) {
    QualifiedPatternPtr ptr = make_shared<QualifiedPattern>(std::move(share<Constructor>(constructor)),
                                                            std::move(symbols->unwrap<Symbol>()));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newMatchCase(AstPtr pattern, AstPtr term) {
    MatchCasePtr ptr = make_shared<MatchCase>(std::move(share<Pattern>(pattern)),
                                              std::move(share<Term>(term)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_s_expr.h
AstPtr ast_newCompSExpression(AstList exprs) {
    CompSExpressionPtr ptr = make_shared<CompSExpression>(std::move(exprs->unwrap<SExpression>()));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_script.h
AstPtr ast_newScript(AstList cmds) {
    ScriptPtr ptr = make_shared<Script>(std::move(cmds->unwrap<Command>()));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_sort.h
AstPtr ast_newSort1(AstPtr identifier) {
    SortPtr ptr = make_shared<Sort>(std::move(share<SimpleIdentifier>(identifier)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSort2(AstPtr identifier, AstList params) {
    SortPtr ptr = make_shared<Sort>(std::move(share<SimpleIdentifier>(identifier)),
                                    std::move(params->unwrap<Sort>()));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_symbol_decl.h
AstPtr ast_newSortSymbolDeclaration(AstPtr identifier, AstPtr arity, AstList attributes) {
    SortSymbolDeclarationPtr ptr =
            make_shared<SortSymbolDeclaration>(std::move(share<SimpleIdentifier>(identifier)),
                                               std::move(share<NumeralLiteral>(arity)),
                                               std::move(attributes->unwrap<Attribute>()));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSpecConstFunDeclaration(AstPtr constant, AstPtr sort, AstList attributes) {
    SpecConstFunDeclarationPtr ptr =
            make_shared<SpecConstFunDeclaration>(std::move(share<SpecConstant>(constant)),
                                                 std::move(share<Sort>(sort)),
                                                 std::move(attributes->unwrap<Attribute>()));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newMetaSpecConstFunDeclaration(AstPtr constant, AstPtr sort, AstList attributes) {
    MetaSpecConstFunDeclarationPtr ptr =
            make_shared<MetaSpecConstFunDeclaration>(std::move(share<MetaSpecConstant>(constant)),
                                                     std::move(share<Sort>(sort)),
                                                     std::move(attributes->unwrap<Attribute>()));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newSimpleFunDeclaration(AstPtr identifier, AstList signature, AstList attributes) {
    SimpleFunDeclarationPtr ptr =
            make_shared<SimpleFunDeclaration>(std::move(share<SimpleIdentifier>(identifier)),
                                              std::move(signature->unwrap<Sort>()),
                                              std::move(attributes->unwrap<Attribute>()));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newParametricFunDeclaration(AstList params, AstPtr identifier, AstList signature, AstList attributes) {
    ParametricFunDeclarationPtr ptr =
            make_shared<ParametricFunDeclaration>(std::move(params->unwrap<Symbol>()),
                                                  std::move(share<SimpleIdentifier>(identifier)),
                                                  std::move(signature->unwrap<Sort>()),
                                                  std::move(attributes->unwrap<Attribute>()));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_term.h
AstPtr ast_newQualifiedTerm(AstPtr identifier, AstList terms) {
    QualifiedTermPtr ptr = make_shared<QualifiedTerm>(std::move(share<Identifier>(identifier)),
                                                      std::move(terms->unwrap<Term>()));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newLetTerm(AstList bindings, AstPtr term) {
    LetTermPtr ptr = make_shared<LetTerm>(std::move(bindings->unwrap<VariableBinding>()),
                                          std::move(share<Term>(term)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newForallTerm(AstList bindings, AstPtr term) {
    ForallTermPtr ptr = make_shared<ForallTerm>(std::move(bindings->unwrap<SortedVariable>()),
                                                std::move(share<Term>(term)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newExistsTerm(AstList bindings, AstPtr term) {
    ExistsTermPtr ptr = make_shared<ExistsTerm>(std::move(bindings->unwrap<SortedVariable>()),
                                                std::move(share<Term>(term)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newMatchTerm(AstPtr term, AstList cases) {
    MatchTermPtr ptr = make_shared<MatchTerm>(std::move(share<Term>(term)),
                                              std::move(cases->unwrap<MatchCase>()));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newAnnotatedTerm(AstPtr term, AstList attrs) {
    AnnotatedTermPtr ptr = make_shared<AnnotatedTerm>(std::move(share<Term>(term)),
                                                      std::move(attrs->unwrap<Attribute>()));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_theory.h
AstPtr ast_newTheory(AstPtr name, AstList attributes) {
    TheoryPtr ptr = make_shared<Theory>(std::move(share<Symbol>(name)),
                                        std::move(attributes->unwrap<Attribute>()));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// ast_variable.h
AstPtr ast_newSortedVariable(AstPtr symbol, AstPtr sort) {
    SortedVariablePtr ptr = make_shared<SortedVariable>(std::move(share<Symbol>(symbol)),
                                                        std::move(share<Sort>(sort)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}

AstPtr ast_newVariableBinding(AstPtr symbol, AstPtr term) {
    VariableBindingPtr ptr = make_shared<VariableBinding>(std::move(share<Symbol>(symbol)),
                                                          std::move(share<Term>(term)));
    smtlib_nodemap[ptr.get()] = ptr;
    return ptr.get();
}
