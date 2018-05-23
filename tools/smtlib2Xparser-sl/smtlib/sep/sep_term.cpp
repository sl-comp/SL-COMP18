#include "sep_term.h"

#include <sstream>

using namespace std;
using namespace smtlib::sep;

/* ================================== QualifiedTerm =================================== */

void QualifiedTerm::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string QualifiedTerm::toString() {
    stringstream ss;
    ss << "(" << identifier->toString();

    for (const auto& term : terms) {
        ss << " " << term->toString();
    }

    ss << ")";
    return ss.str();
}

/* ===================================== LetTerm ====================================== */

void LetTerm::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string LetTerm::toString() {
    stringstream ss;
    ss << "(let (";

    for (size_t i = 0, sz = bindings.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << "(" << bindings[i]->toString() << ")";
    }

    ss << ") " << term->toString() << ")";
    return ss.str();
}

/* ==================================== ForallTerm ==================================== */

void ForallTerm::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string ForallTerm::toString() {
    stringstream ss;
    ss << "(forall (";

    for (size_t i = 0, sz = bindings.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << "(" << bindings[i]->toString() << ")";
    }

    ss << ") " << term->toString() << ")";
    return ss.str();
}

/* ==================================== ExistsTerm ==================================== */

void ExistsTerm::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string ExistsTerm::toString() {
    stringstream ss;
    ss << "(exists (";

    for (size_t i = 0, sz = bindings.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << "(" << bindings[i]->toString() << ")";
    }

    ss << ") " << term->toString() << ")";
    return ss.str();
}

/* ==================================== MatchTerm ===================================== */

void MatchTerm::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string MatchTerm::toString() {
    stringstream ss;
    ss << "(match " << term->toString();

    for (const auto& caseIt : cases) {
        ss << " " << caseIt->toString();
    }

    ss << ")";
    return ss.str();
}

/* ================================== AnnotatedTerm =================================== */

void AnnotatedTerm::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string AnnotatedTerm::toString() {
    stringstream ss;
    ss << "( ! " << term->toString() << " ";

    for (size_t i = 0, sz = attributes.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << attributes[i]->toString();
    }

    ss << ")";
    return ss.str();
}

/* ===================================== TrueTerm ===================================== */

void TrueTerm::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string TrueTerm::toString() {
    return "true";
}

/* ==================================== FalseTerm ===================================== */

void FalseTerm::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string FalseTerm::toString() {
    return "false";
}

/* ===================================== NotTerm ====================================== */

void NotTerm::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string NotTerm::toString() {
    stringstream ss;
    ss << "(not " << term->toString() << ")";
    return ss.str();
}

/* =================================== ImpliesTerm ==================================== */

void ImpliesTerm::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string ImpliesTerm::toString() {
    stringstream ss;
    ss << "(=> ";

    for (size_t i = 0, sz = terms.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << terms[i]->toString();
    }

    ss << ")";
    return ss.str();
}

/* ===================================== AndTerm ====================================== */

void AndTerm::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string AndTerm::toString() {
    stringstream ss;
    ss << "(and ";

    for (size_t i = 0, sz = terms.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << terms[i]->toString();
    }

    ss << ")";
    return ss.str();
}

/* ====================================== OrTerm ====================================== */

void OrTerm::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string OrTerm::toString() {
    stringstream ss;
    ss << "(or ";

    for (size_t i = 0, sz = terms.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << terms[i]->toString();
    }

    ss << ")";
    return ss.str();
}

/* ===================================== XorTerm ====================================== */

void XorTerm::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string XorTerm::toString() {
    stringstream ss;
    ss << "(xor ";

    for (size_t i = 0, sz = terms.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << terms[i]->toString();
    }

    ss << ")";
    return ss.str();
}

/* ==================================== EqualsTerm ==================================== */

void EqualsTerm::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string EqualsTerm::toString() {
    stringstream ss;
    ss << "(= ";

    for (size_t i = 0, sz = terms.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << terms[i]->toString();
    }

    ss << ")";
    return ss.str();
}

/* =================================== DistinctTerm =================================== */

void DistinctTerm::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string DistinctTerm::toString() {
    stringstream ss;
    ss << "(distinct ";

    for (size_t i = 0, sz = terms.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << terms[i]->toString();
    }

    ss << ")";
    return ss.str();
}

/* ===================================== IteTerm ====================================== */

void IteTerm::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string IteTerm::toString() {
    stringstream ss;
    ss << "(ite " << testTerm->toString() << " "
       << thenTerm->toString() << " " << elseTerm->toString() << ")";
    return ss.str();
}


/* ===================================== EmpTerm ====================================== */

void EmpTerm::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string EmpTerm::toString() {
    stringstream ss;

    if(locSort || dataSort)
        ss << "(_ ";

    ss << "emp";

    if(locSort)
        ss << " " << locSort->toString();

    if(dataSort)
        ss << " " << dataSort->toString();

    if(locSort || dataSort)
        ss << ")";

    return ss.str();
}

/* ===================================== SepTerm ====================================== */

void SepTerm::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SepTerm::toString() {
    stringstream ss;
    ss << "(sep ";

    for (size_t i = 0, sz = terms.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << terms[i]->toString();
    }

    ss << ")";
    return ss.str();
}

/* ===================================== WandTerm ===================================== */

void WandTerm::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string WandTerm::toString() {
    stringstream ss;
    ss << "(wand ";

    for (size_t i = 0, sz = terms.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << terms[i]->toString();
    }

    ss << ")";
    return ss.str();
}

/* ===================================== PtoTerm ====================================== */

void PtoTerm::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string PtoTerm::toString() {
    stringstream ss;
    ss << "(pto " << leftTerm->toString() << " " << rightTerm->toString() << ")";
    return ss.str();
}

/* ===================================== NilTerm ====================================== */

void NilTerm::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string NilTerm::toString() {
    if(sort) {
        stringstream ss;
        ss << "(as nil " << sort->toString() << ")";
        return ss.str();
    } else {
        return "nil";
    }
}
