#include "ast_term.h"

#include <sstream>

using namespace std;
using namespace smtlib::ast;

/* ================================== QualifiedTerm =================================== */

void QualifiedTerm::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string QualifiedTerm::toString() {
    stringstream ss;
    ss << "(" << identifier->toString() << " ";

    for (size_t i = 0, sz = terms.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << terms[i]->toString();
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

        ss << bindings[i]->toString();
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

        ss << bindings[i]->toString();
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

        ss << bindings[i]->toString();
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
