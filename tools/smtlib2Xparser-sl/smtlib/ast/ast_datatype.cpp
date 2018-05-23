#include "ast_datatype.h"

#include <sstream>

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

/* ================================= SortDeclaration ================================== */

void SortDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SortDeclaration::toString() {
    stringstream ss;
    ss << "(" << symbol->toString() << " " << arity->toString() << ")";
    return ss.str();
}

/* =============================== SelectorDeclaration ================================ */

void SelectorDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SelectorDeclaration::toString() {
    stringstream ss;
    ss << "(" << symbol->toString() << " " << sort->toString() << ")";
    return ss.str();
}

/* =============================== ConstructorDeclaration ============================== */

void ConstructorDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string ConstructorDeclaration::toString() {
    stringstream ss;
    ss << "(" << symbol->toString();

    for (const auto& sel : selectors) {
        ss << " " << sel->toString();
    }

    ss << ")";
    return ss.str();
}

/* ================================ DatatypeDeclaration =============================== */

void SimpleDatatypeDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SimpleDatatypeDeclaration::toString() {
    stringstream ss;
    ss << "(";

    for (size_t i = 0, sz = constructors.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << constructors[i]->toString();
    }

    ss << ")";
    return ss.str();
}

/* =========================== ParametricDatatypeDeclaration ========================== */

void ParametricDatatypeDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string ParametricDatatypeDeclaration::toString() {
    stringstream ss;
    ss << "(par (";

    for (size_t i = 0, sz = parameters.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << parameters[i]->toString();
    }

    ss << ") (";

    for (size_t i = 0, sz = constructors.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << constructors[i]->toString();
    }

    ss << "))";
    return ss.str();
}
