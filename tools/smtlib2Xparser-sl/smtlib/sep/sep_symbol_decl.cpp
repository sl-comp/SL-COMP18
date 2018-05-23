#include "sep_symbol_decl.h"
#include "sep_attribute.h"

#include <sstream>

using namespace std;
using namespace smtlib::sep;

/* =============================== SortSymbolDeclaration ============================== */

void SortSymbolDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SortSymbolDeclaration::toString() {
    stringstream ss;
    ss << "(" << identifier->toString() << " " << arity;

    for (const auto& attr : attributes) {
        ss << " " << attr->toString();
    }

    ss << ")";
    return ss.str();
}

/* ============================= SpecConstFunDeclaration ============================== */

void SpecConstFunDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SpecConstFunDeclaration::toString() {
    stringstream ss;
    ss << "(" << constant->toString() << " " << sort->toString();

    for (const auto& attr : attributes) {
        ss << " " << attr->toString();
    }

    ss << ")";
    return ss.str();
}

/* ========================== MetaSpecConstFunDeclaration =========================== */

void MetaSpecConstFunDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string MetaSpecConstFunDeclaration::toString() {
    stringstream ss;
    ss << "(" << constant->toString() << " " << sort->toString();

    for (const auto& attr : attributes) {
        ss << " " << attr->toString();
    }

    ss << ")";
    return ss.str();
}

/* ============================== SimpleFunDeclaration =============================== */

void SimpleFunDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SimpleFunDeclaration::toString() {
    stringstream ss;
    ss << "(" << identifier->toString();

    for (const auto& sig : signature) {
        ss << " " << sig->toString();
    }

    for (const auto& attr : attributes) {
        ss << " " << attr->toString();
    }

    ss << ")";
    return ss.str();
}

/* =============================== ParametricFunDeclaration ================================ */

void ParametricFunDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string ParametricFunDeclaration::toString() {
    stringstream ss;
    ss << "(par (";

    for (size_t i = 0, sz = parameters.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << parameters[i];
    }

    ss << ") (" << identifier->toString();

    for (const auto& sig : signature) {
        ss << " " << sig->toString();
    }

    for (const auto& attr : attributes) {
        ss << " " << attr->toString();
    }

    ss << "))";
    return ss.str();
}
