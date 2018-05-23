#include "ast_variable.h"

#include <sstream>

using namespace std;
using namespace smtlib::ast;

/* ================================== SortedVariable ================================== */
void SortedVariable::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SortedVariable::toString() {
    stringstream ss;
    ss << symbol->toString() << " " << sort->toString();
    return ss.str();
}

/* ==================================== VariableBinding ==================================== */
void VariableBinding::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string VariableBinding::toString() {
    stringstream ss;
    ss << symbol->toString() << " " << term->toString();
    return ss.str();
}
