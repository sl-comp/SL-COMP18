#include "sep_variable.h"

#include <sstream>

using namespace std;
using namespace smtlib::sep;

/* ================================== SortedVariable ================================== */

void SortedVariable::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SortedVariable::toString() {
    stringstream ss;
    ss << name << " " << sort->toString();
    return ss.str();
}

/* ================================== VariableBinding ================================== */

void VariableBinding::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string VariableBinding::toString() {
    stringstream ss;
    ss << name << " " << term->toString();
    return ss.str();
}
