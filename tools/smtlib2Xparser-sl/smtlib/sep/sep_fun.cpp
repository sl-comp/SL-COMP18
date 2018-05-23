#include "sep_fun.h"

#include <sstream>

using namespace std;
using namespace smtlib::sep;

/* ================================ FunctionDeclaration =============================== */

void FunctionDeclaration::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string FunctionDeclaration::toString() {
    stringstream ss;
    ss << name << " (";

    for (size_t i = 0, sz = parameters.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << parameters[i]->toString();
    }

    ss << ") " << sort->toString();
    return ss.str();
}

/* ================================ FunctionDefinition ================================ */

void FunctionDefinition::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string FunctionDefinition::toString() {
    stringstream ss;
    ss << signature->toString() << " " << body->toString();
    return ss.str();
}
