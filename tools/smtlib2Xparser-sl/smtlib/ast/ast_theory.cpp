#include "ast_theory.h"

#include <sstream>

using namespace smtlib::ast;
using namespace std;

void Theory::accept(Visitor0 *visitor) {
    visitor->visit(shared_from_this());
}

string Theory::toString() {
    stringstream ss;
    ss << "(theory  " << name->toString();

    for(const auto& attr : attributes) {
        ss << " " << attr->toString();
    }

    ss << ")";
    return ss.str();
}
