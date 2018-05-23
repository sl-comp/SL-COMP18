#include "ast_logic.h"

#include <sstream>

using namespace smtlib::ast;
using namespace std;

void Logic::accept(Visitor0 *visitor) {
    visitor->visit(shared_from_this());
}

string Logic::toString() {
    stringstream ss;
    ss << "(logic  " << name->toString();

    for(const auto& attr : attributes) {
        ss << " " << attr->toString();
    }

    ss << ")";
    return ss.str();
}
