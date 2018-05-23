#include "ast_sort.h"

#include <sstream>

using namespace std;
using namespace smtlib::ast;

bool Sort::hasArgs() {
    return !arguments.empty();
}

void Sort::accept(Visitor0* visitor) {
     visitor->visit(shared_from_this());
}

string Sort::toString() {
    if(!hasArgs()) {
        return identifier->toString();
    }

    stringstream ss;
    ss << "(" << identifier->toString() << " ";

    for (size_t i = 0, sz = arguments.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << arguments[i]->toString();
    }

    ss << ")";
    return ss.str();
}
