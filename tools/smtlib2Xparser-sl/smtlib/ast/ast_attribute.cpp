#include "ast_attribute.h"

#include <sstream>

using namespace smtlib::ast;
using namespace std;

/* ==================================== Attribute ===================================== */

void Attribute::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string Attribute::toString() {
    stringstream ss;
    ss << keyword->toString();

    if (value)
        ss << " " << value->toString();

    return ss.str();
}

/* ============================== CompAttributeValue ============================== */

void CompAttributeValue::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string CompAttributeValue::toString() {
    stringstream ss;
    ss << "(";

    for (size_t i = 0, sz = values.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << values[i]->toString();
    }

    ss << ")";
    return ss.str();
}
