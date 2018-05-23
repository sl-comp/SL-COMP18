#include "ast_basic.h"

#include "util/global_values.h"

#include <sstream>

using namespace std;
using namespace smtlib::ast;

/* ====================================== Symbol ====================================== */

void Symbol::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string Symbol::toString() {
    return value;
}

/* ====================================== Keyword ===================================== */

void Keyword::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string Keyword::toString() {
    return value;
}

/* ================================= MetaSpecConstant ================================= */

void MetaSpecConstant::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string MetaSpecConstant::toString() {
    return (type == Type::STRING) ? MSCONST_STRING
                                  : (type == Type::NUMERAL ? MSCONST_NUMERAL
                                                           : MSCONST_DECIMAL);
}

/* =================================== BooleanValue =================================== */

void BooleanValue::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string BooleanValue::toString() {
    if (value)
        return CONST_TRUE;

    return CONST_FALSE;
}

/* =================================== PropLiteral ==================================== */

void PropLiteral::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string PropLiteral::toString() {
    if (negated) {
        stringstream ss;
        ss << "(not " << symbol->toString() << ")";
        return ss.str();
    }

    return symbol->toString();
}
