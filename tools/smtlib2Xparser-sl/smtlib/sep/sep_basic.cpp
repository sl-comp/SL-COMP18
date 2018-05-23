#include "sep_basic.h"

#include "util/global_values.h"

#include <sstream>

using namespace std;
using namespace smtlib::sep;

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
    return value ? CONST_TRUE : CONST_FALSE;
}

/* =================================== PropLiteral ==================================== */

void PropLiteral::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string PropLiteral::toString() {
    if (negated) {
        stringstream ss;
        ss << "(not " << value << ")";
        return ss.str();
    } else {
        return value;
    }
}
