#include "ast_literal.h"

#include <algorithm>
#include <bitset>
#include <cmath>
#include <iostream>
#include <sstream>

using namespace smtlib::ast;
using namespace std;

/* ================================== NumeralLiteral ================================== */
void NumeralLiteral::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string NumeralLiteral::toString() {
    stringstream ss;

    if (base == 2) {
        ss << "#b";
        if(value == 0)
            ss << 0;
        else {
            long val = value;
            stringstream binary;
            while(val != 0) {
                binary << (val & 1);
                val >>= 1;
            }
            string result = binary.str();
            reverse(result.begin(), result.end());
            ss << result;
        }
    } else if (base == 16) {
        ss << "#x" << std::hex << value;
    } else {
        ss << value;
    }

    return ss.str();
}

/* ================================== DecimalLiteral ================================== */
void DecimalLiteral::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string DecimalLiteral::toString() {
    stringstream ss;
    ss << value;
    return ss.str();
}

/* ================================== StringLiteral =================================== */
void StringLiteral::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string StringLiteral::toString() {
    return value;
}
