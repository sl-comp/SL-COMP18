#include "sep_match.h"

#include <sstream>

using namespace std;
using namespace smtlib::sep;

/* =============================== QualifiedConstructor =============================== */

void QualifiedConstructor::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string QualifiedConstructor::toString() {
    stringstream ss;
    ss << "(as " << name << " " << sort->toString() << ")";
    return ss.str();
}

/* ================================= QualifiedPattern ================================= */

void QualifiedPattern::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string QualifiedPattern::toString() {
    stringstream ss;
    ss << "(" << constructor->toString();

    for (const auto& arg : arguments) {
        ss << " " << arg;
    }

    ss << ")";
    return ss.str();
}

/* ===================================== MatchCase ==================================== */

void MatchCase::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string MatchCase::toString() {
    stringstream ss;
    ss << "(" << pattern->toString() << " " << term->toString() << ")";
    return ss.str();
}
