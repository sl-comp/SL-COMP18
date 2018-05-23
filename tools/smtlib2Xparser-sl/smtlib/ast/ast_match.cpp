#include "ast_match.h"
#include "ast_sort.h"

#include <sstream>

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

void QualifiedConstructor::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string QualifiedConstructor::toString() {
    stringstream ss;
    ss << "(as " << symbol->toString() << " " << sort->toString() << ")";
    return ss.str();
}

/* ================================= QualifiedPattern ================================= */

void QualifiedPattern::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string QualifiedPattern::toString() {
    stringstream ss;
    ss << "(" << constructor->toString();

    for (const auto& symbol : symbols) {
        ss << " " << symbol->toString();
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
