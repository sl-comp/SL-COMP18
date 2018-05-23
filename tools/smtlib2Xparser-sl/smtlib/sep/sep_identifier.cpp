#include "sep_identifier.h"

#include <sstream>

using namespace std;
using namespace smtlib::sep;

/* ==================================== SimpleIdentifier ==================================== */

void SimpleIdentifier::accept(Visitor0 *visitor) {
    visitor->visit(shared_from_this());
}

string SimpleIdentifier::toString() {
    if (!isIndexed())
        return name;
    else {
        stringstream ss;
        ss << "( _ " << name;

        for(const auto& index : indices) {
            ss << " " << index->toString();
        }

        ss << ")";
        return ss.str();
    }
}

/* =============================== QualifiedIdentifier ================================ */

void QualifiedIdentifier::accept(Visitor0 *visitor) {
    visitor->visit(shared_from_this());
}

string QualifiedIdentifier::toString() {
    stringstream ss;
    ss << "(as " << identifier->toString() << " " << sort->toString() << ")";
    return ss.str();
}