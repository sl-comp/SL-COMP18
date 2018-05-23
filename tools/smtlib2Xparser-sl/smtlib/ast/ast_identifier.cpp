#include "ast_identifier.h"

#include <sstream>

using namespace std;
using namespace smtlib::ast;

/* ================================= SimpleIdentifier ================================= */

bool SimpleIdentifier::isIndexed() {
    return !indices.empty();
}

void SimpleIdentifier::accept(Visitor0 *visitor) {
    visitor->visit(shared_from_this());
}

string SimpleIdentifier::toString() {
    if (!isIndexed())
        return symbol->toString();

    stringstream ss;
    ss << "(_ " << symbol->toString() << " ";

    for (size_t i = 0, sz = indices.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << indices[i]->toString();
    }

    ss << ")";
    return ss.str();
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
