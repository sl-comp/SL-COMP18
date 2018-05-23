#include "sep_logic.h"

#include <sstream>

using namespace smtlib::sep;
using namespace std;

void Logic::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string Logic::toString() {
    stringstream ss;
    ss << "(logic  " << name;

    for (const auto& attr : attributes) {
        ss << " " << attr->toString();
    }

    ss << ")";
    return ss.str();
}
