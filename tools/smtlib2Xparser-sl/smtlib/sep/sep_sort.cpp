#include "sep_sort.h"

#include <sstream>

using namespace std;
using namespace smtlib::sep;

bool Sort::hasArgs() {
    return !arguments.empty();
}

void Sort::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string Sort::toString() {
    if (!hasArgs())
        return name;

    stringstream ss;
    ss << "(" << name;

    for (const auto& arg : arguments) {
        ss << " " << arg;
    }

    ss << ")";
    return ss.str();
}
