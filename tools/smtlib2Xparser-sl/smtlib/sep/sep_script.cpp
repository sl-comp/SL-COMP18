#include "sep_script.h"

#include <sstream>

using namespace std;
using namespace smtlib::sep;

void Script::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string Script::toString() {
    stringstream ss;

    for (const auto& cmd : commands) {
        ss << cmd->toString() << "\n";
    }

    return ss.str();
}
