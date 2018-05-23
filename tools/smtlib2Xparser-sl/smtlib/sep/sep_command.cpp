#include "sep_command.h"

#include <sstream>

using namespace std;
using namespace smtlib::sep;

/* ================================== AssertCommand =================================== */

void AssertCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string AssertCommand::toString() {
    stringstream ss;
    ss << "(" << KW_ASSERT << " " << term->toString() << ")";
    return ss.str();
}

/* ================================= CheckSatCommand ================================== */

void CheckSatCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string CheckSatCommand::toString() {
    stringstream ss;
    ss << "(" << KW_CHK_SAT << ")";
    return ss.str();
}

/* ================================ CheckUnsatCommand ================================= */

void CheckUnsatCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string CheckUnsatCommand::toString() {
    stringstream ss;
    ss << "(" << KW_CHK_UNSAT << ")";
    return ss.str();
}

/* =============================== CheckSatAssumCommand =============================== */

void CheckSatAssumCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string CheckSatAssumCommand::toString() {
    stringstream ss;
    ss << "(" << KW_CHK_SAT_ASSUM << " (";

    for (size_t i = 0, sz = assumptions.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << assumptions[i]->toString();
    }

    ss << "))";
    return ss.str();
}

/* =============================== DeclareConstCommand ================================ */

void DeclareConstCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string DeclareConstCommand::toString() {
    stringstream ss;
    ss << "(" << KW_DECL_CONST << " " << name << " " << sort->toString() << ")";
    return ss.str();
}

/* ============================== DeclareDatatypeCommand ============================== */

void DeclareDatatypeCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string DeclareDatatypeCommand::toString() {
    stringstream ss;
    ss << "(" << KW_DECL_DATATYPE << " " << name << " " << declaration->toString() << ")";
    return ss.str();
}

/* ============================= DeclareDatatypesCommand ============================== */

void DeclareDatatypesCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string DeclareDatatypesCommand::toString() {
    stringstream ss;
    ss << "(" << KW_DECL_DATATYPES << " (";

    for (size_t i = 0, sz = sorts.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << sorts[i]->toString();
    }

    ss << ") (";

    for (size_t i = 0, sz = declarations.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << declarations[i]->toString();
    }

    ss << ")";
    return ss.str();
}

/* =============================== DeclareFunCommand ================================ */

void DeclareFunCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string DeclareFunCommand::toString() {
    stringstream ss;
    ss << "(" << KW_DECL_FUN << " " << name << " (";

    for (size_t i = 0, sz = parameters.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << parameters[i]->toString();
    }

    ss << ") " << sort->toString() << ")";

    return ss.str();
}

/* =============================== DeclareSortCommand ================================ */

void DeclareSortCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string DeclareSortCommand::toString() {
    stringstream ss;
    ss << "(" << KW_DECL_SORT << " " << name << " " << arity << ")";
    return ss.str();
}

/* =============================== DeclareHeapCommand ================================ */

void DeclareHeapCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string DeclareHeapCommand::toString() {
    stringstream ss;
    ss << "(" << KW_DECL_HEAP << " ";

    for(const auto &pair : locDataPairs) {
        ss << "(" << pair.first->toString() << " " << pair.second->toString() << ")";
    }

    ss << ")";
    return ss.str();
}

/* ================================= DefineFunCommand ================================= */

void DefineFunCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string DefineFunCommand::toString() {
    stringstream ss;
    ss << "(" << KW_DEF_FUN << " " << definition->toString() << ")";
    return ss.str();
}

/* ================================ DefineFunRecCommand =============================== */

void DefineFunRecCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string DefineFunRecCommand::toString() {
    stringstream ss;
    ss << "(" << KW_DEF_FUN_REC << " " << definition->toString() << ")";
    return ss.str();
}

/* =============================== DefineFunsRecCommand =============================== */

void DefineFunsRecCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string DefineFunsRecCommand::toString() {
    stringstream ss;
    ss << "(" << KW_DEF_FUNS_REC << " (";

    for (size_t i = 0, sz = declarations.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << declarations[i]->toString();
    }

    ss << ") (";

    for (size_t i = 0, sz = bodies.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << bodies[i]->toString();
    }

    ss << "))";
    return ss.str();
}

/* ================================ DefineSortCommand ================================= */

void DefineSortCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string DefineSortCommand::toString() {
    stringstream ss;
    ss << "(" << KW_DEF_SORT << " " << name << " (";

    for (size_t i = 0, sz = parameters.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << parameters[i];
    }

    ss << ") " << sort->toString() << ")";
    return ss.str();
}

/* =================================== EchoCommand ==================================== */

void EchoCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string EchoCommand::toString() {
    stringstream ss;
    ss << "(" << KW_ECHO << " " << message << ")";
    return ss.str();
}

/* =================================== ExitCommand ==================================== */

void ExitCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string ExitCommand::toString() {
    stringstream ss;
    ss << "(" << KW_EXIT << ")";
    return ss.str();
}

/* ================================ GetAssertsCommand ================================= */

void GetAssertsCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string GetAssertsCommand::toString() {
    stringstream ss;
    ss << "(" << KW_GET_ASSERTS << ")";
    return ss.str();
}

/* ================================ GetAssignsCommand ================================= */

void GetAssignsCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string GetAssignsCommand::toString() {
    stringstream ss;
    ss << "(" << KW_GET_ASSIGNS << ")";
    return ss.str();
}

/* ================================== GetInfoCommand ================================== */

void GetInfoCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string GetInfoCommand::toString() {
    stringstream ss;
    ss << "(" << KW_GET_INFO << " " << flag << ")";
    return ss.str();
}

/* ================================= GetModelCommand ================================== */

void GetModelCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string GetModelCommand::toString() {
    stringstream ss;
    ss << "(" << KW_GET_MODEL << ")";
    return ss.str();
}

/* ================================= GetOptionCommand ================================= */

void GetOptionCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string GetOptionCommand::toString() {
    stringstream ss;
    ss << "(" << KW_GET_OPT << " " << option << ")";
    return ss.str();
}

/* ================================= GetProofCommand ================================== */

void GetProofCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string GetProofCommand::toString() {
    stringstream ss;
    ss << "(" << KW_GET_PROOF << ")";
    return ss.str();
}

/* ============================== GetUnsatAssumsCommand =============================== */

void GetUnsatAssumsCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string GetUnsatAssumsCommand::toString() {
    stringstream ss;
    ss << "(" << KW_GET_UNSAT_ASSUMS << ")";
    return ss.str();
}

/* =============================== GetUnsatCoreCommand ================================ */

void GetUnsatCoreCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string GetUnsatCoreCommand::toString() {
    stringstream ss;
    ss << "(" << KW_GET_UNSAT_CORE << ")";
    return ss.str();
}

/* ================================= GetValueCommand ================================== */

void GetValueCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string GetValueCommand::toString() {
    stringstream ss;
    ss << "(" << KW_GET_VALUE << " (";

    for (size_t i = 0, sz = terms.size(); i < sz; i++) {
        if (i != 0)
            ss << " ";

        ss << terms[i]->toString();
    }

    ss << "))";
    return ss.str();
}

/* =================================== PopCommand ==================================== */

void PopCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string PopCommand::toString() {
    stringstream ss;
    ss << "(" << KW_POP << " " << levelCount << ")";
    return ss.str();
}

/* =================================== PushCommand ==================================== */

void PushCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string PushCommand::toString() {
    stringstream ss;
    ss << "(" << KW_PUSH << " " << levelCount << ")";
    return ss.str();
}

/* =================================== ResetCommand =================================== */

void ResetCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string ResetCommand::toString() {
    stringstream ss;
    ss << "(" << KW_RESET << ")";
    return ss.str();
}

/* =============================== ResetAssertsCommand ================================ */

void ResetAssertsCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string ResetAssertsCommand::toString() {
    stringstream ss;
    ss << "(" << KW_RESET_ASSERTS << ")";
    return ss.str();
}

/* ================================== SetInfoCommand ================================== */

void SetInfoCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SetInfoCommand::toString() {
    stringstream ss;
    ss << "(" << KW_SET_INFO << " " << info->toString() << ")";
    return ss.str();
}

/* ================================= SetLogicCommand ================================== */

void SetLogicCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SetLogicCommand::toString() {
    stringstream ss;
    ss << "(" << KW_SET_LOGIC << " " << logic << ")";
    return ss.str();
}

/* ================================= SetOptionCommand ================================= */

void SetOptionCommand::accept(Visitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SetOptionCommand::toString() {
    stringstream ss;
    ss << "(" << KW_SET_OPT << " " << option->toString() << ")";
    return ss.str();
}
