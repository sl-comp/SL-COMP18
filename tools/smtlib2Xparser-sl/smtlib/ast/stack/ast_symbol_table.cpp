#include "ast_symbol_table.h"

#include "ast/ast_command.h"
#include "ast/ast_symbol_decl.h"

using namespace std;
using namespace smtlib::ast;

SortEntryPtr SymbolTable::getSortEntry(const string& name) {
    auto it = sorts.find(name);
    if (it != sorts.end()) {
        return it->second;
    } else {
        SortEntryPtr empty;
        return empty;
    }
}

std::vector<FunEntryPtr> SymbolTable::getFunEntry(const string& name) {
    auto it = funs.find(name);
    if (it != funs.end()) {
        return it->second;
    } else {
        std::vector<FunEntryPtr> empty;
        return empty;
    }
}

VarEntryPtr SymbolTable::getVarEntry(const string& name) {
    auto it = vars.find(name);
    if (it != vars.end()) {
        return it->second;
    } else {
        VarEntryPtr empty;
        return empty;
    }
}

bool SymbolTable::add(const SortEntryPtr& entry) {
    if(sorts.find(entry->name) == sorts.end()) {
        sorts[entry->name] = entry;
        return true;
    } else {
        return false;
    }
}

bool SymbolTable::add(const FunEntryPtr& entry) {
    funs[entry->name].push_back(entry);
    return true;
}

bool SymbolTable::add(const VarEntryPtr& entry) {
    if(vars.find(entry->name) == vars.end()) {
        vars[entry->name] = entry;
        return true;
    } else {
        return false;
    }
}

void SymbolTable::reset() {
    // Clear all variables
    vars.clear();

    // Erase sort information that does not come from theory files
    std::vector<SortEntryPtr> sortEntries;
    for (const auto& sort : sorts) {
        sortEntries.push_back(sort.second);
    }

    for (const auto& sortEntry : sortEntries) {
        if(!dynamic_pointer_cast<SortSymbolDeclaration>(sortEntry->source)) {
            sorts.erase(sortEntry->name);
        }
    }

    // Erase function information that does not come from theory files
    vector<string> funKeys;
    vector<std::vector<FunEntryPtr>> funEntry;
    for (const auto& fun : funs) {
        funKeys.push_back(fun.first);
        funEntry.push_back(fun.second);
    }

    for (int i = 0; i < funKeys.size(); i++) {
        std::vector<FunEntryPtr>& entry = funs[funKeys[i]];
        for (int j = 0; j < funEntry[i].size(); j++) {
            if(!dynamic_pointer_cast<FunSymbolDeclaration>(funEntry[i][j]->source)) {
                entry.erase(entry.begin() + j);
            }
        }
        if(entry.empty())
            funs.erase(funKeys[i]);
    }
}