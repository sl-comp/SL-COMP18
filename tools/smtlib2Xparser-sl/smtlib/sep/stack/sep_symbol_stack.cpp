#include "sep_symbol_stack.h"

#include <algorithm>

using namespace std;
using namespace smtlib::sep;

SymbolStack::SymbolStack() {
    push();
}

SymbolTablePtr SymbolStack::getTopLevel() {
    return stack[stack.size() - 1];
}

std::vector<SymbolTablePtr>& SymbolStack::getLevels() {
    return stack;
}

bool SymbolStack::push() {
    size_t size = stack.size();
    stack.push_back(make_shared<SymbolTable>());
    return (stack.size() == size + 1);
}

bool SymbolStack::push(size_t levels) {
    size_t size = stack.size();
    for (int i = 0; i < levels; i++)
        stack.push_back(make_shared<SymbolTable>());
    return (stack.size() == size + levels);
}

bool SymbolStack::pop() {
    if (stack.size() <= 1) {
        return false;
    } else {
        size_t size = stack.size();
        stack.erase(stack.begin() + (stack.size() - 1));
        return (stack.size() == size - 1);
    }
}

bool SymbolStack::pop(size_t levels) {
    if (stack.size() <= 1 + levels || levels == 0) {
        return false;
    } else {
        size_t size = stack.size();
        stack.erase(stack.begin() + (stack.size() - levels), stack.begin() + (stack.size() - 1));
        return (stack.size() == size - 1);
    }
}

void SymbolStack::reset() {
    pop(stack.size() - 1);
    getTopLevel()->reset();
}

SortEntryPtr SymbolStack::getSortEntry(const string& name) {
    for (const auto& lvl : stack) {
        SortEntryPtr entry = lvl->getSortEntry(name);
        if (entry)
            return entry;
    }
    return SortEntryPtr();
}

std::vector<FunEntryPtr> SymbolStack::getFunEntry(const string& name) {
    std::vector<FunEntryPtr> result;
    for (const auto& lvl : stack) {
        std::vector<FunEntryPtr> entries = lvl->getFunEntry(name);
        result.insert(result.end(), entries.begin(), entries.end());
    }
    return result;
}

VarEntryPtr SymbolStack::getVarEntry(const string& name) {
    for (const auto& lvl : stack) {
        VarEntryPtr entry = lvl->getVarEntry(name);
        if (entry)
            return entry;
    }
    return VarEntryPtr();
}

SortEntryPtr SymbolStack::findDuplicate(const SortEntryPtr& entry) {
    for (const auto& lvl : stack) {
        SortEntryPtr dup = lvl->getSortEntry(entry->name);
        if (dup)
            return dup;
    }
    return SortEntryPtr();
}

FunEntryPtr SymbolStack::findDuplicate(const FunEntryPtr& entry) {
    std::vector<FunEntryPtr> knownFuns = getFunEntry(entry->name);
    for (const auto& fun : knownFuns) {
        if (entry->params.empty() && fun->params.empty()) {
            if (equal(entry->signature, fun->signature)) {
                return fun;
            }
        } else {
            if (equal(entry->params, entry->signature, fun->params, fun->signature)) {
                return fun;
            }
        }
    }
    return FunEntryPtr();
}

VarEntryPtr SymbolStack::findDuplicate(const VarEntryPtr& entry) {
    return getTopLevel()->getVarEntry(entry->name);
}

SortPtr SymbolStack::replace(const SortPtr& sort, unordered_map<string, SortPtr>& mapping) {
    if (mapping.empty())
        return sort;

    if (!sort->hasArgs()) {
        if (mapping.find(sort->toString()) != mapping.end())
            return mapping[sort->toString()];
        else
            return sort;
    } else {
        std::vector<SortPtr> newargs;
        bool changed = false;
        std::vector<SortPtr>& argSorts = sort->arguments;
        for (const auto& arg : argSorts) {
            SortPtr result = replace(arg, mapping);

            newargs.push_back(result);
            if (result.get() != arg.get())
                changed = true;
        }

        if (changed) {
            return make_shared<Sort>(sort->name, newargs);
        } else {
            return sort;
        }
    }
}

HeapEntry SymbolStack::findDuplicate(const HeapEntry& entry) {
    const SortPtr& locSortExp = expand(entry.first);
    const SortPtr& dataSortExp = expand(entry.second);

    string locSortStr = std::move(locSortExp->toString());
    string dataSortExpStr = std::move(dataSortExp->toString());

    for (const auto& lvl : stack) {
        const HeapEntryMap& heap = lvl->getHeap();

        auto found = find_if(heap.begin(), heap.end(),
                             [&](const pair<SortPtr, SortPtr>& p) {
                                 return locSortStr == p.first->toString() &&
                                        dataSortExpStr == p.second->toString();
                             });

        if(found != heap.end())  {
            return (*found);
        }
    }

    return make_pair(SortPtr(), SortPtr());
}

SortPtr SymbolStack::expand(const SortPtr& sort) {
    if (!sort)
        return sort;

    SortEntryPtr entry = getSortEntry(sort->name);
    if (!sort->hasArgs()) {
        if (entry) {
            if (entry->params.empty()) {
                std::vector<SortPtr> empty;
                SortPtr newsort = make_shared<Sort>(entry->name, empty);
                return newsort;
            } else {
                return SortPtr();
            }
        } else {
            return sort;
        }
    } else {
        if (entry) {
            if (entry->arity != sort->arguments.size())
                return SortPtr();

            if (entry->params.size() == sort->arguments.size()) {
                unordered_map<string, SortPtr> mapping;
                for (int i = 0; i < entry->params.size(); i++) {
                    mapping[entry->params[i]] = sort->arguments[i];
                }

                SortPtr newsort = replace(entry->sort, mapping);
                newsort = expand(newsort);
                return newsort;
            } else {
                return SortPtr();
            }
        } else {
            std::vector<SortPtr> newargs;
            bool changed = false;
            std::vector<SortPtr>& argSorts = sort->arguments;
            for (const auto& arg : argSorts) {
                SortPtr result = expand(arg);
                if (!result)
                    return SortPtr();

                newargs.push_back(result);
                if (result.get() != arg.get())
                    changed = true;
            }

            if (changed) {
                SortPtr newsort = make_shared<Sort>(sort->name, newargs);
                return newsort;
            } else {
                return sort;
            }
        }
    }
}

bool SymbolStack::equal(const SortPtr& sort1, const SortPtr& sort2) {
    if (sort1 && sort2) {
        return sort1->toString() == sort2->toString();
    } else {
        return false;
    }
}

bool SymbolStack::equal(const vector<string>& params1, const SortPtr& sort1,
                        const vector<string>& params2, const SortPtr& sort2,
                        unordered_map<string, string>& mapping) {
    if (!sort1 || !sort2) {
        return false;
    }

    if (sort1->arguments.size() != sort2->arguments.size())
        return false;

    if (sort1->arguments.empty()) {
        bool isParam1 = false;
        bool isParam2 = false;

        string str1 = sort1->toString();
        string str2 = sort2->toString();

        for (size_t j = 0, sz = params1.size(); j < sz; j++) {
            if (params1[j] == str1)
                isParam1 = true;
            if (params2[j] == str2)
                isParam2 = true;
        }

        if ((isParam1 && !isParam2) || (!isParam1 && isParam2)) {
            return false;
        } else if (isParam1) {
            if (mapping.find(str1) != mapping.end()) {
                return mapping[str1] == str2;
            } else {
                mapping[str1] = str2;
                return true;
            }
        } else {
            return equal(sort1, sort2);
        }
    } else {
        if (sort1->name != sort2->name)
            return false;

        for (size_t k = 0, sz = sort1->arguments.size(); k < sz; k++) {
            if (!equal(params1, sort1->arguments[k], params2, sort2->arguments[k], mapping))
                return false;
        }

        return true;
    }
}

bool SymbolStack::equal(const vector<SortPtr>& signature1,
                        const vector<SortPtr>& signature2) {
    if (signature1.size() != signature2.size())
        return false;

    for (size_t i = 0, sz = signature1.size(); i < sz; i++) {
        if (!equal(signature1[i], signature2[i]))
            return false;
    }

    return true;
}

bool SymbolStack::equal(const vector<string>& params1,
                        const vector<SortPtr>& signature1,
                        const vector<string>& params2,
                        const vector<SortPtr>& signature2) {
    if (params1.size() != params2.size() || signature1.size() != signature2.size())
        return false;

    unordered_map<string, string> mapping;
    for (size_t i = 0, sz = signature1.size(); i < sz; i++) {
        SortPtr sort1 = signature1[i];
        SortPtr sort2 = signature2[i];

        if (!equal(params1, sort1, params2, sort2, mapping))
            return false;
    }

    return mapping.size() == params1.size();
}

SortEntryPtr SymbolStack::tryAdd(const SortEntryPtr& entry) {
    SortEntryPtr dup = findDuplicate(entry);
    if (!dup)
        getTopLevel()->add(entry);
    return dup;
}

FunEntryPtr SymbolStack::tryAdd(const FunEntryPtr& entry) {
    FunEntryPtr dup = findDuplicate(entry);
    if (!dup)
        getTopLevel()->add(entry);
    return dup;
}

VarEntryPtr SymbolStack::tryAdd(const VarEntryPtr& entry) {
    VarEntryPtr dup = findDuplicate(entry);
    if (!dup)
        getTopLevel()->add(entry);
    return dup;
}

HeapEntry SymbolStack::tryAdd(const HeapEntry& entry) {
    const HeapEntry& entryExp = make_pair(expand(entry.first), expand(entry.second));

    HeapEntry dup = findDuplicate(entryExp);
    if(!dup.first || !dup.second) {
        getTopLevel()->add(entryExp);
    }
    return dup;
}
