#include "ast_symbol_stack.h"

using namespace std;
using namespace smtlib::ast;

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
        return (stack.size() == size - levels);
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

SortPtr SymbolStack::replace(const SortPtr& sort,
                             unordered_map<string, SortPtr>& mapping) {
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
        for (const auto& argSort : argSorts) {
            SortPtr result = replace(argSort, mapping);

            newargs.push_back(result);
            if (result.get() != argSort.get())
                changed = true;
        }

        if (changed) {
            return make_shared<Sort>(sort->identifier, newargs);
        } else {
            return sort;
        }
    }
}

SortPtr SymbolStack::expand(const SortPtr& sort) {
    if (!sort)
        return sort;

    SortEntryPtr entry = getSortEntry(sort->identifier->toString());
    if (!sort->hasArgs()) {
        if (entry && entry->definition) {
            if (entry->definition->params.empty()) {
                SortPtr newsort = make_shared<Sort>(entry->definition->sort->identifier,
                                                    entry->definition->sort->arguments);
                newsort->rowLeft = sort->rowLeft;
                newsort->colLeft = sort->colLeft;
                newsort->rowRight = sort->rowRight;
                newsort->colRight = sort->colRight;
                newsort->filename = sort->filename;

                return newsort;
            } else {
                return SortPtr();
            }
        } else {
            return sort;
        }
    } else {
        if (entry && entry->definition) {
            if (entry->definition->params.size() == sort->arguments.size()) {
                unordered_map<string, SortPtr> mapping;
                for (int i = 0; i < entry->definition->params.size(); i++) {
                    mapping[entry->definition->params[i]->toString()] = sort->arguments[i];
                }

                SortPtr newsort = replace(entry->definition->sort, mapping);
                newsort = expand(newsort);
                newsort->rowLeft = sort->rowLeft;
                newsort->colLeft = sort->colLeft;
                newsort->rowRight = sort->rowRight;
                newsort->colRight = sort->colRight;
                newsort->filename = sort->filename;

                return newsort;
            } else {
                return SortPtr();
            }
        } else {
            if (entry && entry->arity != sort->arguments.size())
                return SortPtr();

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
                SortPtr newsort = make_shared<Sort>(sort->identifier, newargs);
                newsort->rowLeft = sort->rowLeft;
                newsort->colLeft = sort->colLeft;
                newsort->rowRight = sort->rowRight;
                newsort->colRight = sort->colRight;
                newsort->filename = sort->filename;

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

bool SymbolStack::equal(const std::vector<SymbolPtr>& params1, const SortPtr& sort1,
                        const std::vector<SymbolPtr>& params2, const SortPtr& sort2,
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
            if (params1[j]->toString() == str1)
                isParam1 = true;
            if (params2[j]->toString() == str2)
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
        if (sort1->identifier->toString() != sort2->identifier->toString())
            return false;

        for (size_t k = 0, sz = sort1->arguments.size(); k < sz; k++) {
            if (!equal(params1, sort1->arguments[k], params2, sort2->arguments[k], mapping))
                return false;
        }

        return true;
    }
}

bool SymbolStack::equal(const std::vector<SortPtr>& signature1,
                        const std::vector<SortPtr>& signature2) {
    if (signature1.size() != signature2.size())
        return false;

    for (size_t i = 0, sz = signature1.size(); i < sz; i++) {
        if (!equal(signature1[i], signature2[i]))
            return false;
    }

    return true;
}

bool SymbolStack::equal(const std::vector<SymbolPtr>& params1,
                        const std::vector<SortPtr>& signature1,
                        const std::vector<SymbolPtr>& params2,
                        const std::vector<SortPtr>& signature2) {
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