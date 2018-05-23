#include "sep_term_sorter.h"

#include "sep/sep_term.h"
#include "util/global_values.h"

#include <algorithm>

using namespace std;
using namespace smtlib::sep;

void TermSorter::visit(const SimpleIdentifierPtr& node) {
    VarEntryPtr varInfo = ctx->getStack()->getVarEntry(node->toString());
    if (varInfo) {
        ret = varInfo->sort;
    } else {
        vector<FunEntryPtr> infos = ctx->getStack()->getFunEntry(node->toString());
        vector<SortPtr> possibleSorts;
        for (const auto& info : infos) {
            if (info->signature.size() == 1 && info->params.empty())
                possibleSorts.push_back(info->signature[0]);
        }

        if (possibleSorts.size() == 1) {
            ret = possibleSorts[0];
        }
    }
}

void TermSorter::visit(const QualifiedIdentifierPtr& node) {
    vector<FunEntryPtr> infos = ctx->getStack()->getFunEntry(node->identifier->toString());
    SortPtr retExpanded = ctx->getStack()->expand(node->sort);

    vector<SortPtr> retSorts;
    for (const auto& info : infos) {
        if (info->signature.size() == 1) {
            if (info->params.empty()) {
                retSorts.push_back(info->signature[0]);
            } else {
                unordered_map<string, SortPtr> mapping;
                unify(info->signature[0], retExpanded, info->params, mapping);

                if (mapping.size() == info->params.size()) {
                    SortPtr retSort = ctx->getStack()->replace(info->signature[0], mapping);
                    if (retSort->toString() == retExpanded->toString()) {
                        ret = retSort;
                        return;
                    }
                    retSorts.push_back(retSort);
                }
            }
        }
    }

    if (retSorts.size() == 1 && retSorts[0]->toString() == retExpanded->toString()) {
        ret = retSorts[0];
    }
}

void TermSorter::visit(const DecimalLiteralPtr& node) {
    vector<FunEntryPtr> entries = ctx->getStack()->getFunEntry(MSCONST_DECIMAL);
    if (entries.size() == 1) {
        if (entries[0]->signature.size() == 1) {
            ret = entries[0]->signature[0];
        }
    }
}

void TermSorter::visit(const NumeralLiteralPtr& node) {
    vector<FunEntryPtr> entries = ctx->getStack()->getFunEntry(MSCONST_NUMERAL);
    if (entries.size() == 1) {
        if (entries[0]->signature.size() == 1) {
            ret = entries[0]->signature[0];
        }
    }
}

void TermSorter::visit(const StringLiteralPtr& node) {
    vector<FunEntryPtr> entries = ctx->getStack()->getFunEntry(MSCONST_STRING);
    if (entries.size() == 1) {
        if (entries[0]->signature.size() == 1) {
            ret = entries[0]->signature[0];
        }
    }
}

void TermSorter::visit(const QualifiedTermPtr& node) {
    vector<SortPtr> argSorts;
    vector<TermPtr>& terms = node->terms;
    for (const auto& term : terms) {
        SortPtr result = wrappedVisit(term);
        if (result)
            argSorts.push_back(result);
        else {
            return;
        }
    }

    SimpleIdentifierPtr id = dynamic_pointer_cast<SimpleIdentifier>(node->identifier);
    QualifiedIdentifierPtr qid = dynamic_pointer_cast<QualifiedIdentifier>(node->identifier);

    SortPtr retExpanded;
    string name;

    if (id) {
        name = id->toString();
    } else {
        name = qid->identifier->toString();
        retExpanded = ctx->getStack()->expand(qid->sort);
    }

    vector<FunEntryPtr> infos = ctx->getStack()->getFunEntry(name);
    vector<SortPtr> retSorts;

    for (const auto& info : infos) {
        vector<SortPtr> funSig;
        if (argSorts.size() >= 2) {
            if (info->assocL) {
                funSig.push_back(info->signature[0]);
                for (int i = 0; i < argSorts.size() - 1; i++) {
                    funSig.push_back(info->signature[1]);
                }
                funSig.push_back(info->signature[2]);
            } else if (info->assocR) {
                for (int i = 0; i < argSorts.size() - 1; i++) {
                    funSig.push_back(info->signature[0]);
                }
                funSig.push_back(info->signature[1]);
                funSig.push_back(info->signature[2]);
            } else if (info->chainable || info->pairwise) {
                for (int i = 0; i < argSorts.size(); i++) {
                    funSig.push_back(info->signature[0]);
                }
                funSig.push_back(info->signature[2]);
            } else {
                funSig.insert(funSig.begin(), info->signature.begin(), info->signature.end());
            }
        } else {
            funSig.insert(funSig.begin(), info->signature.begin(), info->signature.end());
        }

        if (argSorts.size() == funSig.size() - 1) {
            bool fits = true;
            if (info->params.empty()) {
                for (size_t i = 0, sz = funSig.size() - 1; i < sz; i++) {
                    if (funSig[i]->toString() != argSorts[i]->toString())
                        fits = false;
                }

                if (id) {
                    if (fits)
                        retSorts.push_back(funSig[funSig.size() - 1]);
                } else {
                    SortPtr retSort = funSig[funSig.size() - 1];
                    if (fits && retSort->toString() == retExpanded->toString()) {
                        ret = retSort;
                        return;
                    }
                }
            } else {
                unordered_map<string, SortPtr> mapping;

                for (size_t i = 0, sz = funSig.size() - 1; i < sz; i++) {
                    fits = fits && unify(funSig[i], argSorts[i], info->params, mapping);
                }

                if (fits && mapping.size() == info->params.size()) {
                    SortPtr retSort = funSig[funSig.size() - 1];
                    retSort = ctx->getStack()->replace(retSort, mapping);
                    string retSortString = retSort->toString();
                    if (id) {
                        retSorts.push_back(retSort);
                    } else {
                        if (retSortString == retExpanded->toString()) {
                            ret = retSort;
                            return;
                        }
                    }
                }
            }
        }
    }

    vector<string> argSortsStr;
    for (const auto& sort : argSorts) {
        argSortsStr.push_back(sort->toString());
    }

    vector<string> retSortsStr;
    for (const auto& sort : retSorts) {
        retSortsStr.push_back(sort->toString());
    }

    if (id && retSorts.size() == 1) {
        ret = retSorts[0];
    }
}

void TermSorter::visit(const LetTermPtr& node) {
    ctx->getStack()->push();

    for (const auto& binding : node->bindings) {
        SortPtr result = wrappedVisit(binding->term);
        if (result) {
            ctx->getStack()->tryAdd(make_shared<VarEntry>(binding->name, result, node));
        } else {
            return;
        }
    }

    SortPtr result = wrappedVisit(node->term);
    if (result) {
        ret = result;
    }

    ctx->getStack()->pop();
}

void TermSorter::visit(const ForallTermPtr& node) {
    ctx->getStack()->push();

    for (const auto& bind : node->bindings) {
        ctx->getStack()->tryAdd(
            make_shared<VarEntry>(bind->name, std::move(ctx->getStack()->expand(bind->sort)), node));
    }

    SortPtr result = wrappedVisit(node->term);
    if (result && result->name == SORT_BOOL) {
        ret = result;
    }

    ctx->getStack()->pop();
}

void TermSorter::visit(const ExistsTermPtr& node) {
    ctx->getStack()->push();

    for (const auto& bind : node->bindings) {
        ctx->getStack()->tryAdd(
            make_shared<VarEntry>(bind->name, std::move(ctx->getStack()->expand(bind->sort)), node));
    }

    SortPtr result = wrappedVisit(node->term);
    if (result && result->name == SORT_BOOL) {
            ret = result;
    }

    ctx->getStack()->pop();
}

void TermSorter::visit(const MatchTermPtr& node) {
    vector<SortPtr> caseSorts;

    for (const auto& caseIt : node->cases) {
        SortPtr caseSort = wrappedVisit(caseIt->term);
        if (caseSort) {
            caseSorts.push_back(caseSort);
        }
    }

    vector<string> caseSortsStr;
    for (const auto& sort : caseSorts) {
        caseSortsStr.push_back(sort->toString());
    }

    if (caseSorts.size() == node->cases.size()) {
        string case1 = caseSorts[0]->toString();
        bool equalCases = true;
        for (size_t i = 1, sz = caseSorts.size(); i < sz; i++) {
            if (caseSorts[1]->toString() != case1) {
                equalCases = false;
                break;
            }
        }
        if (equalCases)
            ret = caseSorts[0];
    }
}

void TermSorter::visit(const AnnotatedTermPtr& node) {
    ret = wrappedVisit(node->term);
}

void TermSorter::visit(const TrueTermPtr& node) {
    ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(const FalseTermPtr& node) {
    ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(const NotTermPtr& node) {
    SortPtr sort = wrappedVisit(node->term);
    if (sort->name == SORT_BOOL)
        ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(const ImpliesTermPtr& node) {
    bool sorted = true;
    auto terms = node->terms;

    for (const auto& term : terms) {
        SortPtr sort = wrappedVisit(term);
        if (sort->name != SORT_BOOL)
            sorted = false;
    }

    if (sorted)
        ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(const AndTermPtr& node) {
    bool sorted = true;
    auto terms = node->terms;

    for (const auto& term : terms) {
        SortPtr sort = wrappedVisit(term);
        if (sort->name != SORT_BOOL)
            sorted = false;
    }

    if (sorted)
        ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(const OrTermPtr& node) {
    bool sorted = true;
    auto terms = node->terms;

    for (const auto& term : terms) {
        SortPtr sort = wrappedVisit(term);
        if (sort->name != SORT_BOOL)
            sorted = false;
    }

    if (sorted)
        ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(const XorTermPtr& node) {
    bool sorted = true;
    auto terms = node->terms;

    for (const auto& term : terms) {
        SortPtr sort = wrappedVisit(term);
        if (sort->name != SORT_BOOL)
            sorted = false;
    }

    if (sorted)
        ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(const EqualsTermPtr& node) {
    bool sorted = true;
    auto terms = node->terms;

    for (const auto& term : terms) {
        SortPtr sort = wrappedVisit(term);
        if (sort->name != SORT_BOOL)
            sorted = false;
    }

    if (sorted)
        ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(const DistinctTermPtr& node) {
    bool sorted = true;
    auto terms = node->terms;

    for (const auto& term : terms) {
        SortPtr sort = wrappedVisit(term);
        if (sort->name != SORT_BOOL)
            sorted = false;
    }

    if (sorted)
        ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(const IteTermPtr& node) {
    SortPtr resultThen = wrappedVisit(node->thenTerm);
    SortPtr resultElse = wrappedVisit(node->elseTerm);

    if (resultThen->toString() == resultElse->toString()) {
        ret = resultThen;
    }
}

void TermSorter::visit(const EmpTermPtr& node) {
    ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(const SepTermPtr& node) {
    bool sorted = true;
    auto terms = node->terms;

    for (const auto& term : terms) {
        SortPtr sort = wrappedVisit(term);
        if (sort->name != SORT_BOOL)
            sorted = false;
    }

    if (sorted)
        ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(const WandTermPtr& node) {
    ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(const PtoTermPtr& node) {
    ret = make_shared<Sort>(SORT_BOOL);
}

void TermSorter::visit(const NilTermPtr& node) {
    if (node->sort) {
        ret = ctx->getStack()->expand(node->sort);
    }
}

bool TermSorter::unify(const SortPtr& sort1, const SortPtr& sort2,
                       const vector<string>& params,
                       unordered_map<string, SortPtr>& mapping) {
    if (!sort1 || !sort2)
        return false;

    string sort1Name = sort1->name;
    bool isParam = (find(params.begin(), params.end(), sort1Name) != params.end());

    if (isParam) {
        if (mapping[sort1Name]) {
            return mapping[sort1Name]->toString() == sort2->toString();
        } else {
            mapping[sort1Name] = sort2;
            return true;
        }
    } else {
        if (sort1->arguments.size() != sort2->arguments.size()) {
            return false;
        } else if (sort1->arguments.empty()) {
            return sort1Name == sort2->name;
        } else {
            string sort2Name = sort2->name;

            if (sort1Name != sort2Name || sort1->arguments.size() != sort2->arguments.size()) {
                return false;
            }

            bool fits = true;
            for (size_t i = 0, sz = sort1->arguments.size(); i < sz; i++) {
                fits = fits && unify(sort1->arguments[i], sort2->arguments[i], params, mapping);
            }

            return fits;
        }
    }
}
