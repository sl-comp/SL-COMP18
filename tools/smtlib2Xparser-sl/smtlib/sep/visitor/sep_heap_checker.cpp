#include "sep_heap_checker.h"

#include "sep/sep_term.h"
#include "util/error_messages.h"

#include <algorithm>
#include <iostream>

using namespace std;
using namespace smtlib::sep;

HeapChecker::NodeErrorPtr HeapChecker::addError(const string& message,
                                                const NodePtr& node,
                                                NodeErrorPtr& nodeErr) {
    if (!nodeErr) {
        auto err = std::move(make_shared<Error>(message));
        nodeErr = std::move(make_shared<NodeError>(err, node));
        errors.push_back(nodeErr);
    } else {
        nodeErr->errs.push_back(make_shared<Error>(message));
    }

    return nodeErr;
}

void HeapChecker::addError(const string& message, const NodePtr& node) {
    auto err = std::move(make_shared<Error>(message));
    errors.push_back(std::move(make_shared<NodeError>(err, node)));
}

bool HeapChecker::isValidLocSort(const SortPtr& locSort) {
    const SortPtr& locSortExp = stack->expand(locSort);
    const string& locSortExpStr = locSortExp->toString();

    const auto& levels = stack->getLevels();

    for (const auto& lvl : levels) {
        const auto& heap = lvl->getHeap();
        const auto& found = find_if(heap.begin(), heap.end(),
                                    [&](const pair<SortPtr, SortPtr>& p) {
                                        return locSortExpStr == p.first->toString();
                                    });
        if (found != heap.end()) {
            return true;
        }
    }

    return false;
}

vector<string> HeapChecker::getAcceptedLocDataPairs() {
    const auto& levels = stack->getLevels();
    vector<string> result;

    for (const auto& lvl : levels) {
        const auto& heap = lvl->getHeap();
        for (const auto& pair : heap) {
            stringstream ss;
            ss << "(" << pair.first->toString()
               << ", " << pair.second->toString() << ")";

            result.push_back(ss.str());
        }
    }

    return result;
}

vector<string> HeapChecker::getAcceptedLocSorts() {
    const auto& levels = stack->getLevels();
    vector<string> result;

    for (const auto& lvl : levels) {
        const auto& heap = lvl->getHeap();
        for (const auto& pair : heap) {
            const string& loc = pair.first->toString();
            const auto& found = find_if(result.begin(), result.end(),
                                        [&](const string& str) {
                                            return str == loc;
                                        });

            if(found == result.end()) {
                result.push_back(pair.first->toString());
            }
        }
    }

    return result;
}

void HeapChecker::visitWithStack(const EmpTermPtr& node) {
    if (!node->locSort || !node->dataSort) {
        NodeErrorPtr nodeErr;

        if (!node->locSort)
            nodeErr = addError(ErrorMessages::ERR_UNSPECIFIED_LOC_SORT, node, nodeErr);

        if (!node->dataSort)
            addError(ErrorMessages::ERR_UNSPECIFIED_DATA_SORT, node, nodeErr);

        return;
    }

    HeapEntry found = stack->findDuplicate(make_pair(node->locSort, node->dataSort));
    if (!found.first || !found.second) {
        const string& msg = ErrorMessages::buildLocDataPairUnaccepted(node->locSort, node->dataSort,
                                                                      getAcceptedLocDataPairs());
        addError(msg, node);
    }
}

void HeapChecker::visitWithStack(const PtoTermPtr& node) {
    TermSorterContextPtr ctx = make_shared<TermSorterContext>(stack);
    TermSorterPtr sorter = make_shared<TermSorter>(ctx);

    NodeErrorPtr nodeErr;
    /*if(dynamic_pointer_cast<NilTerm>(node->leftTerm)) {
        nodeErr = addError(ErrorMessages::ERR_PTO_LEFT_NIL, node, nodeErr);
    }*/

    SortPtr leftSort = sorter->run(node->leftTerm);
    SortPtr rightSort = sorter->run(node->rightTerm);

    HeapEntry found = stack->findDuplicate(make_pair(leftSort, rightSort));
    if (!found.first || !found.second) {
        const string& msg = ErrorMessages::buildLocDataPairUnaccepted(leftSort, rightSort,
                                                                      getAcceptedLocDataPairs());
        addError(msg, node, nodeErr);
    }
}

void HeapChecker::visitWithStack(const NilTermPtr& node) {
    if (!node->sort) {
        addError(ErrorMessages::ERR_UNSPECIFIED_NIL_SORT, node);
        return;
    }

    if (!isValidLocSort(node->sort)) {
        const string& msg = ErrorMessages::buildLocSortUnaccepted(node->sort, getAcceptedLocSorts());
        addError(msg, node);
    }
}

bool HeapChecker::check(const NodePtr& node) {
    if (node) {
        visit0(node);
    } else {
        Logger::warning("HeapChecker::run()", "Attempting to check an empty smtlib::sep node");
        return false;
    }

    return errors.empty();
}

string HeapChecker::getErrors() {
    if (errors.empty())
        return "";

    stringstream ss;

    for (const auto& error : errors) {
        if (error->node) {
            ss << error->node->rowLeft << ":" << error->node->colLeft
               << " - " << error->node->rowRight << ":" << error->node->colRight << "   ";

            string nodestr = error->node->toString();
            if (nodestr.length() > 100)
                ss << string(nodestr, 0, 100) << "[...]";
            else
                ss << nodestr;
            ss << endl;
        }

        for (auto& err : error->errs) {
            NodePtr source;
            ss << "\t" << err->message << "." << endl;
        }
        ss << endl;
    }
    ss << endl;

    return ss.str();
}
