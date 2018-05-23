#ifndef SLCOMP_PARSER_SEP_HEAP_CHECKER_H
#define SLCOMP_PARSER_SEP_HEAP_CHECKER_H

#include "sep_visitor_stack.h"
#include "stack/sep_symbol_stack.h"

namespace smtlib {
    namespace sep {

        /* =================================== HeapChecker ==================================== */
        class HeapChecker : public DummyVisitorWithStack0,
                            public std::enable_shared_from_this<HeapChecker> {
        public:
            struct Error {
                std::string message;
                SymbolEntryPtr entry;

                inline explicit Error(std::string message)
                        : message(std::move(message)) {}

                inline Error(std::string message, SymbolEntryPtr entry)
                        : message(std::move(message))
                        , entry(std::move(entry)) {}
            };

            typedef std::shared_ptr<Error> ErrorPtr;

            struct NodeError {
                std::vector<ErrorPtr> errs;
                NodePtr node;

                inline NodeError() = default;

                inline NodeError(ErrorPtr err, NodePtr node)
                        : node(std::move(node)) {
                    errs.push_back(std::move(err));
                }

                inline NodeError(std::vector<ErrorPtr> errs, NodePtr node)
                        : errs(std::move(errs))
                        , node(std::move(node)) {}
            };

            typedef std::shared_ptr<NodeError> NodeErrorPtr;

        private:
            std::vector<NodeErrorPtr> errors;

            bool isValidLocSort(const SortPtr& locSort);
            std::vector<std::string> getAcceptedLocDataPairs();
            std::vector<std::string> getAcceptedLocSorts();

        public:

            NodeErrorPtr addError(const std::string& message,
                                  const NodePtr& node,
                                  NodeErrorPtr& nodeErr);

            void addError(const std::string& message,
                          const NodePtr& node);

            inline explicit HeapChecker() = default;

            void visitWithStack(const EmpTermPtr& node) override;
            void visitWithStack(const PtoTermPtr& node) override;
            void visitWithStack(const NilTermPtr& node) override;

            bool check(const NodePtr& node);
            std::string getErrors();
        };

        typedef std::shared_ptr<HeapChecker> HeapCheckerPtr;
    }
}

#endif //SLCOMP_PARSER_SEP_HEAP_CHECKER_H
