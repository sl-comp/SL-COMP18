#ifndef SLCOMP_PARSER_SEP_TERM_SORTER_H
#define SLCOMP_PARSER_SEP_TERM_SORTER_H

#include "visitor/sep_visitor.h"
#include "visitor/sep_visitor_extra.h"

#include "stack/sep_symbol_stack.h"

namespace smtlib {
    namespace sep {
        class ITermSorterContext {
        public:
            virtual SymbolStackPtr getStack() = 0;
        };

        typedef std::shared_ptr<ITermSorterContext> ITermSorterContextPtr;

        /* ================================ ITermSorterContext ================================ */
        /** Context interface for term sorting */
        class TermSorterContext : public ITermSorterContext {
        private:
            SymbolStackPtr stack;
        public:
            inline explicit TermSorterContext(SymbolStackPtr stack)
                    : stack(std::move(stack)) {}

            inline SymbolStackPtr getStack() override { return stack; }

            inline void setStack(const SymbolStackPtr& stack) { this->stack = stack; }
        };

        typedef std::shared_ptr<TermSorterContext> TermSorterContextPtr;

        /* ==================================== TermSorter ==================================== */
        /** Determines the sort of a term */
        class TermSorter : public DummyVisitor1<SortPtr> {
        private:
            ITermSorterContextPtr ctx;

            static bool unify(const SortPtr& sort1, const SortPtr& sort2,
                              const std::vector<std::string>& params,
                              std::unordered_map<std::string, SortPtr>& mapping);

        public:
            inline explicit TermSorter(ITermSorterContextPtr ctx)
                    : ctx(std::move(ctx)) {}

            void visit(const SimpleIdentifierPtr& node) override;
            void visit(const QualifiedIdentifierPtr& node) override;
            void visit(const DecimalLiteralPtr& node) override;
            void visit(const NumeralLiteralPtr& node) override;
            void visit(const StringLiteralPtr& node) override;

            void visit(const QualifiedTermPtr& node) override;
            void visit(const LetTermPtr& node) override;
            void visit(const ForallTermPtr& node) override;
            void visit(const ExistsTermPtr& node) override;
            void visit(const MatchTermPtr& node) override;
            void visit(const AnnotatedTermPtr& node) override;

            void visit(const TrueTermPtr& node) override;
            void visit(const FalseTermPtr& node) override;
            void visit(const NotTermPtr& node) override;
            void visit(const ImpliesTermPtr& node) override;
            void visit(const AndTermPtr& node) override;
            void visit(const OrTermPtr& node) override;
            void visit(const XorTermPtr& node) override;
            void visit(const EqualsTermPtr& node) override;
            void visit(const DistinctTermPtr& node) override;
            void visit(const IteTermPtr& node) override;

            void visit(const EmpTermPtr& node) override;
            void visit(const SepTermPtr& node) override;
            void visit(const WandTermPtr& node) override;
            void visit(const PtoTermPtr& node) override;
            void visit(const NilTermPtr& node) override;

            SortPtr run(const NodePtr& node) override {
                return wrappedVisit(node);
            }
        };

        typedef std::shared_ptr<TermSorter> TermSorterPtr;
    }
}

#endif //SLCOMP_PARSER_SEP_TERM_SORTER_H
