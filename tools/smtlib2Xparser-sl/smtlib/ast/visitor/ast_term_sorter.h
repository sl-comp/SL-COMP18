/**
 * \file ast_term_sorter.h
 * \brief Visitor that determines the sort of a term
 */

#ifndef SLCOMP_PARSER_AST_TERM_SORTER_H
#define SLCOMP_PARSER_AST_TERM_SORTER_H

#include "ast_visitor_extra.h"

#include "stack/ast_symbol_stack.h"
#include "util/configuration.h"

#include <algorithm>

namespace smtlib {
    namespace ast {
        class SortednessChecker;
        typedef std::shared_ptr<SortednessChecker> SortednessCheckerPtr;

        /* ================================ ITermSorterContext ================================ */
        /** Context interface for term sorting */
        class ITermSorterContext {
        public:
            virtual SymbolStackPtr getStack() = 0;
            virtual SortednessCheckerPtr getChecker() = 0;
            virtual ConfigurationPtr getConfiguration() = 0;
        };

        typedef std::shared_ptr<ITermSorterContext> ITermSorterContextPtr;

        /* ==================================== TermSorter ==================================== */
        /** Determines the sort of a term */
        class TermSorter : public DummyVisitor1<SortPtr> {
        private:
            ITermSorterContextPtr ctx;

            static std::vector<SortPtr> extractReturnSorts(const std::vector<FunEntryPtr>& entries,
                                                           size_t arity, bool parametric);

            static void extractReturnSorts(const std::vector<FunEntryPtr>& entries,
                                           size_t arity, bool parametric,
                                           std::vector<SortPtr>& accum);

            static std::vector<SortPtr> extractParamMatches(const std::vector<FunEntryPtr>& entries,
                                                            size_t arity, const SortPtr& sort,
                                                            const SymbolStackPtr& stack);

            static void extractParamMatches(const std::vector<FunEntryPtr>& entries,
                                            size_t arity, const SortPtr& sort,
                                            const SymbolStackPtr& stack,
                                            std::vector<SortPtr>& accum);

            static std::vector<std::string> extractParamNames(const FunEntryPtr& entry);

            /**
             * Attempts to unify two sorts
             * \param sort1     Sort to unify
             * \param sort2     Sort onto which to unify
             * \param params    Sort parameters occurring in sort1 and sort2
             * \param mapping   Mapping of sort parameters to sorts
             */
            static bool unify(const SortPtr& sort1, const SortPtr &sort2,
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

            SortPtr run(const NodePtr& node) override {
                return wrappedVisit(node);
            }
        };

        typedef std::shared_ptr<TermSorter> TermSorterPtr;
    }
}


#endif //SLCOMP_PARSER_AST_TERM_SORTER_H
