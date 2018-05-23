#ifndef SLCOMP_PARSER_AST_SYMBOL_STACK_H
#define SLCOMP_PARSER_AST_SYMBOL_STACK_H

#include "ast_symbol_table.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        class SymbolStack {
        private:
            std::vector<SymbolTablePtr> stack;

            bool equal(const ast::SortPtr& sort1, const ast::SortPtr& sort2);

            bool equal(const std::vector<ast::SortPtr>& signature1,
                       const std::vector<ast::SortPtr>& signature2);

            bool equal(const std::vector<ast::SymbolPtr>& params1,
                       const std::vector<ast::SortPtr>& signature1,
                       const std::vector<ast::SymbolPtr>& params2,
                       const std::vector<ast::SortPtr>& signature2);

            bool equal(const std::vector<ast::SymbolPtr>& params1, const ast::SortPtr& sort1,
                       const std::vector<ast::SymbolPtr>& params2, const ast::SortPtr& sort2,
                       std::unordered_map<std::string, std::string>& mapping);
        public:
            SymbolStack();

            SymbolTablePtr getTopLevel();

            std::vector<SymbolTablePtr>& getLevels();

            bool push();
            bool push(size_t levels);

            bool pop();
            bool pop(size_t levels);

            void reset();

            SortEntryPtr getSortEntry(const std::string& name);
            std::vector<FunEntryPtr> getFunEntry(const std::string& name);
            VarEntryPtr getVarEntry(const std::string& name);

            SortEntryPtr findDuplicate(const SortEntryPtr& entry);
            FunEntryPtr findDuplicate(const FunEntryPtr& entry);
            VarEntryPtr findDuplicate(const VarEntryPtr& entry);

            ast::SortPtr expand(const ast::SortPtr& sort);

            ast::SortPtr replace(const ast::SortPtr&,
                                 std::unordered_map<std::string, ast::SortPtr>& mapping);

            SortEntryPtr tryAdd(const SortEntryPtr& entry);
            FunEntryPtr tryAdd(const FunEntryPtr& entry);
            VarEntryPtr tryAdd(const VarEntryPtr& entry);
        };

        typedef std::shared_ptr<SymbolStack> SymbolStackPtr;
    }
}

#endif //SLCOMP_PARSER_AST_SYMBOL_STACK_H
