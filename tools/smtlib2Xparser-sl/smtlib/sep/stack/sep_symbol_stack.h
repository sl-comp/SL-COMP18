#ifndef SLCOMP_PARSER_SEP_SYMBOL_STACK_H
#define SLCOMP_PARSER_SEP_SYMBOL_STACK_H

#include "sep_symbol_table.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace sep {
        class SymbolStack {
        private:
            std::vector<SymbolTablePtr> stack;

            bool equal(const SortPtr& sort1, const SortPtr& sort2);

            bool equal(const std::vector<SortPtr>& signature1,
                       const std::vector<SortPtr>& signature2);

            bool equal(const std::vector<std::string>& params1,
                       const std::vector<SortPtr>& signature1,
                       const std::vector<std::string>& params2,
                       const std::vector<SortPtr>& signature2);

            bool equal(const std::vector<std::string>& params1, const SortPtr& sort1,
                       const std::vector<std::string>& params2, const SortPtr& sort2,
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
            HeapEntry findDuplicate(const HeapEntry& entry);

            SortPtr expand(const SortPtr& sort);

            SortPtr replace(const SortPtr&,
                            std::unordered_map<std::string, SortPtr>& mapping);

            SortEntryPtr tryAdd(const SortEntryPtr& entry);
            FunEntryPtr tryAdd(const FunEntryPtr& entry);
            VarEntryPtr tryAdd(const VarEntryPtr& entry);
            HeapEntry tryAdd(const HeapEntry& entry);
        };

        typedef std::shared_ptr<SymbolStack> SymbolStackPtr;
    }
}

#endif //SLCOMP_PARSER_SEP_SYMBOL_STACK_H
