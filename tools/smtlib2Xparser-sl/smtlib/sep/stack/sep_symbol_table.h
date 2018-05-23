#ifndef SLCOMP_PARSER_SEP_SYMBOL_TABLE_H
#define SLCOMP_PARSER_SEP_SYMBOL_TABLE_H

#include "sep_symbol_util.h"

#include <unordered_map>

namespace smtlib {
    namespace sep {
        typedef std::unordered_map<std::string, SortEntryPtr> SortEntryMap;
        typedef std::unordered_map<std::string, std::vector<FunEntryPtr>> FunEntryMap;
        typedef std::unordered_map<std::string, VarEntryPtr> VarEntryMap;
        typedef std::vector<std::pair<SortPtr, SortPtr>> HeapEntryMap;

        class SymbolTable {
        private:
            SortEntryMap sorts;
            FunEntryMap funs;
            VarEntryMap vars;
            HeapEntryMap heap;

        public:
            inline SortEntryMap& getSorts() {
                return sorts;
            }

            inline FunEntryMap& getFuns() {
                return funs;
            }

            inline VarEntryMap& getVars() {
                return vars;
            }

            inline HeapEntryMap& getHeap() {
                return heap;
            }

            SortEntryPtr getSortEntry(const std::string& name);
            std::vector<FunEntryPtr> getFunEntry(const std::string& name);
            VarEntryPtr getVarEntry(const std::string& name);

            bool add(const SortEntryPtr& entry);
            bool add(const FunEntryPtr& entry);
            bool add(const VarEntryPtr& entry);
            bool add(const HeapEntry& entry);

            void reset();
        };

        typedef std::shared_ptr<SymbolTable> SymbolTablePtr;
    }
}

#endif //SLCOMP_PARSER_SEP_SYMBOL_TABLE_H
