#ifndef SLCOMP_PARSER_SEP_SYMBOL_UTIL_H
#define SLCOMP_PARSER_SEP_SYMBOL_UTIL_H

#include "sep/sep_abstract.h"
#include "sep/sep_sort.h"
#include "sep/sep_fun.h"

#include <memory>
#include <string>

namespace smtlib {
    namespace sep {
        /* =================================== SymbolEntry ==================================== */
        class SymbolEntry {
        public:
            std::string name;
            sep::NodePtr source;

            inline SymbolEntry() = default;

            inline SymbolEntry(std::string name, sep::NodePtr source)
                    : name(std::move(name))
                    , source(std::move(source)) {}

            virtual ~SymbolEntry();
        };

        typedef std::shared_ptr<SymbolEntry> SymbolEntryPtr;

        /* ===================================== SortEntry ====================================== */
        class SortEntry : public SymbolEntry {
        public:
            size_t arity;
            SortPtr sort;
            std::vector<std::string> params;
            std::vector<AttributePtr> attributes;

            inline SortEntry(std::string name,
                             size_t arity,
                             NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , arity(arity) {}

            inline SortEntry(std::string name,
                             size_t arity,
                             std::vector<AttributePtr> attributes,
                             NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , arity(arity)
                    , attributes(std::move(attributes)) {}

            inline SortEntry(std::string name,
                             size_t arity,
                             std::vector<std::string> params,
                             SortPtr sort,
                             NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , arity(arity)
                    , sort(std::move(sort))
                    , params(std::move(params)) {}

            inline SortEntry(std::string name,
                             size_t arity,
                             std::vector<std::string> params,
                             SortPtr sort,
                             std::vector<AttributePtr> attributes,
                             NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , arity(arity)
                    , sort(std::move(sort))
                    , params(std::move(params))
                    , attributes(std::move(attributes)) {}

        };

        typedef std::shared_ptr<SortEntry> SortEntryPtr;

        /* ===================================== FunEntry ===================================== */
        class FunEntry : public SymbolEntry {
        public:
            std::vector<SortPtr> signature;
            std::vector<std::string> params;
            TermPtr body;
            std::vector<AttributePtr> attributes;

            bool assocR { false };
            bool assocL { false };
            bool chainable { false };
            bool pairwise { false };

            inline FunEntry(std::string name,
                            std::vector<SortPtr> signature,
                            NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , signature(std::move(signature)) {}

            inline FunEntry(std::string name,
                            std::vector<SortPtr> signature,
                            std::vector<AttributePtr> attributes,
                            NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , signature(std::move(signature))
                    , attributes(std::move(attributes)) {}

            inline FunEntry(std::string name,
                            std::vector<SortPtr> signature,
                            TermPtr body,
                            NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , body(std::move(body))
                    , signature(std::move(signature)) {}

            inline FunEntry(std::string name,
                            std::vector<SortPtr> signature,
                            TermPtr body,
                            std::vector<AttributePtr> attributes,
                            NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , body(std::move(body))
                    , signature(std::move(signature))
                    , attributes(std::move(attributes)) {}

            inline FunEntry(std::string name,
                            std::vector<SortPtr> signature,
                            std::vector<std::string> params,
                            NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , signature(std::move(signature))
                    , params(std::move(params)) {}

            inline FunEntry(std::string name,
                            std::vector<SortPtr> signature,
                            std::vector<std::string> params,
                            std::vector<AttributePtr> attributes,
                            NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , signature(std::move(signature))
                    , params(std::move(params))
                    , attributes(std::move(attributes)) {}

            inline FunEntry(std::string name,
                            std::vector<SortPtr> signature,
                            std::vector<std::string> params,
                            TermPtr body,
                            NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , body(std::move(body))
                    , signature(std::move(signature))
                    , params(std::move(params)) {}

            inline FunEntry(std::string name,
                            std::vector<SortPtr> signature,
                            std::vector<std::string> params,
                            TermPtr body,
                            std::vector<AttributePtr> attributes,
                            NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , body(std::move(body))
                    , signature(std::move(signature))
                    , params(std::move(params))
                    , attributes(std::move(attributes)) {}
        };

        typedef std::shared_ptr<FunEntry> FunEntryPtr;

        /* ===================================== VarEntry ===================================== */
        class VarEntry : public SymbolEntry {
        public:
            SortPtr sort;
            TermPtr term;

            inline VarEntry(std::string name,
                            SortPtr sort,
                            NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , sort(std::move(sort)) {}

            inline VarEntry(std::string name,
                            SortPtr sort,
                            TermPtr term,
                            NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , sort(std::move(sort))
                    , term(std::move(term)) {}
        };

        typedef std::shared_ptr<VarEntry> VarEntryPtr;

        /* ================================== DatatypeEntry =================================== */
        class DatatypeEntry : public SymbolEntry {
        public:
            SortEntryPtr sort;
            std::vector<FunEntryPtr> funs;

            inline DatatypeEntry(std::string name, NodePtr source)
                : SymbolEntry(std::move(name), std::move(source)) {}

            inline DatatypeEntry(std::string name,
                                 SortEntryPtr sort,
                                 std::vector<FunEntryPtr> funs,
                                 NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , sort(std::move(sort))
                    , funs(std::move(funs)) {}
        };

        typedef std::shared_ptr<DatatypeEntry> DatatypeEntryPtr;

        /* ==================================== HeapEntry ===================================== */
        typedef std::pair<SortPtr, SortPtr> HeapEntry;
    }
}

#endif //SLCOMP_PARSER_SEP_SYMBOL_UTIL_H
