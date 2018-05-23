#ifndef SLCOMP_PARSER_AST_SYMBOL_UTIL_H
#define SLCOMP_PARSER_AST_SYMBOL_UTIL_H

#include "ast/ast_basic.h"
#include "ast/ast_term.h"

#include <memory>
#include <string>

namespace smtlib {
    namespace ast {
        /* =================================== SymbolEntry ==================================== */
        class SymbolEntry {
        public:
            std::string name;
            ast::NodePtr source;

            inline SymbolEntry() = default;

            inline SymbolEntry(std::string name, ast::NodePtr source)
                    : name(std::move(name))
                    , source(std::move(source)) {}

            virtual ~SymbolEntry();
        };

        typedef std::shared_ptr<SymbolEntry> SymbolEntryPtr;

        /* =================================== SortDefEntry =================================== */
        class SortDefEntry {
        public:
            std::vector<ast::SymbolPtr> params;
            ast::SortPtr sort;

            inline SortDefEntry(std::vector<ast::SymbolPtr> params,
                               ast::SortPtr sort)
                    : params(std::move(params))
                    , sort(std::move(sort)) {}
        };

        typedef std::shared_ptr<SortDefEntry> SortDefEntryPtr;

        /* ==================================== SortEntry ===================================== */
        class SortEntry : public SymbolEntry {
        public:
            size_t arity;
            SortDefEntryPtr definition;
            std::vector<ast::AttributePtr> attributes;

            inline SortEntry(std::string name,
                            size_t arity,
                            ast::NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , arity(arity) {}

            inline SortEntry(std::string name,
                            size_t arity,
                            std::vector<ast::AttributePtr> attributes,
                            ast::NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , arity(arity)
                    , attributes(std::move(attributes)) {}

            inline SortEntry(std::string name,
                            size_t arity,
                            std::vector<ast::SymbolPtr> params,
                            ast::SortPtr sort,
                            ast::NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , arity(arity)
                    , definition(std::make_shared<SortDefEntry>(std::move(params), std::move(sort))) {}

            inline SortEntry(std::string name,
                            size_t arity,
                            std::vector<ast::SymbolPtr> params,
                            ast::SortPtr sort,
                            std::vector<ast::AttributePtr> attributes,
                            ast::NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , arity(arity)
                    , attributes(std::move(attributes))
                    , definition(std::make_shared<SortDefEntry>(std::move(params), std::move(sort))) {}
        };

        typedef std::shared_ptr<SortEntry> SortEntryPtr;

        /* ===================================== FunEntry ===================================== */
        class FunEntry : public SymbolEntry {
        public:
            std::vector<ast::SortPtr> signature;
            std::vector<ast::SymbolPtr> params;
            ast::TermPtr body;
            std::vector<ast::AttributePtr> attributes;

            bool assocR { false };
            bool assocL { false };
            bool chainable { false };
            bool pairwise { false };

            inline FunEntry(std::string name,
                           std::vector<ast::SortPtr> signature,
                           ast::NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , signature(std::move(signature)) {}

            inline FunEntry(std::string name,
                           std::vector<ast::SortPtr> signature,
                           ast::TermPtr body,
                           ast::NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , signature(std::move(signature))
                    , body(std::move(body)) {}

            inline FunEntry(std::string name,
                           std::vector<ast::SortPtr> signature,
                           std::vector<ast::SymbolPtr> params,
                           ast::NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , signature(std::move(signature))
                    , params(std::move(params)) {}

            inline FunEntry(std::string& name,
                           std::vector<ast::SortPtr> signature,
                           std::vector<ast::SymbolPtr> params,
                           ast::TermPtr body,
                           ast::NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , signature(std::move(signature))
                    , params(std::move(params))
                    , body(std::move(body)) {}

            inline FunEntry(std::string name,
                           std::vector<ast::SortPtr> signature,
                           std::vector<ast::AttributePtr> attributes,
                           ast::NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , signature(std::move(signature))
                    , attributes(std::move(attributes)) {}

            inline FunEntry(std::string name,
                           std::vector<ast::SortPtr> signature,
                           ast::TermPtr body,
                           std::vector<ast::AttributePtr> attributes,
                           ast::NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , signature(std::move(signature))
                    , body(std::move(body))
                    , attributes(std::move(attributes)) {}

            inline FunEntry(std::string name,
                           std::vector<ast::SortPtr> signature,
                           std::vector<ast::SymbolPtr> params,
                           std::vector<ast::AttributePtr> attributes,
                           ast::NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , signature(std::move(signature))
                    , params(std::move(params))
                    , attributes(std::move(attributes)) {}

            inline FunEntry(std::string name,
                           std::vector<ast::SortPtr> signature,
                           std::vector<ast::SymbolPtr> params,
                           ast::TermPtr body,
                           std::vector<ast::AttributePtr> attributes,
                           ast::NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , signature(std::move(signature))
                    , params(std::move(params))
                    , attributes(std::move(attributes))
                    , body(std::move(body)) {}
        };

        typedef std::shared_ptr<FunEntry> FunEntryPtr;

        /* ===================================== VarEntry ===================================== */
        class VarEntry : public SymbolEntry {
        public:
            ast::SortPtr sort;
            ast::TermPtr term;

            inline VarEntry(std::string name,
                           ast::SortPtr sort,
                           ast::NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , sort(std::move(sort)) {}

            inline VarEntry(std::string name,
                           ast::SortPtr sort,
                           ast::TermPtr term,
                           ast::NodePtr source)
                    : SymbolEntry(std::move(name), std::move(source))
                    , sort(std::move(sort))
                    , term(std::move(term)) {}
        };

        typedef std::shared_ptr<VarEntry> VarEntryPtr;
    }
}
#endif //SLCOMP_PARSER_AST_SYMBOL_UTIL_H
