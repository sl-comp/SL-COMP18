/**
 * \file ast_attribute.h
 * \brief SMT-LIB+SEPLOG attributes.
 */

#ifndef SLCOMP_PARSER_SEP_ATTR_H
#define SLCOMP_PARSER_SEP_ATTR_H

#include "sep_abstract.h"
#include "sep_basic.h"
#include "sep_interfaces.h"
#include "sep_literal.h"
#include "sep_symbol_decl.h"

#include "util/global_values.h"

#include <vector>

namespace smtlib {
    namespace sep {
        /* ==================================== Attribute ===================================== */
        /** An SMT-LIB+SEPLOG attribute */
        struct Attribute : public Node {
            std::string keyword;

            inline Attribute() = default;

            inline explicit Attribute(std::string keyword)
                    : keyword(std::move(keyword)) {}
        };

        /* ================================= SimpleAttribute ================================== */
        /** An attribute without value */
        class SimpleAttribute : public Attribute,
                                public std::enable_shared_from_this<SimpleAttribute> {
        public:
            inline SimpleAttribute() = default;

            inline explicit SimpleAttribute(std::string keyword)
                    : Attribute(std::move(keyword)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =============================== SExpressionAttribute =============================== */
        /** An attribute with a sep::SExpression value */
        class SExpressionAttribute : public Attribute,
                                     public std::enable_shared_from_this<SExpressionAttribute> {
        public:
            SExpressionPtr value;

            inline SExpressionAttribute() = default;

            inline SExpressionAttribute(std::string keyword, SExpressionPtr value)
                    : Attribute(std::move(keyword))
                    , value(std::move(value)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================= SymbolAttribute ================================== */
        /** An attribute with a sep::Symbol value */
        class SymbolAttribute : public Attribute,
                                public std::enable_shared_from_this<SymbolAttribute> {
        public:
            std::string value;

            inline SymbolAttribute() = default;

            inline SymbolAttribute(std::string keyword, std::string value)
                    : Attribute(std::move(keyword))
                    , value(std::move(value)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================= BooleanAttribute ================================= */
        /** An attribute with a boolean value */
        class BooleanAttribute : public Attribute,
                                 public std::enable_shared_from_this<BooleanAttribute> {
        public:
            bool value{};

            inline BooleanAttribute() = default;

            inline BooleanAttribute(std::string keyword, bool value)
                    : Attribute(std::move(keyword))
                    , value(value) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================= NumeralAttribute ================================= */
        /** An attribute with a sep::NumeralLiteral value */
        class NumeralAttribute : public Attribute,
                                 public std::enable_shared_from_this<NumeralAttribute> {
        public:
            NumeralLiteralPtr value;

            inline NumeralAttribute() = default;

            inline NumeralAttribute(std::string symbol, NumeralLiteralPtr value)
                    : Attribute(std::move(symbol))
                    , value(std::move(value)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================= DecimalAttribute ================================= */
        /** An attribute with a sep::DecimalLiteal value */
        class DecimalAttribute : public Attribute,
                                 public std::enable_shared_from_this<DecimalAttribute> {
        public:
            DecimalLiteralPtr value;

            inline DecimalAttribute() = default;

            inline DecimalAttribute(std::string keyword, DecimalLiteralPtr value)
                    : Attribute(std::move(keyword))
                    , value(std::move(value)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================= StringAttribute ================================== */
        /** An attribute with a sep::StringLiteral value */
        class StringAttribute : public Attribute,
                                public std::enable_shared_from_this<StringAttribute> {
        public:
            StringLiteralPtr value;

            inline StringAttribute() = default;

            inline StringAttribute(std::string keyword, StringLiteralPtr value)
                    : Attribute(std::move(keyword))
                    , value(std::move(value)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================ TheoriesAttribute ================================= */
        /** An attribute with a list of theory names value */
        class TheoriesAttribute : public Attribute,
                                  public std::enable_shared_from_this<TheoriesAttribute> {
        public:
            std::vector<std::string> theories;

            inline TheoriesAttribute()
                    : Attribute(KW_THEORIES) {}

            inline explicit TheoriesAttribute(std::vector<std::string> theories)
                    : theories(std::move(theories)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================== SortsAttribute ================================== */
        /** An attribute with a list of sep::SortSymbolDeclaration value */
        class SortsAttribute : public Attribute,
                               public std::enable_shared_from_this<SortsAttribute> {
        public:
            std::vector<SortSymbolDeclarationPtr> declarations;

            inline SortsAttribute()
                    : Attribute(KW_SORTS) {}

            inline explicit SortsAttribute(std::vector<SortSymbolDeclarationPtr> decls)
                    : declarations(std::move(decls)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================== FunsAttribute =================================== */
        /** An attribute with a list of sep::FunSymbolDeclaration value */
        class FunsAttribute : public Attribute,
                              public std::enable_shared_from_this<FunsAttribute> {
        public:
            std::vector<FunSymbolDeclarationPtr> declarations;

            inline FunsAttribute()
                    : Attribute(KW_FUNS) {}

            inline explicit FunsAttribute(std::vector<FunSymbolDeclarationPtr> decls)
                    : declarations(std::move(decls)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //SLCOMP_PARSER_SEP_ATTR_H
