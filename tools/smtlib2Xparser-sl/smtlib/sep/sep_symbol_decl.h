/**
 * \file sep_symbol_decl.h
 * \brief Sort and function symbol declarations.
 */

#ifndef SLCOMP_PARSER_SEP_SYMBOL_DECL_H
#define SLCOMP_PARSER_SEP_SYMBOL_DECL_H

#include "sep_abstract.h"
#include "sep_basic.h"
#include "sep_identifier.h"
#include "sep_interfaces.h"
#include "sep_literal.h"
#include "sep_sort.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace sep {
        class Attribute;

        /* =============================== SortSymbolDeclaration ============================== */
        /**
         * Declaration of a sort symbol.
         * Can act as an attribute value.
         */
        class SortSymbolDeclaration : public virtual Node,
                                      public AttributeValue,
                                      public std::enable_shared_from_this<SortSymbolDeclaration> {
        public:
            SimpleIdentifierPtr identifier;
            long arity;
            std::vector<AttributePtr> attributes;

            /**
             * Constructs declaration without attributes.
             * \param identifier    Sort symbol identiier
             * \param arity         Sort arity
             */
            inline SortSymbolDeclaration(SimpleIdentifierPtr identifier, long arity)
                    : identifier(std::move(identifier))
                    , arity(arity) {}

            /**
             * Constructs declaration with attributes.
             * \param identifier    Sort symbol identiier
             * \param arity         Sort arity
             * \param attributes    Sort symbol declaration attributes
             */
            inline SortSymbolDeclaration(SimpleIdentifierPtr identifier,
                                         long arity,
                                         std::vector<AttributePtr> attributes)
                    : identifier(std::move(identifier))
                    , arity(arity)
                    , attributes(std::move(attributes)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =============================== FunSymbolDeclaration =============================== */
        /**
         * A function symbol declaration.
         * Can act as an attribute value.
         */
        class FunSymbolDeclaration : public virtual Node,
                                     public AttributeValue {
        };

        /* ============================= SpecConstFunDeclaration ============================== */
        /**
         * Specification constant function symbol declaration.
         * Can act as an attribute value.
         */
        class SpecConstFunDeclaration : public FunSymbolDeclaration,
                                        public std::enable_shared_from_this<SpecConstFunDeclaration> {
        public:
            SpecConstantPtr constant;
            SortPtr sort;
            std::vector<AttributePtr> attributes;

            /**
            * Constructs declaration without attributes.
            * \param constant      Specification constant
            * \param sort          Function sort
            */
            inline SpecConstFunDeclaration(SpecConstantPtr constant,
                                           SortPtr sort)
                    : constant(std::move(constant))
                    , sort(std::move(sort)) {}

            /**
             * Constructs declaration with attributes.
             * \param constant      Specification constant
             * \param sort          Function sort
             * \param attributes    Function symbol declaration attributes
             */
            inline SpecConstFunDeclaration(SpecConstantPtr constant,
                                           SortPtr sort,
                                           std::vector<AttributePtr> attributes)
                    : constant(std::move(constant))
                    , sort(std::move(sort))
                    , attributes(std::move(attributes)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ========================== MetaSpecConstFunDeclaration =========================== */
        /**
         * Meta specification constant function symbol declaration.
         * Can act as an attribute value.
         */
        class MetaSpecConstFunDeclaration : public FunSymbolDeclaration,
                                            public std::enable_shared_from_this<MetaSpecConstFunDeclaration> {
        public:
            MetaSpecConstantPtr constant;
            SortPtr sort;
            std::vector<AttributePtr> attributes;

            /**
            * Constructs declaration without attributes.
            * \param constant      Meta specification constant
            * \param sort          Function sort
            */
            inline MetaSpecConstFunDeclaration(MetaSpecConstantPtr constant,
                                               SortPtr sort)
                    : constant(std::move(constant))
                    , sort(std::move(sort)) {}

            /**
             * Constructs declaration with attributes.
             * \param constant      Meta specification constant
             * \param sort          Function sort
             * \param attributes    Function symbol declaration attributes
             */
            inline MetaSpecConstFunDeclaration(MetaSpecConstantPtr constant,
                                               SortPtr sort,
                                               std::vector<AttributePtr> attributes)
                    : constant(std::move(constant))
                    , sort(std::move(sort))
                    , attributes(std::move(attributes)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ============================== SimpleFunDeclaration =============================== */
        /**
         * Identifier function symbol declaration.
         * Can act as an attribute value.
         */
        class SimpleFunDeclaration : public FunSymbolDeclaration,
                                     public std::enable_shared_from_this<SimpleFunDeclaration> {
        public:
            SimpleIdentifierPtr identifier;
            std::vector<SortPtr> signature;
            std::vector<AttributePtr> attributes;

        protected:
            SimpleFunDeclaration() = default;

        public:
            /**
             * Constructs declaration without attributes.
             * \param identifier    Function identifier
             * \param signature     Function signature
             */
            inline SimpleFunDeclaration(SimpleIdentifierPtr identifier,
                                        std::vector<SortPtr> signature)
                    : identifier(std::move(identifier))
                    , signature(std::move(signature)) {}

            /**
             * Constructs declaration with attributes.
             * \param identifier    Function identifier
             * \param signature     Function signature
             * \param attributes    Function symbol declaration attributes
             */
            inline SimpleFunDeclaration(SimpleIdentifierPtr identifier,
                                        std::vector<SortPtr> signature,
                                        std::vector<AttributePtr> attributes)
                    : identifier(std::move(identifier))
                    , signature(std::move(signature))
                    , attributes(std::move(attributes)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =============================== ParametricFunDeclaration ================================ */
        /**
        * Parametric function symbol declaration.
        * Can act as an attribute value.
        */
        class ParametricFunDeclaration : public FunSymbolDeclaration,
                                         public std::enable_shared_from_this<ParametricFunDeclaration> {
        public:
            std::vector<std::string> parameters;
            SimpleIdentifierPtr identifier;
            std::vector<SortPtr> signature;
            std::vector<AttributePtr> attributes;

            /**
             * Constructs declaration without attributes.
             * \param parameters    Function parameters
             * \param identifier    Function identifier
             * \param signature     Function signature
             */
            inline ParametricFunDeclaration(std::vector<std::string> parameters,
                                            SimpleIdentifierPtr identifier,
                                            std::vector<SortPtr> signature)
                    : parameters(std::move(parameters))
                    , identifier(std::move(identifier))
                    , signature(std::move(signature)) {}

            /**
             * Constructs declaration with attributes.
             * \param parameters    Function parameters
             * \param identifier    Function identifier
             * \param signature     Function signature
             * \param attributes    Function symbol declaration attributes
             */
            inline ParametricFunDeclaration(std::vector<std::string> parameters,
                                            SimpleIdentifierPtr identifier,
                                            std::vector<SortPtr> signature,
                                            std::vector<AttributePtr> attributes)
                    : parameters(std::move(parameters))
                    , identifier(std::move(identifier))
                    , signature(std::move(signature))
                    , attributes(std::move(attributes)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //SLCOMP_PARSER_SEP_SYMBOL_DECL_H
