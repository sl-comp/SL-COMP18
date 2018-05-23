/**
 * \file sep_datatype.h
 * \brief SMT-LIB+SEPLOG datatype declarations and their components.
 */

#ifndef SLCOMP_PARSER_SEP_DATATYPE_H
#define SLCOMP_PARSER_SEP_DATATYPE_H

#include "sep_abstract.h"
#include "sep_basic.h"
#include "sep_literal.h"
#include "sep_sort.h"

namespace smtlib {
    namespace sep {
        /* ================================= SortDeclaration ================================== */
        /** A sort declaration (used by the declare-datatypes command). */
        class SortDeclaration : public Node,
                                public std::enable_shared_from_this<SortDeclaration> {
        public:
            std::string name;
            size_t arity;

            /**
             * \param symbol    Datatype (sort) name
             * \param arity     Arity
             */
            inline SortDeclaration(std::string name, size_t arity)
                    : name(std::move(name))
                    , arity(arity) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =============================== SelectorDeclaration ================================ */
        /** A selector declaration (used by constructor declarations). */
        class SelectorDeclaration : public Node,
                                    public std::enable_shared_from_this<SelectorDeclaration> {
        public:
            std::string name;
            SortPtr sort;

            /**
             * \param symbol    Selector name
             * \param sort      Selector sort
             */
            inline SelectorDeclaration(std::string name, SortPtr sort)
                    : name(std::move(name))
                    , sort(std::move(sort)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =============================== ConstructorDeclaration ============================== */
        /** A sort declaration (used by the declare-datatypes command). */
        class ConstructorDeclaration : public Node,
                                       public std::enable_shared_from_this<ConstructorDeclaration> {
        public:
            std::string name;
            std::vector<SelectorDeclarationPtr> selectors;

            /**
             * \param symbol        Constructor name
             * \param selectors     Selectors for the constructor
             */
            inline ConstructorDeclaration(std::string name,
                                          std::vector<SelectorDeclarationPtr> selectors)
                    : name(std::move(name))
                    , selectors(std::move(selectors)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================ DatatypeDeclaration =============================== */
        /** A datatype declaration (used by the declare-datatype and declare-datatypes commands). */
        class DatatypeDeclaration : public Node {
        };

        /* ============================= SimpleDatatypeDeclaration ============================ */
        /** A simple (non-parametric) datatype declaration. */
        class SimpleDatatypeDeclaration : public DatatypeDeclaration,
                                          public std::enable_shared_from_this<SimpleDatatypeDeclaration> {
        public:
            std::vector<ConstructorDeclarationPtr> constructors;

            /**
             * \param constructors  Constructors for this datatype
             */
            inline explicit SimpleDatatypeDeclaration(std::vector<ConstructorDeclarationPtr> constructors)
                    : constructors(std::move(constructors)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* =========================== ParametricDatatypeDeclaration ========================== */
        /** A parametric datatype declaration. */
        class ParametricDatatypeDeclaration : public DatatypeDeclaration,
                                              public std::enable_shared_from_this<ParametricDatatypeDeclaration> {
        public:
            std::vector<std::string> parameters;
            std::vector<ConstructorDeclarationPtr> constructors;

            /**
             * \param params        Parameters for the declaration
             * \param constructors  Constructors for this datatype
             */
            ParametricDatatypeDeclaration(std::vector<std::string> parameters,
                                          std::vector<ConstructorDeclarationPtr> constructors)
                    : parameters(std::move(parameters))
                    , constructors(std::move(constructors)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //SLCOMP_PARSER_SEP_DATATYPE_H
