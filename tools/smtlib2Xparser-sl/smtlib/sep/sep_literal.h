/**
 * \file sep_literal.h
 * \brief SMT-LIB+SEPLOG literals.
 */

#ifndef SLCOMP_PARSER_SEP_LITERAL_H
#define SLCOMP_PARSER_SEP_LITERAL_H

#include "sep_abstract.h"
#include "sep_interfaces.h"

#include <string>

namespace smtlib {
    namespace sep {
        /* ====================================== Literal ===================================== */
        /** Literal containing a generic value */
        template<class T>
        class Literal : public virtual Node {
        public:
            T value;

        protected:
            Literal() = default;

            explicit Literal(T value)
                    : value(std::move(value)) {}
        };

        /* ================================== NumeralLiteral ================================== */
        /**
         * Numeric literal.
         * Can act as an index or a specification constant.
         */
        class NumeralLiteral : public Literal<long>,
                               public Index,
                               public SpecConstant,
                               public std::enable_shared_from_this<NumeralLiteral> {
        public:
            unsigned int base;

            inline NumeralLiteral(long value, unsigned int base)
                    : Literal(value)
                    , base(base) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================== DecimalLiteral ================================== */
        /**
         * Decimal literal.
         * Can act as a specification constant.
         */
        class DecimalLiteral : public Literal<double>,
                               public SpecConstant,
                               public std::enable_shared_from_this<DecimalLiteral> {
        public:
            inline explicit DecimalLiteral(double value)
                    : Literal(value) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================== StringLiteral =================================== */
        /**
         * String literal.
         * Can act as a specification constant.
         */
        class StringLiteral : public Literal<std::string>,
                              public SpecConstant,
                              public std::enable_shared_from_this<StringLiteral> {
        public:
            inline explicit StringLiteral(std::string value)
                    : Literal(std::move(value)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //SLCOMP_PARSER_SEP_LITERAL_H
