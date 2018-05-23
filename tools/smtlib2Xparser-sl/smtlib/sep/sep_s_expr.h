/**
 * \file sep_s_expression.h
 * \brief Compound S-expression.
 */

#ifndef SLCOMP_PARSER_SEP_S_EXPR_H
#define SLCOMP_PARSER_SEP_S_EXPR_H

#include "sep_abstract.h"
#include "sep_interfaces.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace sep {
        /** Compound S-expression. */
        class CompSExpression : public SExpression,
                                public AttributeValue,
                                public std::enable_shared_from_this<CompSExpression> {
        public:
            std::vector<SExpressionPtr> expressions;

            /**
             * \param exprs     Subexpressions
             */
            inline explicit CompSExpression(std::vector<SExpressionPtr> exprs)
                    : expressions(std::move(exprs)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //SLCOMP_PARSER_SEP_S_EXPR_H
