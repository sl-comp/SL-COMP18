/**
 * \file ast_s_expression.h
 * \brief Compound S-expression.
 */

#ifndef SLCOMP_PARSER_AST_S_EXPR_H
#define SLCOMP_PARSER_AST_S_EXPR_H

#include "ast_abstract.h"
#include "ast_interfaces.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        /** Compound S-expression. */
        class CompSExpression : public SExpression,
                                public AttributeValue,
                                public std::enable_shared_from_this<CompSExpression> {
        public:
            std::vector<SExpressionPtr> expressions;

            /**
             * \param expressions     Subexpressions
             */
            inline explicit CompSExpression(std::vector<SExpressionPtr> expressions)
                    : expressions(std::move(expressions)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //SLCOMP_PARSER_AST_S_EXPR_H
