/**
 * \file ast_abstract.h
 * \brief Abstract SMT-LIB data structures.
 */

#ifndef SLCOMP_PARSER_AST_ABSTRACT_H
#define SLCOMP_PARSER_AST_ABSTRACT_H

#include "ast_classes.h"

#include "visitor/ast_visitor.h"

#include <string>
#include <memory>

namespace smtlib {
    namespace ast {
        /* ======================================= Node ======================================= */
        /** Node of the SMT-LIB abstract syntax tree */
        class Node {
        public:
            int rowLeft{0};
            int rowRight{0};
            int colLeft{0};
            int colRight{0};
            std::shared_ptr<std::string> filename;

            inline Node() = default;

            /** Accept a visitor */
            virtual void accept(class Visitor0* visitor) = 0;

            /** Get string representation of the node */
            virtual std::string toString() = 0;
        };

        /** Root of the SMT-LIB abstract syntax tree */
        class Root : public Node {
        };
    }
}

#endif //SLCOMP_PARSER_AST_ABSTRACT_H
