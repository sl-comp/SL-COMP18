/**
 * \file sep_abstract.h
 * \brief Abstract SMT-LIB+SEPLOG data structures.
 */
#ifndef SLCOMP_PARSER_SEP_ABSTRACT_H
#define SLCOMP_PARSER_SEP_ABSTRACT_H

#include "sep_classes.h"

#include "visitor/sep_visitor.h"

#include <memory>
#include <string>

namespace smtlib {
    namespace sep {
        /** Node of the SMT-LIB+SEPLOG hierarchy */
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

        /** Root of the SMT-LIB+SEPLOG hierarchy */
        class Root : public Node {
        };
    }
}

#endif //SLCOMP_PARSER_SEP_ABSTRACT_H
