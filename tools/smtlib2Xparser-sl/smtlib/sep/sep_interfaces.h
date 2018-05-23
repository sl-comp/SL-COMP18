#ifndef SLCOMP_PARSER_SEP_INTERFACES_H
#define SLCOMP_PARSER_SEP_INTERFACES_H

#include "sep_abstract.h"

namespace smtlib {
    namespace sep {

        class AttributeValue : public virtual Node {
        };

        class SExpression : public virtual Node {
        };

        class Term : public virtual Node {
        };

        class Identifier : public virtual Node,
                           public Term {
        };

        class Index : public virtual Node {
        };

        class SpecConstant : public virtual Node,
                             public SExpression,
                             public Term,
                             public AttributeValue {
        };

        class Pattern : public virtual Node {
        };

        class Constructor : public virtual Node,
                            public Pattern {
        };

    }
}

#endif //SLCOMP_PARSER_SEP_INTERFACES_H
