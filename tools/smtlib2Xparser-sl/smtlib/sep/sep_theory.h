/**
 * \file sep_theory.h
 * \brief SMT-LIB+SEPLOG theory.
 */

#ifndef SLCOMP_PARSER_SEP_THEORY_H
#define SLCOMP_PARSER_SEP_THEORY_H

#include "sep_abstract.h"
#include "sep_attribute.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace sep {
        /**
         * SMT-LIB+SEPLOG theory.
         * Represents the contents of a theory file.
         */
        class Theory : public Root,
                       public std::enable_shared_from_this<Theory> {
        public:
            std::string name;
            std::vector<AttributePtr> attributes;

            /**
             * Constructs theory without attributes.
             * \param name  Theory name
             */
            inline explicit Theory(std::string name)
                    : name(std::move(name)) {}

            /**
             * Constructs theory with attributes.
             * \param name          Theory name
             * \param attributes    Theory attributes
             */
            inline Theory(std::string name, std::vector<AttributePtr> attributes)
                    : name(std::move(name))
                    , attributes(std::move(attributes)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //SLCOMP_PARSER_SEP_THEORY_H
