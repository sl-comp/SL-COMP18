/**
 * \file sep_logic
 * \brief SMT-LIB+SEPLOG logic.
 */

#ifndef SLCOMP_PARSER_SEP_LOGIC_H
#define SLCOMP_PARSER_SEP_LOGIC_H

#include "sep_abstract.h"
#include "sep_attribute.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace sep {
        /**
         * SMT-LIB+SEPLOG logic.
         * Represents the contents of a logic file.
         */
        class Logic : public Root,
                      public std::enable_shared_from_this<Logic> {
        public:
            std::string name;
            std::vector<AttributePtr> attributes;

            /**
             * Constructs logic without attributes.
             * \param name          Logic name
             */
            inline explicit Logic(std::string name)
                    : name(std::move(name)) {}

            /**
             * Constructs logic with attributes.
             * \param name          Logic name
             * \param attributes    Logic attributes
             */
            inline Logic(std::string name, std::vector<AttributePtr> attributes)
                    : name(std::move(name))
                    , attributes(std::move(attributes)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //SLCOMP_PARSER_SEP_LOGIC_H
