/**
 * \file ast_logic
 * \brief SMT-LIB logic.
 */

#ifndef SLCOMP_PARSER_AST_LOGIC_H
#define SLCOMP_PARSER_AST_LOGIC_H

#include "ast_abstract.h"
#include "ast_attribute.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        /** Represents the contents of a logic file. */
        class Logic : public Root,
                      public std::enable_shared_from_this<Logic> {
        public:
            SymbolPtr name;
            std::vector<AttributePtr> attributes;
        
            /**
             * Constructs logic without attributes.
             * \param name          Logic name
             */
            inline explicit Logic(SymbolPtr name)
                    : name(std::move(name)) {}

            /**
             * Constructs logic with attributes.
             * \param name          Logic name
             * \param attributes    Logic attributes
             */
            inline Logic(SymbolPtr name, std::vector<AttributePtr> attributes)
                    : name(std::move(name))
                    , attributes(std::move(attributes)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //SLCOMP_PARSER_AST_LOGIC_H
