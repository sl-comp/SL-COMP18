/**
 * \file ast_theory.h
 * \brief SMT-LIB theory.
 */

#ifndef SLCOMP_PARSER_AST_THEORY_H
#define SLCOMP_PARSER_AST_THEORY_H

#include "ast_abstract.h"
#include "ast_attribute.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {

        /**
         * SMT-LIB theory.
         * Represents the contents of a theory file.
         */
        class Theory : public Root,
                       public std::enable_shared_from_this<Theory> {
        public:
            SymbolPtr name;
            std::vector<AttributePtr> attributes;

            /**
             * Constructs theory without attributes.
             * \param name  Theory name
             */
            inline explicit Theory(SymbolPtr name)
                    : name(std::move(name)) {}

            /**
             * Constructs theory with attributes.
             * \param name          Theory name
             * \param attributes    Theory attributes
             */
            inline Theory(SymbolPtr name, std::vector<AttributePtr> attributes)
                    : name(std::move(name))
                    , attributes(std::move(attributes)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //SLCOMP_PARSER_AST_THEORY_H
