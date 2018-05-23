/**
 * \file ast_script
 * \brief SMT-LIB script.
 */

#ifndef SLCOMP_PARSER_AST_SCRIPT_H
#define SLCOMP_PARSER_AST_SCRIPT_H

#include "ast_abstract.h"
#include "ast_basic.h"
#include "ast_command.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        /**
         * SMT-LIB script.
         * Represents the contents of a query file.
         */
        class Script : public Root,
                       public std::enable_shared_from_this<Script> {
        public:
            std::vector<CommandPtr> commands;
        
            /**
             * Default constructor
             */
            inline Script() = default;

            /**
             * \param cmds    Command list
             */
            inline explicit Script(std::vector<CommandPtr> commands)
                    : commands(std::move(commands)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //SLCOMP_PARSER_AST_SCRIPT_H
