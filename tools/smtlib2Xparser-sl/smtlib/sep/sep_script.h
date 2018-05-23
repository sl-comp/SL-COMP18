/**
 * \file sep_script
 * \brief SMT-LIB+SEPLOG script.
 */

#ifndef SLCOMP_PARSER_SEP_SCRIPT_H
#define SLCOMP_PARSER_SEP_SCRIPT_H

#include "sep_abstract.h"
#include "sep_command.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace sep {
        /**
         * SMT-LIB+SEPLOG script.
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

#endif //SLCOMP_PARSER_SEP_SCRIPT_H
