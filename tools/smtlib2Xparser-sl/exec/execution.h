/**
 * \file execution.h
 * \brief Execution handling.
 */

#ifndef SLCOMP_PARSER_EXECUTION_H
#define SLCOMP_PARSER_EXECUTION_H

#include "execution_settings.h"

#include "parser/smtlib_parser.h"
#include "util/global_typedef.h"

#include <memory>

namespace slcompparser {
    /** Class handling the execution of the project */
    class Execution {
    private:
        ExecutionSettingsPtr settings;
        smtlib::ast::NodePtr ast;

        bool parseAttempted, parseSuccessful;
        bool syntaxCheckAttempted, syntaxCheckSuccessful;
        bool sortednessCheckAttempted, sortednessCheckSuccessful;
        bool heapCheckAttempted, heapCheckSuccessful;

    public:
        /** Execution instance with default settings */
        Execution();

        /** Execution instance with specific settings */
        explicit Execution(const ExecutionSettingsPtr& settings);

        /** Parse an input file */
        bool parse();

        /** Check the syntax of an input file */
        bool checkSyntax();

        /** Check the sortedness of an input file */
        bool checkSortedness();

        bool checkHeap();
    };

    typedef std::shared_ptr<Execution> ExecutionPtr;
}

#endif //SLCOMP_PARSER_EXECUTION_H
