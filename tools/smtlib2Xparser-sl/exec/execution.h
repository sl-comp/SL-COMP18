/**
 * \file        execution.h
 * \brief       Handling parsing, type checking, and translation
 * 
 * \author      Cristina Serban
 * \author      Mihaela Sighireanu
 * \copyright   See 'LICENSE' file.
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
        smtlib::sep::ScriptPtr sepScript;

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

        /** Check the type of the heap constructs in the input file */
        bool checkHeap();

        /** Translate an input file in SMT-LIB for Separation Logic */
        bool translate();
    };

    typedef std::shared_ptr<Execution> ExecutionPtr;
}

#endif //SLCOMP_PARSER_EXECUTION_H
