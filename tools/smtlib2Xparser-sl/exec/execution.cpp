/**
 * \file        execution.cpp
 * \brief       Handling parsing, type checking, and translation
 *
 * \author      Cristina Serban
 * \author      Mihaela Sighireanu
 * \copyright   See 'LICENSE' file.
 */

#include "execution.h"

#include "ast/ast_script.h"
#include "sep/sep_script.h"
#include "transl/sep_translator.h"
#include "util/global_values.h"
#include "visitor/ast_syntax_checker.h"
#include "visitor/ast_sortedness_checker.h"
#include "visitor/sep_heap_checker.h"
#include "visitor/sep_pp_slcomp14.h"

#include <iostream>

using namespace std;
using namespace slcompparser;
using namespace smtlib;
using namespace smtlib::ast;

Execution::Execution()
: settings(make_shared<ExecutionSettings>()) {
    parseAttempted = false;
    parseSuccessful = false;
    syntaxCheckAttempted = false;
    syntaxCheckSuccessful = false;
    sortednessCheckAttempted = false;
    sortednessCheckSuccessful = false;
}

Execution::Execution(const ExecutionSettingsPtr& settings)
: settings(make_shared<ExecutionSettings>(settings)) {
    this->settings = settings;
    if (settings->getInputMethod() == ExecutionSettings::InputMethod::INPUT_AST) {
        ast = settings->getInputAst();
        parseAttempted = true;
        parseSuccessful = true;
    } else {
        parseAttempted = false;
        parseSuccessful = false;
    }

    syntaxCheckAttempted = false;
    syntaxCheckSuccessful = false;
    sortednessCheckAttempted = false;
    sortednessCheckSuccessful = false;
}

bool Execution::parse() {
    if (parseAttempted)
        return parseSuccessful;

    parseAttempted = true;

    if (settings->getInputMethod() == ExecutionSettings::InputMethod::INPUT_NONE) {
        Logger::error("SmtExecution::parse()", "No input provided");
        return false;
    }

    if (settings->getInputMethod() == ExecutionSettings::InputMethod::INPUT_FILE) {
        ParserPtr parser = make_shared<Parser>();
        ast = parser->parse(settings->getInputFile());
        if (ast) {
            parseSuccessful = true;
        } else {
            //Logger::error("SmtExecution::parse()", "Stopped due to previous errors");
        }
    }

    return parseSuccessful;
}

bool Execution::checkSyntax() {
    if (syntaxCheckAttempted)
        return syntaxCheckSuccessful;

    syntaxCheckAttempted = true;

    if (!parse()) {
        //Logger::error("SmtExecution::checkSyntax()", "Stopped due to previous errors");
        return false;
    }

    //SyntaxCheckerPtr chk = make_shared<SyntaxChecker>();
    SyntaxCheckerPtr chk = shared_ptr<SyntaxChecker>(new SyntaxChecker());
    syntaxCheckSuccessful = chk->check(ast);

    if (!syntaxCheckSuccessful) {
        if (settings->getInputMethod() == ExecutionSettings::InputMethod::INPUT_AST) {
            Logger::syntaxError("SmtExecution::checkSyntax()", chk->getErrors().c_str());
        } else {
            Logger::syntaxError("SmtExecution::checkSyntax()",
                    settings->getInputFile().c_str(), chk->getErrors().c_str());
        }
    }

    return syntaxCheckSuccessful;
}

bool Execution::checkSortedness() {
    if (sortednessCheckAttempted)
        return sortednessCheckSuccessful;

    sortednessCheckAttempted = true;

    if (!checkSyntax()) {
        //Logger::error("SmtExecution::checkSortedness()", "Stopped due to previous errors");
        return false;
    }

    SortednessCheckerPtr chk;

    if (settings->getSortCheckContext())
        chk = make_shared<SortednessChecker>(settings->getSortCheckContext());
    else
        chk = make_shared<SortednessChecker>();

    if (settings->isCoreTheoryEnabled())
        chk->loadTheory(THEORY_CORE);
    sortednessCheckSuccessful = chk->check(ast);

    if (!sortednessCheckSuccessful) {
        if (settings->getInputMethod() == ExecutionSettings::InputMethod::INPUT_AST) {
            Logger::sortednessError("SmtExecution::checkSortedness()", chk->getErrors().c_str());
        } else {
            Logger::sortednessError("SmtExecution::checkSortedness()",
                    settings->getInputFile().c_str(), chk->getErrors().c_str());
        }
    }

    return sortednessCheckSuccessful;
}

bool Execution::checkHeap() {
    if (heapCheckAttempted)
        return heapCheckSuccessful;

    heapCheckAttempted = true;

    if (!checkSortedness()) {
        //Logger::error("SmtExecution::checkHeap()", "Stopped due to previous errors");
        return false;
    }

    ast::ScriptPtr astScript = dynamic_pointer_cast<Script>(ast);
    if (astScript) {
        sep::TranslatorPtr transl = make_shared<sep::Translator>();
        sepScript = transl->translate(astScript);

        sep::HeapCheckerPtr checker = make_shared<sep::HeapChecker>();
        heapCheckSuccessful = checker->check(sepScript);

        if (!heapCheckSuccessful) {
            Logger::heapError("SmtExecution::checkHeap()", checker->getErrors().c_str());
        }
    }

    return heapCheckSuccessful;
}

bool Execution::translate() {
    if (!heapCheckAttempted ||
            !heapCheckSuccessful ||
            !sepScript) {
        Logger::error("SmtExecution::translate()", "Stopped due to previous errors");
        return false;
    }

    switch (settings->getOutputFormat()) {
	case ExecutionSettings::OutputFormat::SL_COMP14 : {
            sep::Pp_SLCOMP14Ptr pp = make_shared<sep::Pp_SLCOMP14>();
            return pp->run(sepScript);
	}
	case ExecutionSettings::OutputFormat::SL_COMP18 : {
	    std::cout << sepScript->toString();
	    return true;
	}
	default: {
            std::string msg = "Translation to the " + settings->toStringOutputFormat()
                + " format is not supported yet!";
            Logger::warning("SmtExecution::translate()", msg.data());
            return false; // TODO
	}
    }
}
