/**
 * \file        execution_settings.cpp
 * \brief       Options for the selected tools
 * 
 * \author      Cristina Serban
 * \author      Mihaela Sighireanu
 * \copyright   See 'LICENSE' file.
 */

#include "execution_settings.h"

using namespace std;
using namespace slcompparser;
using namespace smtlib;
using namespace smtlib::ast;

ExecutionSettings::ExecutionSettings()
: coreTheoryEnabled(true)
, inputMethod(INPUT_NONE) {
}

ExecutionSettings::ExecutionSettings(const ExecutionSettingsPtr& settings) {
    this->coreTheoryEnabled = settings->coreTheoryEnabled;
    this->inputMethod = settings->inputMethod;
    this->filename = settings->filename;
    this->ast = settings->ast;
    this->sortCheckContext = settings->sortCheckContext;
}

void ExecutionSettings::setInputFromFile(string filename) {
    this->filename = std::move(filename);
    this->ast.reset();
    inputMethod = INPUT_FILE;
}

void ExecutionSettings::setInputFromAst(NodePtr ast) {
    this->ast = std::move(ast);
    this->filename = "";
    inputMethod = INPUT_AST;
}

void ExecutionSettings::setOutputFormat(char* format) {
    if (!format)
        this->outputFormat = SL_COMP18;
    else if (strcmp(format, "SL-COMP14"))
        this->outputFormat = SL_COMP14;
    else
        this->outputFormat = SL_COMP18;
}

std::string ExecutionSettings::toStringOutputFormat() {
    switch (this->outputFormat) {
        case SL_COMP14: return std::string("SL_COMP14");
        case ASTERIX:
        case CYCLIST:
        case SLIDE: return std::string("Other");
        default: break;
    }
    return std::string("SL_COMP18");
}
