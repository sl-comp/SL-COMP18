#include "execution_settings.h"

using namespace std;
using namespace slcompparser;
using namespace smtlib;
using namespace smtlib::ast;

ExecutionSettings::ExecutionSettings()
        : coreTheoryEnabled(true)
        , inputMethod(INPUT_NONE) {}

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
