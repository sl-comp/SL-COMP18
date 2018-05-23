#include "smtlib_parser.h"

#include "util/logger.h"
#include "visitor/ast_syntax_checker.h"
#include "visitor/ast_sortedness_checker.h"

#include "smtlib-glue.h"

#include <string>
#include <sstream>
#include <iostream>

extern "C" {
extern FILE* smt_yyin;
}

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

shared_ptr<Node> Parser::parse(const string& filename) {
    smt_yyin = fopen(filename.c_str(), "r");
    if (smt_yyin) {
        this->filename = make_shared<string>(filename.c_str());
        smt_yyparse(this);
        fclose(smt_yyin);
    } else {
        stringstream ss;
        ss << "Unable to open file '" << filename << "'";
        Logger::error("Parser::parse()", ss.str().c_str());
    }
    return ast;
}

shared_ptr<string> Parser::getFilename() {
    return filename;
}

void Parser::setAst(NodePtr ast) {
    if (ast) {
        this->ast = ast;
    }
}

NodePtr Parser::getAst() {
    return ast;
}

void Parser::reportError(int lineLeft, int colLeft,
                         int lineRight, int colRight, const char* msg) {
    Logger::parsingError(lineLeft, colLeft, lineRight, colRight, filename->c_str(), msg);
}
