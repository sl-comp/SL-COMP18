/**
 * \file strat_parser.h
 * \brief Proof strategy parser.
 */

#ifndef SLCOMP_PARSER_SMT_PARSER_H
#define SLCOMP_PARSER_SMT_PARSER_H

#include "ast/ast_abstract.h"

#include <memory>
#include <string>

namespace smtlib {
    /** SMT-LIB parser */
    class Parser {
    private:
        ast::NodePtr ast;
        std::shared_ptr<std::string> filename;
    public:
        ast::NodePtr parse(const std::string& filename);

        /** Get input file */
        std::shared_ptr<std::string> getFilename();

        /** Get the resulting AST */
        ast::NodePtr getAst();

        /** Set the resulting AST */
        void setAst(ast::NodePtr ast);

        /** Report a parsing error */
        void reportError(int lineLeft, int colLeft,
                         int lineRight, int colRight, const char* msg);
    };

    typedef std::shared_ptr<Parser> ParserPtr;
}

#endif //SLCOMP_PARSER_SMT_PARSER_H
