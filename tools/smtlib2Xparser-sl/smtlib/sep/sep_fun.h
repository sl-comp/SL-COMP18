/**
 * \file sep_fun.h
 * \brief Function declaration and definition.
 */

#ifndef SLCOMP_PARSER_SEP_FUN_H
#define SLCOMP_PARSER_SEP_FUN_H

#include "sep_abstract.h"
#include "sep_basic.h"
#include "sep_interfaces.h"
#include "sep_sort.h"
#include "sep_variable.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace sep {
        /* =============================== FunctionDeclaration ================================ */
        /** A function declaration. */
        class FunctionDeclaration : public Node,
                                    public std::enable_shared_from_this<FunctionDeclaration> {
        public:
            std::string name;
            std::vector<SortedVariablePtr> parameters;
            SortPtr sort;

            /**
             * \param symbol        Name of the function
             * \param parameters    List of parameters
             * \param sort          Sort of the return value
             */
            inline FunctionDeclaration(std::string name,
                                       std::vector<SortedVariablePtr> parameters,
                                       SortPtr sort)
                    : name(std::move(name))
                    , parameters(std::move(parameters))
                    , sort(std::move(sort)) {}

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };

        /* ================================ FunctionDefinition ================================ */
        /** A function definition. */
        class FunctionDefinition : public Node,
                                   public std::enable_shared_from_this<FunctionDefinition> {
        public:
            FunctionDeclarationPtr signature;
            TermPtr body;

            /**
             * \param signature    Function signature
             * \param body         Function body
             */
            inline FunctionDefinition(FunctionDeclarationPtr signature,
                                      TermPtr body)
                    : signature(std::move(signature))
                    , body(std::move(body)) {}

            /**
             * \param symbol        Name of the function
             * \param parameters    List of parameters
             * \param type          Sort of the return value
             * \param body          Function body
             */
            inline FunctionDefinition(std::string name,
                                      std::vector<SortedVariablePtr> parameters,
                                      SortPtr sort,
                                      TermPtr body)
                    : body(std::move(body))
                    , signature(std::make_shared<FunctionDeclaration>(std::move(name),
                                                                      std::move(parameters),
                                                                      std::move(sort))) {}


            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //SLCOMP_PARSER_SEP_FUN_H
