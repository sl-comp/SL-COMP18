/**
 * \file ast_sort.h
 * \brief SMT-LIB+SEPLOG sort.
 */

#ifndef SLCOMP_PARSER_SEP_SORT_H
#define SLCOMP_PARSER_SEP_SORT_H

#include "sep_abstract.h"
#include "sep_basic.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace sep {
        /** An SMT-LIB+SEPLOG sort. */
        class Sort : public Node,
                     public std::enable_shared_from_this<Sort> {
        public:
            std::string name;
            std::vector<SortPtr> arguments;

            /**
             * Constructor for a simple sort
             * \param name      Sort name
             */
            inline explicit Sort(std::string name)
                    : name(std::move(name)) {}

            /**
             * Constructor for a sort with arguments
             * \param name      Sort name
             * \param arguments Sort arguments
             */
            inline Sort(std::string name, std::vector<SortPtr> arguments)
                    : name(std::move(name))
                    , arguments(std::move(arguments)) {}

            /** Checks whether the sort has arguments */
            bool hasArgs();

            void accept(Visitor0* visitor) override;

            std::string toString() override;
        };
    }
}

#endif //SLCOMP_PARSER_SEP_SORT_H
