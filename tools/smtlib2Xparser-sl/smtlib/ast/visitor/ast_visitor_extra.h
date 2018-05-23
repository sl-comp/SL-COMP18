/**
 * \file ast_visitor_extra.h
 * \brief Additional visitor types.
 */

#ifndef SLCOMP_PARSER_AST_VISITOR_EXTRA_H
#define SLCOMP_PARSER_AST_VISITOR_EXTRA_H

#include "ast_visitor.h"

#include "ast/ast_abstract.h"
#include "util/logger.h"

namespace smtlib {
    namespace ast {
        /* ===================================== Visitor1 ===================================== */
        /**
         * An extended visitor for the smtlib::ast hierarchy,
         * where each visit returns a result
         */
        template<class RetT>
        class Visitor1 : public virtual Visitor0 {
        protected:
            RetT ret;

            RetT wrappedVisit(const NodePtr& node) {
                RetT oldRet = ret;
                visit0(node);
                RetT newRet = ret;
                ret = oldRet;
                return newRet;
            }

            std::vector<RetT> wrappedVisit(std::vector<NodePtr>& nodes) {
                std::vector<RetT> result(nodes.size());
                for (size_t i = 0, n = nodes.size(); i < n; ++i) {
                    result[i] = wrappedVisit(nodes[i]);
                }
                return result;
            }

        public:
            virtual RetT run(const NodePtr& node) {
                return wrappedVisit(node);
            }
        };

        /* ===================================== Visitor2 ===================================== */
        /**
         * An extended visitor for the smtlib::ast hierarchy,
         * where each visit returns a result and takes an additional argument
         */
        template<class RetT, class ArgT>
        class Visitor2 : public virtual Visitor0 {
        protected:
            ArgT arg;
            RetT ret;

            RetT wrappedVisit(ArgT arg, const NodePtr& node) {
                RetT oldRet = ret;
                ArgT oldArg = this->arg;
                this->arg = arg;
                visit0(node);
                RetT newRet = ret;
                ret = oldRet;
                this->arg = oldArg;
                return newRet;
            }

            std::vector<RetT> wrappedVisit(ArgT arg, std::vector<NodePtr>& nodes) {
                std::vector<RetT> result(nodes.size());
                for (size_t i = 0, n = nodes.size(); i < n; ++i) {
                    result[i] = wrappedVisit(arg, nodes[i]);
                }
                return result;
            }

        public:
            virtual RetT run(ArgT arg, const NodePtr& node) {
                return wrappedVisit(arg, node);
            }
        };

        /* ================================== DummyVisitor1 =================================== */
        /** A dummy (empty) implementation of Visitor1 */
        template<class RetT>
        class DummyVisitor1 : public Visitor1<RetT>,
                              public DummyVisitor0 {
        };

        /* ================================== DummyVisitor2 =================================== */
        /** A dummy (empty) implementation of Visitor2 */
        template<class RetT, class ArgT>
        class DummyVisitor2 : public Visitor2<RetT, ArgT>,
                              public DummyVisitor0 {
        };
    }
}

#endif //SLCOMP_PARSER_AST_VISITOR_EXTRA_H
