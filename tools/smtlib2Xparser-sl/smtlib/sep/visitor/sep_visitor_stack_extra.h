#ifndef SLCOMP_PARSER_SEP_VISITOR_STACK_EXTRA_H
#define SLCOMP_PARSER_SEP_VISITOR_STACK_EXTRA_H

#include "sep_visitor_stack.h"

namespace smtlib {
    namespace sep {
        /* ================================ VisitorWithStack1 ================================= */
        /**
         * An extended visitor with stack for the smtlib::sep hierarchy,
         * where each visit returns a result
         */
        template<class RetT>
        class VisitorWithStack1 : public virtual VisitorWithStack0 {
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

        /* ================================ VisitorWithStack2 ================================= */
        /**
        * An extended visitor with stack for the smtlib::sep hierarchy,
        * where each visit returns a result and takes an additional argument
        */
        template<class RetT, class ArgT>
        class VisitorWithStack2 : public virtual VisitorWithStack0 {
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

            template<class T>
            std::vector<RetT> wrappedVisit(ArgT arg, const std::vector<std::shared_ptr<T>>& nodes) {
                std::vector<RetT> result(nodes.size());
                for (size_t i = 0, n = nodes.size(); i < n; ++i) {
                    result[i] = wrappedVisit(arg, std::dynamic_pointer_cast<T>(nodes[i]));
                }
                return result;
            }

        public:
            virtual RetT run(ArgT arg, const NodePtr& node) {
                return wrappedVisit(arg, node);
            }
        };

        /* ============================== DummyVisitorWithStack1 ============================== */
        template<class RetT>
        class DummyVisitorWithStack1 : public VisitorWithStack1<RetT>,
                                       public DummyVisitorWithStack0 {
        };

        /* ============================== DummyVisitorWithStack2 ============================== */
        template<class RetT, class ArgT>
        class DummyVisitorWithStack2 : public VisitorWithStack2<RetT, ArgT>,
                                       public DummyVisitorWithStack0 {
        };
    }
}

#endif //SLCOMP_PARSER_SEP_VISITOR_STACK_EXTRA_H
