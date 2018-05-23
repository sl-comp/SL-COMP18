#include "smtlib/parser/smtlib_parser.h"
#include "transl/sep_translator.h"
#include "sep_visitor_stack.h"

#include "ast/ast_logic.h"
#include "ast/ast_theory.h"
#include "sep/sep_attribute.h"
#include "sep/sep_command.h"
#include "sep/sep_logic.h"
#include "sep/sep_s_expr.h"
#include "sep/sep_script.h"
#include "sep/sep_symbol_decl.h"
#include "sep/sep_term.h"
#include "sep/sep_theory.h"

using namespace std;
using namespace smtlib::sep;

/* ================================ VisitorWithStack0 ================================= */
void VisitorWithStack0::loadTheory(const string& theory) {
    string path = config->get(Configuration::Property::LOC_THEORIES) + theory
                  + config->get(Configuration::Property::FILE_EXT_THEORY);
    FILE *f = fopen(path.c_str(), "r");
    if (f) {
        fclose(f);
        ParserPtr parser = make_shared<Parser>();
        TranslatorPtr translator = make_shared<Translator>();

        smtlib::ast::NodePtr ast = parser->parse(path);
        if (auto theoryAst = dynamic_pointer_cast<smtlib::ast::Theory>(ast)) {
            TheoryPtr theorySmt = translator->translate(theoryAst);
            visit0(theorySmt);
        }
    }
}

void VisitorWithStack0::loadLogic(const string& logic) {
    string path = config->get(Configuration::Property::LOC_LOGICS) + logic
                  + config->get(Configuration::Property::FILE_EXT_LOGIC);
    FILE *f = fopen(path.c_str(), "r");
    if (f) {
        fclose(f);

        ParserPtr parser = make_shared<Parser>();
        TranslatorPtr translator = make_shared<Translator>();

        smtlib::ast::NodePtr ast = parser->parse(path);
        if (auto logicAst = dynamic_pointer_cast<smtlib::ast::Logic>(ast)) {
            LogicPtr logicSmt = translator->translate(logicAst);
            visit0(logicSmt);
        }
    }
}

SortEntryPtr VisitorWithStack0::buildEntry(const SortSymbolDeclarationPtr& node) {
    return make_shared<SortEntry>(node->identifier->toString(),
                                  node->arity, node->attributes, node);
}

SortEntryPtr VisitorWithStack0::buildEntry(const DeclareSortCommandPtr& node) {
    return make_shared<SortEntry>(node->name, node->arity, node);
}

SortEntryPtr VisitorWithStack0::buildEntry(const DefineSortCommandPtr& node) {
    return make_shared<SortEntry>(node->name, node->parameters.size(), node->parameters,
                                  stack->expand(node->sort), node);
}

FunEntryPtr VisitorWithStack0::buildEntry(const SpecConstFunDeclarationPtr& node) {
    std::vector<SortPtr> sig;
    sig.push_back(stack->expand(node->sort));
    return make_shared<FunEntry>(node->constant->toString(), sig, node->attributes, node);
}

FunEntryPtr VisitorWithStack0::buildEntry(const MetaSpecConstFunDeclarationPtr& node) {
    std::vector<SortPtr> sig;
    sig.push_back(stack->expand(node->sort));
    return make_shared<FunEntry>(node->constant->toString(), sig, node->attributes, node);
}

FunEntryPtr VisitorWithStack0::buildEntry(const SimpleFunDeclarationPtr& node) {
    std::vector<SortPtr> newsig;

    for (const auto& sort : node->signature) {
        newsig.push_back(stack->expand(sort));
    }

    FunEntryPtr funEntry = make_shared<FunEntry>(node->identifier->toString(),
                                                 newsig, node->attributes, node);

    for (const auto& attr : node->attributes) {
        if (attr->toString() == KW_RIGHT_ASSOC) {
            funEntry->assocR = true;
        }

        if (attr->toString() == KW_LEFT_ASSOC) {
            funEntry->assocL = true;
        }

        if (attr->toString() == KW_CHAINABLE) {
            funEntry->chainable = true;
        }

        if (attr->toString() == KW_PAIRWISE) {
            funEntry->pairwise = true;
        }
    }

    return funEntry;
}

FunEntryPtr VisitorWithStack0::buildEntry(const ParametricFunDeclarationPtr& node) {
    std::vector<SortPtr> newsig;
    for (const auto& sort : node->signature) {
        newsig.push_back(stack->expand(sort));
    }

    FunEntryPtr funEntry = make_shared<FunEntry>(node->identifier->toString(), newsig,
                                                 node->parameters, node->attributes, node);

    for (const auto& attr : node->attributes) {
        if (attr->toString() == KW_RIGHT_ASSOC) {
            funEntry->assocR = true;
        }

        if (attr->toString() == KW_LEFT_ASSOC) {
            funEntry->assocL = true;
        }

        if (attr->toString() == KW_CHAINABLE) {
            funEntry->chainable = true;
        }

        if (attr->toString() == KW_PAIRWISE) {
            funEntry->pairwise = true;
        }
    }

    return funEntry;
}

FunEntryPtr VisitorWithStack0::buildEntry(const DeclareConstCommandPtr& node) {
    std::vector<SortPtr> sig;
    sig.push_back(stack->expand(node->sort));

    return make_shared<FunEntry>(node->name, sig, node);
}

FunEntryPtr VisitorWithStack0::buildEntry(const DeclareFunCommandPtr& node) {
    std::vector<SortPtr> newsig;

    for (const auto& sort : node->parameters) {
        SortPtr itsort = stack->expand(sort);
        newsig.push_back(itsort);
    }
    SortPtr retsort = stack->expand(node->sort);
    newsig.push_back(retsort);

    return make_shared<FunEntry>(node->name, newsig, node);
}

FunEntryPtr VisitorWithStack0::buildEntry(const DefineFunCommandPtr& node) {
    std::vector<SortPtr> newsig;
    for (const auto& param : node->definition->signature->parameters) {
        newsig.push_back(stack->expand(param->sort));
    }
    newsig.push_back(stack->expand(node->definition->signature->sort));

    return make_shared<FunEntry>(node->definition->signature->name,
                                 newsig, node->definition->body, node);
}

FunEntryPtr VisitorWithStack0::buildEntry(const DefineFunRecCommandPtr& node) {
    std::vector<SortPtr> newsig;
    for (const auto& param : node->definition->signature->parameters) {
        newsig.push_back(stack->expand(param->sort));
    }
    newsig.push_back(stack->expand(node->definition->signature->sort));

    return make_shared<FunEntry>(node->definition->signature->name,
                                 newsig, node->definition->body, node);
}

std::vector<FunEntryPtr> VisitorWithStack0::buildEntry(const DefineFunsRecCommandPtr& node) {
    std::vector<FunEntryPtr> infos;
    for (size_t i = 0, sz = node->declarations.size(); i < sz; i++) {
        std::vector<SortPtr> newsig;
        for (const auto& param : node->declarations[i]->parameters) {
            newsig.push_back(stack->expand(param->sort));
        }
        newsig.push_back(stack->expand(node->declarations[i]->sort));

        infos.push_back(make_shared<FunEntry>(node->declarations[i]->name,
                                              newsig, node->bodies[i], node));
    }

    return infos;
}

DatatypeEntryPtr VisitorWithStack0::buildEntry(const DeclareDatatypeCommandPtr& node) {
    string typeName = node->name;
    DatatypeEntryPtr entry = make_shared<DatatypeEntry>(typeName, node);

    ParametricDatatypeDeclarationPtr pdecl =
            dynamic_pointer_cast<ParametricDatatypeDeclaration>(node->declaration);

    if (pdecl) {
        // Add datatype (parametric) sort info
        entry->sort = make_shared<SortEntry>(typeName, pdecl->parameters.size(), node);

        // Build a sort representing the datatype
        // (to be used in the signatures of the constructors and selectors)
        SortPtr typeSort = make_shared<Sort>(node->name);

        for (const auto& param : pdecl->parameters) {
            typeSort->arguments.push_back(make_shared<Sort>(param));
        }

        typeSort = stack->expand(typeSort);

        for (const auto& cons : pdecl->constructors) {
            // Start building function info for current constructor
            string consName = cons->name;
            std::vector<SortPtr> consSig;

            for (const auto& sel : cons->selectors) {
                // Add sort of current selector to current constructor signature
                consSig.push_back(stack->expand(sel->sort));

                // Build function info for current selector
                string selName = sel->name;
                std::vector<SortPtr> selSig;
                selSig.push_back(typeSort);
                selSig.push_back(stack->expand(sel->sort));

                // Add selector function info
                entry->funs.push_back(make_shared<FunEntry>(selName, selSig, pdecl->parameters, node));
            }

            // Add constructor function info
            consSig.push_back(typeSort);
            entry->funs.push_back(make_shared<FunEntry>(consName, consSig, pdecl->parameters, node));
        }

    } else {
        // Add datatype (non-parametric) sort info
        entry->sort = make_shared<SortEntry>(typeName, 0, node);

        // Build a sort representing the datatype (to be used in the signatures of the constructors and selectors)
        SortPtr typeSort = make_shared<Sort>(node->name);
        typeSort = stack->expand(typeSort);

        SimpleDatatypeDeclarationPtr sdecl =
                dynamic_pointer_cast<SimpleDatatypeDeclaration>(node->declaration);

        for (const auto& cons : sdecl->constructors) {
            // Start building function info for current constructor
            string consName = cons->name;
            std::vector<SortPtr> consSig;
            std::vector<SelectorDeclarationPtr> selectors = cons->selectors;

            for (const auto& sel : cons->selectors) {
                // Add sort of current selector to current constructor signature
                consSig.push_back(stack->expand(sel->sort));

                // Build function info for current selector
                string selName = sel->name;
                std::vector<SortPtr> selSig;
                selSig.push_back(typeSort);
                selSig.push_back(stack->expand(sel->sort));

                // Add selector function info
                entry->funs.push_back(make_shared<FunEntry>(selName, selSig, node));
            }

            // Add constructor function info
            consSig.push_back(typeSort);
            entry->funs.push_back(make_shared<FunEntry>(consName, consSig, node));
        }
    }

    return entry;
}

std::vector<DatatypeEntryPtr> VisitorWithStack0::buildEntry(const DeclareDatatypesCommandPtr& node) {
    std::vector<DatatypeEntryPtr> entries;
    std::vector<SortDeclarationPtr> datatypeSorts = node->sorts;

    for (const auto& sort : datatypeSorts) {
        // Create datatype entry
        DatatypeEntryPtr entry = make_shared<DatatypeEntry>(sort->name, node);

        // Add datatype sort info
        entry->sort = make_shared<SortEntry>(sort->name, (size_t) sort->arity, node);

        // Add new datatype entry to list
        entries.push_back(entry);
    }

    for (size_t i = 0, sz = datatypeSorts.size(); i < sz; i++) {
        ParametricDatatypeDeclarationPtr pdecl =
                dynamic_pointer_cast<ParametricDatatypeDeclaration>(node->declarations[i]);
        if (pdecl) {
            // Build a sort representing the datatype
            // (to be used in the signatures of the constructors and selectors)
            SortPtr typeSort = make_shared<Sort>(node->sorts[i]->name);
            typeSort = stack->expand(typeSort);

            for (const auto& param : pdecl->parameters) {
                typeSort->arguments.push_back(make_shared<Sort>(param));
            }

            for (const auto& cons : pdecl->constructors) {
                // Start building function info for current constructor
                string consName = cons->name;
                std::vector<SortPtr> consSig;

                for (const auto& sel : cons->selectors) {
                    // Add sort of current selector to current constructor signature
                    consSig.push_back(stack->expand(sel->sort));

                    // Build function info for current selector
                    string selName = sel->name;
                    std::vector<SortPtr> selSig;
                    selSig.push_back(typeSort);
                    selSig.push_back(stack->expand(sel->sort));

                    // Add selector function info
                    entries[i]->funs.push_back(make_shared<FunEntry>(selName, selSig, pdecl->parameters, node));
                }

                // Add constructor function info
                consSig.push_back(typeSort);
                entries[i]->funs.push_back(make_shared<FunEntry>(consName, consSig, pdecl->parameters, node));
            }
        } else {
            // Build a sort representing the datatype
            // (to be used in the signatures of the constructors and selectors)
            SortPtr typeSort =
                    make_shared<Sort>(node->sorts[i]->name);
            typeSort = stack->expand(typeSort);

            SimpleDatatypeDeclarationPtr sdecl =
                    dynamic_pointer_cast<SimpleDatatypeDeclaration>(node->declarations[i]);

            for (const auto& cons : sdecl->constructors) {
                // Start building function info for current constructor
                string consName = cons->name;
                std::vector<SortPtr> consSig;

                for (const auto& sel : cons->selectors) {
                    // Add sort of current selector to current constructor signature
                    consSig.push_back(stack->expand(sel->sort));

                    // Build function info for current selector
                    string selName = sel->name;
                    std::vector<SortPtr> selSig;
                    selSig.push_back(typeSort);
                    selSig.push_back(stack->expand(sel->sort));

                    // Add selector function info
                    entries[i]->funs.push_back(make_shared<FunEntry>(selName, selSig, node));
                }

                // Add constructor function info
                consSig.push_back(typeSort);
                entries[i]->funs.push_back(make_shared<FunEntry>(consName, consSig, node));
            }
        }
    }

    return entries;
}


void VisitorWithStack0::visit(const SimpleAttributePtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const SExpressionAttributePtr& node) {
    visitWithStack(node);
    visit0(node->value);
}

void VisitorWithStack0::visit(const SymbolAttributePtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const BooleanAttributePtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const NumeralAttributePtr& node) {
    visitWithStack(node);
    visit0(node->value);
}

void VisitorWithStack0::visit(const DecimalAttributePtr& node) {
    visitWithStack(node);
    visit0(node->value);
}

void VisitorWithStack0::visit(const StringAttributePtr& node) {
    visitWithStack(node);
    visit0(node->value);
}

void VisitorWithStack0::visit(const TheoriesAttributePtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const SortsAttributePtr& node) {
    visitWithStack(node);

    visit0(node->declarations);
}

void VisitorWithStack0::visit(const FunsAttributePtr& node) {
    visitWithStack(node);

    visit0(node->declarations);
}

void VisitorWithStack0::visit(const SymbolPtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const KeywordPtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const MetaSpecConstantPtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const BooleanValuePtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const PropLiteralPtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const AssertCommandPtr& node) {
    visitWithStack(node);
    visit0(node->term);
}

void VisitorWithStack0::visit(const CheckSatCommandPtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const CheckUnsatCommandPtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const CheckSatAssumCommandPtr& node) {
    visitWithStack(node);
    visit0(node->assumptions);
}

void VisitorWithStack0::visit(const DeclareConstCommandPtr& node) {
    FunEntryPtr entry = buildEntry(node);
    stack->tryAdd(entry);

    visitWithStack(node);

    visit0(node->sort);
}

void VisitorWithStack0::visit(const DeclareDatatypeCommandPtr& node) {
    DatatypeEntryPtr entry = buildEntry(node);
    stack->tryAdd(entry->sort);

    for (const auto& fun : entry->funs) {
        stack->tryAdd(fun);
    }

    visitWithStack(node);

    visit0(node->declaration);
}

void VisitorWithStack0::visit(const DeclareDatatypesCommandPtr& node) {
    std::vector<DatatypeEntryPtr> entries = buildEntry(node);
    for (const auto& entry : entries) {
        stack->tryAdd(entry->sort);

        for (const auto& fun : entry->funs) {
            stack->tryAdd(fun);
        }
    }

    visitWithStack(node);

    visit0(node->sorts);
    visit0(node->declarations);
}

void VisitorWithStack0::visit(const DeclareFunCommandPtr& node) {
    FunEntryPtr entry = buildEntry(node);
    stack->tryAdd(entry);

    visitWithStack(node);

    visit0(node->parameters);
    visit0(node->sort);
}

void VisitorWithStack0::visit(const DeclareSortCommandPtr& node) {
    SortEntryPtr entry = buildEntry(node);
    stack->tryAdd(entry);

    visitWithStack(node);
}

void VisitorWithStack0::visit(const DeclareHeapCommandPtr& node) {
    for(const auto& pair : node->locDataPairs) {
        stack->tryAdd(pair);
    }

    visitWithStack(node);

    visit0(node->locDataPairs);
}

void VisitorWithStack0::visit(const DefineFunCommandPtr& node) {
    FunEntryPtr entry = buildEntry(node);
    stack->tryAdd(entry);

    visitWithStack(node);

    // New stack level for parameters
    stack->push();

    for(const auto& param : node->definition->signature->parameters) {
        stack->tryAdd(make_shared<VarEntry>(param->name, std::move(stack->expand(param->sort)), node));
    }

    visit0(node->definition);

    // Pop the previously added level
    stack->pop();
}

void VisitorWithStack0::visit(const DefineFunRecCommandPtr& node) {
    FunEntryPtr entry = buildEntry(node);
    stack->tryAdd(entry);

    visitWithStack(node);

    // New stack level for parameters
    stack->push();

    for(const auto& param : node->definition->signature->parameters) {
        stack->tryAdd(make_shared<VarEntry>(param->name, std::move(stack->expand(param->sort)), node));
    }

    visit0(node->definition);

    // Pop the previously added level
    stack->pop();
}

void VisitorWithStack0::visit(const DefineFunsRecCommandPtr& node) {
    std::vector<FunEntryPtr> entries = buildEntry(node);
    for (const auto& entry : entries) {
        stack->tryAdd(entry);
    }

    visitWithStack(node);

    for(size_t i = 0, sz = node->declarations.size(); i < sz; i++) {
        // New stack level for parameters
        stack->push();

        for(const auto& param : node->declarations[i]->parameters) {
            stack->tryAdd(make_shared<VarEntry>(param->name, std::move(stack->expand(param->sort)), node));
        }

        visit0(node->declarations[i]);
        visit0(node->bodies[i]);

        // Pop the previously added level
        stack->pop();
    }
}

void VisitorWithStack0::visit(const DefineSortCommandPtr& node) {
    SortEntryPtr entry = buildEntry(node);
    stack->tryAdd(entry);

    visitWithStack(node);

    visit0(node->sort);
}

void VisitorWithStack0::visit(const EchoCommandPtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const ExitCommandPtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const GetAssertsCommandPtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const GetAssignsCommandPtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const GetInfoCommandPtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const GetModelCommandPtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const GetOptionCommandPtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const GetProofCommandPtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const GetUnsatAssumsCommandPtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const GetUnsatCoreCommandPtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const GetValueCommandPtr& node) {
    visitWithStack(node);
    visit0(node->terms);
}

void VisitorWithStack0::visit(const PopCommandPtr& node) {
    stack->pop((size_t) node->levelCount);

    visitWithStack(node);
}

void VisitorWithStack0::visit(const PushCommandPtr& node) {
    stack->push((size_t) node->levelCount);

    visitWithStack(node);
}

void VisitorWithStack0::visit(const ResetCommandPtr& node) {
    stack->reset();
    currentLogic = "";
    currentTheories.clear();

    visitWithStack(node);
}

void VisitorWithStack0::visit(const ResetAssertsCommandPtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const SetInfoCommandPtr& node) {
    visitWithStack(node);
    visit0(node->info);
}

void VisitorWithStack0::visit(const SetLogicCommandPtr& node) {
    if (currentLogic.empty()) {
        currentLogic = node->logic;
        loadLogic(node->logic);
    }

    visitWithStack(node);
}

void VisitorWithStack0::visit(const SetOptionCommandPtr& node) {
    visitWithStack(node);
    visit0(node->option);
}

void VisitorWithStack0::visit(const SortDeclarationPtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const SelectorDeclarationPtr& node) {
    visitWithStack(node);
    visit0(node->sort);
}

void VisitorWithStack0::visit(const ConstructorDeclarationPtr& node) {
    visitWithStack(node);
    visit0(node->selectors);
}

void VisitorWithStack0::visit(const SimpleDatatypeDeclarationPtr& node) {
    visitWithStack(node);
    visit0(node->constructors);
}

void VisitorWithStack0::visit(const ParametricDatatypeDeclarationPtr& node) {
    visitWithStack(node);
    visit0(node->constructors);
}

void VisitorWithStack0::visit(const FunctionDeclarationPtr& node) {
    visitWithStack(node);

    visit0(node->parameters);
    visit0(node->sort);
}

void VisitorWithStack0::visit(const FunctionDefinitionPtr& node) {
    visitWithStack(node);

    visit0(node->signature);
    visit0(node->body);
}

void VisitorWithStack0::visit(const SimpleIdentifierPtr& node) {
    visitWithStack(node);
    visit0(node->indices);
}

void VisitorWithStack0::visit(const QualifiedIdentifierPtr& node) {
    visitWithStack(node);

    visit0(node->identifier);
    visit0(node->sort);
}

void VisitorWithStack0::visit(const NumeralLiteralPtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const DecimalLiteralPtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const StringLiteralPtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const LogicPtr& node) {
    for (const auto& attr : node->attributes) {
        if (auto theoriesAttr = dynamic_pointer_cast<TheoriesAttribute>(attr)) {
            for (const auto& theory : theoriesAttr->theories) {
                auto found = find(currentTheories.begin(), currentTheories.end(), theory);

                if (found == currentTheories.end()) {
                    currentTheories.push_back(theory);
                    loadTheory(theory);
                }
            }
        }
    }

    visitWithStack(node);

    visit0(node->attributes);
}

void VisitorWithStack0::visit(const TheoryPtr& node) {
    visitWithStack(node);

    for (const auto& attr : node->attributes) {
        if (auto sortsAttr = dynamic_pointer_cast<SortsAttribute>(attr)) {
            visit0(sortsAttr);
        }

        if (auto funsAttr = dynamic_pointer_cast<FunsAttribute>(attr)) {
            visit0(funsAttr);
        }
    }
}

void VisitorWithStack0::visit(const ScriptPtr& node) {
    visitWithStack(node);

    visit0(node->commands);
}

void VisitorWithStack0::visit(const QualifiedConstructorPtr& node) {
    visitWithStack(node);
    visit0(node->sort);
}

void VisitorWithStack0::visit(const QualifiedPatternPtr& node) {
    visitWithStack(node);
    visit0(node->constructor);
}

void VisitorWithStack0::visit(const MatchCasePtr& node) {
    visitWithStack(node);

    visit0(node->pattern);
    visit0(node->term);
}

void VisitorWithStack0::visit(const CompSExpressionPtr& node) {
    visitWithStack(node);

    visit0(node->expressions);
}

void VisitorWithStack0::visit(const SortPtr& node) {
    visitWithStack(node);

    visit0(node->arguments);
}

void VisitorWithStack0::visit(const SortSymbolDeclarationPtr& node) {
    SortEntryPtr entry = buildEntry(node);
    stack->tryAdd(entry);

    visitWithStack(node);

    visit0(node->identifier);
    visit0(node->attributes);
}

void VisitorWithStack0::visit(const SpecConstFunDeclarationPtr& node) {
    FunEntryPtr entry = buildEntry(node);
    stack->tryAdd(entry);

    visitWithStack(node);

    visit0(node->constant);
    visit0(node->sort);
    visit0(node->attributes);
}

void VisitorWithStack0::visit(const MetaSpecConstFunDeclarationPtr& node) {
    FunEntryPtr entry = buildEntry(node);
    stack->tryAdd(entry);

    visitWithStack(node);

    visit0(node->constant);
    visit0(node->sort);
    visit0(node->attributes);
}

void VisitorWithStack0::visit(const SimpleFunDeclarationPtr& node) {
    FunEntryPtr entry = buildEntry(node);
    stack->tryAdd(entry);

    visitWithStack(node);

    visit0(node->identifier);
    visit0(node->signature);
    visit0(node->attributes);
}

void VisitorWithStack0::visit(const ParametricFunDeclarationPtr& node) {
    FunEntryPtr entry = buildEntry(node);
    stack->tryAdd(entry);

    visitWithStack(node);

    visit0(node->identifier);
    visit0(node->signature);
    visit0(node->attributes);
}

void VisitorWithStack0::visit(const QualifiedTermPtr& node) {
    visitWithStack(node);

    visit0(node->identifier);
    visit0(node->terms);
}

void VisitorWithStack0::visit(const LetTermPtr& node) {
    visitWithStack(node);

    // New stack level for bindings
    stack->push();

    for (const auto& binding : node->bindings) {
        TermSorterContextPtr ctx = make_shared<TermSorterContext>(stack);
        TermSorterPtr sorter = make_shared<TermSorter>(ctx);

        SortPtr result = sorter->run(binding->term);
        stack->tryAdd(make_shared<VarEntry>(binding->name, result, node));
    }

    visit0(node->bindings);
    visit0(node->term);

    // Pop the previously added level
    stack->pop();
}

void VisitorWithStack0::visit(const ForallTermPtr& node) {
    visitWithStack(node);

    // New stack level for bindings
    stack->push();

    for (const auto& bind : node->bindings) {
        stack->tryAdd(make_shared<VarEntry>(bind->name, std::move(stack->expand(bind->sort)), node));
    }

    visit0(node->bindings);
    visit0(node->term);

    // Pop the previously added level
    stack->pop();
}

void VisitorWithStack0::visit(const ExistsTermPtr& node) {
    visitWithStack(node);

    // New stack level for bindings
    stack->push();

    for (const auto& bind : node->bindings) {
        stack->tryAdd(make_shared<VarEntry>(bind->name, std::move(stack->expand(bind->sort)), node));
    }

    visit0(node->bindings);
    visit0(node->term);

    // Pop the previously added level
    stack->pop();
}

void VisitorWithStack0::visit(const MatchTermPtr& node) {
    visitWithStack(node);

    visit0(node->term);
    visit0(node->cases);
}

void VisitorWithStack0::visit(const AnnotatedTermPtr& node) {
    visitWithStack(node);

    visit0(node->term);
    visit0(node->attributes);
}

void VisitorWithStack0::visit(const TrueTermPtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const FalseTermPtr& node) {
    visitWithStack(node);
}

void VisitorWithStack0::visit(const NotTermPtr& node) {
    visitWithStack(node);

    visit0(node->term);
}

void VisitorWithStack0::visit(const ImpliesTermPtr& node) {
    visitWithStack(node);

    visit0(node->terms);
}

void VisitorWithStack0::visit(const AndTermPtr& node) {
    visitWithStack(node);

    visit0(node->terms);
}

void VisitorWithStack0::visit(const OrTermPtr& node) {
    visitWithStack(node);

    visit0(node->terms);
}

void VisitorWithStack0::visit(const XorTermPtr& node) {
    visitWithStack(node);

    visit0(node->terms);
}

void VisitorWithStack0::visit(const EqualsTermPtr& node) {
    visitWithStack(node);

    visit0(node->terms);
}

void VisitorWithStack0::visit(const DistinctTermPtr& node) {
    visitWithStack(node);

    visit0(node->terms);
}

void VisitorWithStack0::visit(const IteTermPtr& node) {
    visitWithStack(node);

    visit0(node->testTerm);
    visit0(node->thenTerm);
    visit0(node->elseTerm);
}

void VisitorWithStack0::visit(const EmpTermPtr& node) {
    visitWithStack(node);

    if(node->dataSort)
        visit0(node->dataSort);

    if(node->locSort)
        visit0(node->locSort);
}

void VisitorWithStack0::visit(const SepTermPtr& node) {
    visitWithStack(node);

    visit0(node->terms);
}

void VisitorWithStack0::visit(const WandTermPtr& node) {
    visitWithStack(node);

    visit0(node->terms);
}

void VisitorWithStack0::visit(const PtoTermPtr& node) {
    visitWithStack(node);

    visit0(node->leftTerm);
    visit0(node->rightTerm);
}

void VisitorWithStack0::visit(const NilTermPtr& node) {
    visitWithStack(node);

    visit0(node->sort);
}

void VisitorWithStack0::visit(const SortedVariablePtr& node) {
    visitWithStack(node);

    visit0(node->sort);
}

void VisitorWithStack0::visit(const VariableBindingPtr& node) {
    visitWithStack(node);

    visit0(node->term);
}

/* ============================== DummyVisitorWithStack0 ============================== */

void DummyVisitorWithStack0::visitWithStack(const SimpleAttributePtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const SExpressionAttributePtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const SymbolAttributePtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const BooleanAttributePtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const NumeralAttributePtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const DecimalAttributePtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const StringAttributePtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const TheoriesAttributePtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const SortsAttributePtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const FunsAttributePtr& node) {}

void DummyVisitorWithStack0::visitWithStack(const SymbolPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const KeywordPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const MetaSpecConstantPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const BooleanValuePtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const PropLiteralPtr& node) {}

void DummyVisitorWithStack0::visitWithStack(const AssertCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const CheckSatCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const CheckUnsatCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const CheckSatAssumCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const DeclareConstCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const DeclareDatatypeCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const DeclareDatatypesCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const DeclareFunCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const DeclareSortCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const DeclareHeapCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const DefineFunCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const DefineFunRecCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const DefineFunsRecCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const DefineSortCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const EchoCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const ExitCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const GetAssertsCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const GetAssignsCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const GetInfoCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const GetModelCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const GetOptionCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const GetProofCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const GetUnsatAssumsCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const GetUnsatCoreCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const GetValueCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const PopCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const PushCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const ResetCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const ResetAssertsCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const SetInfoCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const SetLogicCommandPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const SetOptionCommandPtr& node) {}

void DummyVisitorWithStack0::visitWithStack(const SortDeclarationPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const SelectorDeclarationPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const ConstructorDeclarationPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const SimpleDatatypeDeclarationPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const ParametricDatatypeDeclarationPtr& node) {}

void DummyVisitorWithStack0::visitWithStack(const FunctionDeclarationPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const FunctionDefinitionPtr& node) {}

void DummyVisitorWithStack0::visitWithStack(const SimpleIdentifierPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const QualifiedIdentifierPtr& node) {}

void DummyVisitorWithStack0::visitWithStack(const NumeralLiteralPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const DecimalLiteralPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const StringLiteralPtr& node) {}

void DummyVisitorWithStack0::visitWithStack(const LogicPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const TheoryPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const ScriptPtr& node) {}

void DummyVisitorWithStack0::visitWithStack(const QualifiedConstructorPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const QualifiedPatternPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const MatchCasePtr& node) {}

void DummyVisitorWithStack0::visitWithStack(const CompSExpressionPtr& node) {}

void DummyVisitorWithStack0::visitWithStack(const SortPtr& node) {}

void DummyVisitorWithStack0::visitWithStack(const SortSymbolDeclarationPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const SpecConstFunDeclarationPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const MetaSpecConstFunDeclarationPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const SimpleFunDeclarationPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const ParametricFunDeclarationPtr& node) {}

void DummyVisitorWithStack0::visitWithStack(const QualifiedTermPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const LetTermPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const ForallTermPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const ExistsTermPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const MatchTermPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const AnnotatedTermPtr& node) {}

void DummyVisitorWithStack0::visitWithStack(const TrueTermPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const FalseTermPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const NotTermPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const ImpliesTermPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const AndTermPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const OrTermPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const XorTermPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const EqualsTermPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const DistinctTermPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const IteTermPtr& node) {}

void DummyVisitorWithStack0::visitWithStack(const EmpTermPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const SepTermPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const WandTermPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const PtoTermPtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const NilTermPtr& node) {}

void DummyVisitorWithStack0::visitWithStack(const SortedVariablePtr& node) {}
void DummyVisitorWithStack0::visitWithStack(const VariableBindingPtr& node) {}
