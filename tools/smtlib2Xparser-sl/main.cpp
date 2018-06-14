/**
 * \file        main.cpp
 * \brief       Entry point for processing SMT-LIB format for Separation Logic
 * \author      Cristina Serban
 * \author      Mihaela Sighireanu
 * \copyright   See 'LICENSE' file.
 */

#include <cstring>
#include <iostream>
#include <memory>
#include <regex>
#include <vector>

#include "exec/execution.h"
#include "util/error_messages.h"
#include "util/logger.h"

using namespace std;
using namespace slcompparser;
using namespace smtlib;

int main(int argc, char **argv) {
    ExecutionSettingsPtr settings = make_shared<ExecutionSettings>();

    vector<string> files;

    for (int i = 1; i < argc;) {
        // string argstr = string(argv[i]);
        // smatch sm;

        if (strcmp(argv[i], "--config") == 0) {
	    i++;
	    if (i < argc) {
		smtlib::ast::SortCheckContextPtr cf = 
			make_shared<smtlib::ast::SortednessCheckerContext>();
		cf->getConfiguration()->loadFile(argv[i]);
	        settings->setSortCheckContext(cf);
                i++;
            }
	} else if (strcmp(argv[i], "--no-core") == 0) {
            settings->setCoreTheoryEnabled(false);
            i++;
        } else if (strcmp(argv[i], "--output") == 0) {
            i++;
            if (i < argc) {
                settings->setOutputFormat(argv[i]);
                i++;
            }
        } else if (argv[i][0] == '-') {
	    // unknown option, print the help
	    Logger::error("main()", "Unknown option");
	    Logger::error("main()", "Usage: slcomp-parser [--no-core] [--output <format>] file1.smt2 ... fileN.smt2");
	    i++;
        } else {
            files.push_back(string(argv[i]));
            i++;
        }
    }

    if (files.empty()) {
        Logger::error("main()", "No input files");
        return 1;
    }

    for (const auto& file : files) {
        settings->setInputFromFile(file);
        Execution exec(settings);
        exec.checkHeap();
        exec.translate();
    }

    return 0;
}
