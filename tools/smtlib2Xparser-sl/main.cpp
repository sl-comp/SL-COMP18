/**
 * \file        main.cpp
 * \brief       Entry point for processing SMT-LIB format for Separation Logic
 * \author      Cristina Serban
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

        if (strcmp(argv[i], "--no-core") == 0) {
            settings->setCoreTheoryEnabled(false);
            i++;
        } else if (strcmp(argv[i], "--output") == 0) {
            i++;
            if (i < argc) {
                settings->setOutputFormat(argv[i]);
                i++;
            }
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