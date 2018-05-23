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

    for (int i = 1; i < argc; i++) {
        string argstr = string(argv[i]);
        smatch sm;

        if (strcmp(argv[i], "--no-core") == 0) {
            settings->setCoreTheoryEnabled(false);
        } else {
            files.push_back(string(argv[i]));
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
    }

    return 0;
}