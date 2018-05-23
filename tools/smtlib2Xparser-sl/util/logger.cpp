#include "logger.h"

#include <cstdio>
#include <cstdlib>

void Logger::message(const char* msg) {
    fprintf(stdout, "%s\n", msg);
}

void Logger::warning(const char* fun, const char* msg) {
    fprintf(stderr, "Warning in %s: %s.\n", fun, msg);
}

void Logger::error(const char* fun, const char* msg) {
    fprintf(stderr, "Error in %s: %s.\n", fun, msg);
}

void Logger::syntaxError(const char* fun, const char* msg) {
    fprintf(stderr, "%s: Syntax errors in \n%s", fun, msg);
}

void Logger::syntaxError(const char* fun, const char* file, const char* msg) {
    fprintf(stderr, "%s: Syntax errors in file '%s'\n%s", fun, file, msg);
}

void Logger::sortednessError(const char* fun, const char* file, const char* msg) {
    fprintf(stderr, "%s: Well-sortedness errors when checking file '%s'\n\n%s", fun, file, msg);
}

void Logger::sortednessError(const char* fun, const char* msg) {
    fprintf(stderr, "%s: Well-sortedness errors\n\n%s", fun, msg);
}

void Logger::heapError(const char* fun, const char* msg) {
    fprintf(stderr, "\n%s: Heap check errors:\n%s", fun, msg);
}

void Logger::parsingError(int rowLeft, int colLeft,
                          int rowRight, int colRight,
                          const char* filename, const char* msg) {

    fprintf(stderr, "In %s from %d:%d to %d:%d - %s\n",
            filename, rowLeft, colLeft, rowRight, colRight, msg);
    exit(Logger::ErrorCode::ERR_PARSE);
}

void Logger::predicateError(const char* msg) {
    fprintf(stderr, "Error when loading inductive predicates:\n %s\n", msg);
}
