/**
 * \file logger.h
 * \brief Error, warning and message logger.
 */

#ifndef SLCOMP_PARSER_SMT_LOGGER_H
#define SLCOMP_PARSER_SMT_LOGGER_H

/** Error, warning and message logger */
class Logger {
public:
    enum ErrorCode {
        ERR_PARSE = 1
    };

    static void message(const char *msg);

    static void warning(const char *fun, const char *msg);

    static void error(const char *fun, const char *msg);

    static void parsingError(int rowLeft, int colLeft,
                             int rowRight, int colRight,
                             const char *filename, const char *msg);

    static void syntaxError(const char *fun, const char *msg);

    static void syntaxError(const char *fun, const char *file, const char *msg);

    static void sortednessError(const char *fun, const char *file, const char *msg);

    static void sortednessError(const char *fun, const char *msg);

    static void heapError(const char *fun, const char *msg);

    static void predicateError(const char *msg);
};

#endif //SLCOMP_PARSER_SMT_LOGGER_H
