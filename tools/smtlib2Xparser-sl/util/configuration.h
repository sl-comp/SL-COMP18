/**
 * \file configuration.h
 * \brief Project configuration.
 */

#ifndef SLCOMP_PARSER_CONFIGURATION_H
#define SLCOMP_PARSER_CONFIGURATION_H

#include <algorithm>
#include <map>
#include <memory>
#include <string>

class Configuration {
public:
    enum Property {
        LOC_LOGICS = 0, LOC_THEORIES, FILE_EXT_LOGIC, FILE_EXT_THEORY
    };

    static std::map<std::string, Property> PROP_NAMES;

private:
    static const std::string TRIM_CHARS;

    static inline bool isTrimChar(char c) {
        bool value = TRIM_CHARS.find(c) != std::string::npos;
        return value;
    }

    // trim from start
    static inline void ltrim(std::string& s) {
        s.erase(s.begin(),
                std::find_if(s.begin(), s.end(),
                             std::not1(std::ptr_fun<char, bool>(Configuration::isTrimChar))));
    }

    // trim from end
    static inline void rtrim(std::string& s) {
        s.erase(std::find_if(s.rbegin(), s.rend(),
                             std::not1(std::ptr_fun<char, bool>(Configuration::isTrimChar))).base(),
                s.end());
    }

    // trim from both ends
    static inline void trim(std::string& s) {
        rtrim(s);
        ltrim(s);
    }

    std::map<Property, std::string> properties;

public:
    Configuration();

    explicit Configuration(const std::string& path);

    void populatePropNames();

    void loadDefaults();

    void loadFile(const std::string& path);

    std::string get(Property key);
};

typedef std::shared_ptr<Configuration> ConfigurationPtr;

#endif //SLCOMP_PARSER_CONFIGURATION_H
