#include "configuration.h"

#include <cstring>
#include <fstream>
#include <iostream>
#include <sstream>

using namespace std;

const std::string Configuration::TRIM_CHARS = " \t\n\r=";

std::map<std::string, Configuration::Property> Configuration::PROP_NAMES;

void Configuration::loadFile(const std::string& path) {
    ifstream input(path);
    while(!input.eof()) {
        char buffer[1024];

        input.get(buffer, 1024, '=');
        string prop(buffer);
        trim(prop);

        input.get(buffer, 1024, '\n');
        string value(buffer);
        trim(value);

        std::map<std::string, Property>::iterator it;
        it = PROP_NAMES.find(prop);

        if(it != PROP_NAMES.end()) {
            properties[it->second] = value;
        }
    }
}

Configuration::Configuration() {
    populatePropNames();
    loadDefaults();
}

Configuration::Configuration(const string& path) {
    populatePropNames();
    loadDefaults();
    loadFile(path);
}

void Configuration::populatePropNames() {
    PROP_NAMES["LOC_LOGICS"] = Property::LOC_LOGICS;
    PROP_NAMES["LOC_THEORIES"] = Property::LOC_THEORIES;
    PROP_NAMES["FILE_EXT_LOGIC"] = Property::FILE_EXT_LOGIC;
    PROP_NAMES["FILE_EXT_THEORY"] = Property::FILE_EXT_THEORY;
}

void Configuration::loadDefaults() {
    properties[Property::LOC_LOGICS] = "input/Logics/";
    properties[Property::LOC_THEORIES] = "input/Theories/";
    properties[Property::FILE_EXT_LOGIC] = ".smt2";
    properties[Property::FILE_EXT_THEORY] = ".smt2";
}

string Configuration::get(Configuration::Property key) {
    if(properties.find(key) != properties.end())
        return properties[key];
    else
        return "";
}
