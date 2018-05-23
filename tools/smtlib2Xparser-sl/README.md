# README #

Parser for SMT-LIB v2.6 compatible with input format of SL-COMP'18.

## Requirements ##
 - g++ 4.9.0
 - Flex 2.5.35
 - Bison 2.5
 - CMake 3.5.1
 - Doxygen (optional, for documentation)

## Required files ##
The files containing the definitions of theories and logics, located in `input/Theories` and `input/Logics`, are required for handling the input scripts.

Some sample script inputs can be found in `input/Scripts`.

## Compiling the Flex/Bison parser ##
To compile the files `smtlib/parser/smtlib-bison-parser.y` and `smtlib/parser/smtlib-flex-lexer.l`, go to the `parser` directory and run `make`. If these files are changed, they need to be recompiled.
```
.../smtlib/parser$ make
```
To erase the generated code, run `make clean`.
```
.../smtlib/parser$ make clean
```

## Building and running the project ##
(1) Before building the project, make sure the files `smtlib/parser/smtlib-bison-parser.y.c`, `smtlib/parser/smtlib-bison-parser.y.h` and `smtlib/parser/smtlib-flex-lexer.l.c` have been generated. If any of these files is missing, see section ["Compiling the Flex/Bison parser" above](https://github.com/cristina-serban/inductor/blob/master/README.md#compiling-the-parser).

(2) Run `cmake`. This creates a `Makefile`.

(3) Run `make`. This creates the executable `slcomp-parser` which can parse a list of file inputs.
```
.../slcomp-parser$ make
.../slcomp-parser$ ./slcomp-parser input_file_path1 input_file_path2 input_file_path3 ...
```

(4) As an example, here is how you would run the sample scripts in `input/Scripts`:
```
.../slcomp-parser$ ./slcomp-parser input/Scripts/01.tst.smt2.sl2
```

## Generating documentation ##
```
.../slcomp-parser$ doxygen
```
The documentation in `html` format is generated in the `docs` folder. Open the `docs/index.html` file in a browser.


