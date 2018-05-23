code:
	bison -d smtlib-bison-parser.y -Wconflicts-sr -Wconflicts-rr
	mv smtlib-bison-parser.tab.h smtlib-bison-parser.y.h
	mv smtlib-bison-parser.tab.c smtlib-bison-parser.y.c
	flex smtlib-flex-lexer.l
	mv lex.smt_yy.c smtlib-flex-lexer.l.c
clean:
	rm -f smtlib-bison-parser.y.h
	rm -f smtlib-bison-parser.y.c
	rm -f smtlib-flex-lexer.l.c
	rm -f *.o
	rm -f parser