# the name of the output
CO=smtlib-sl

# names of files other than sources the change of which should recompile the
# source
CHANGED_FILES_OTHER =refs.bib commenting.sty

# List of TeX files
TEX_FILES=$(wildcard *.tex)

###############################################################################
#                                 Rules                                       #
###############################################################################

.PHONY: all 

all: $(CO).pdf

$(CO).pdf: $(CHANGED_FILES_OTHER) $(TEX_FILES)
	pdflatex $(CO)
	bibtex $(CO)
	pdflatex $(CO)
	pdflatex $(CO)

clean:
	rm -f *.dvi *.log $(CO).blg $(CO).bbl $(CO).toc *.aux $(CO).out $(CO).lof
	rm -f *~

