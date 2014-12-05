
DIRGUARD=@mkdir -p $(@D)

MAIN_NAME=thesis
REFERENCES_NAME=references
LATEXMKOPTS=-pdf -f -quiet
TEXT_PARTS_SRC_ROOT=text
TEXT_PARTS_SRC_GENTEX=$(TEXT_PARTS_SRC_ROOT)

MAINTEX=$(TEXT_PARTS_SRC_ROOT)/$(MAIN_NAME).tex
MAINPDF=./$(MAIN_NAME).pdf
REFERENCES=$(REFERENCES_NAME).bib
TEXT_PARTS=Agda_prelude \
           Background_prelude \
           Background_LambdaCalc \
           Background_MartinLof \
           RelationalAlgebra_prelude \
           Problem \
           Intro \
           Reflection_prelude


CODE_AGDA_ROOT=code/agda
CODE_AGDA_SRC=$(CODE_AGDA_ROOT)/src
CODE_AGDA_EXCERPTS=$(CODE_AGDA_ROOT)/excerpts
CODE_AGDA_STY=./agda.sty
CODE_AGDA_STDLIB=/home/victor/Documents/UU/Thesis/agda-stdlib/src
CODE_AGDA_REL=/home/victor/Documents/UU/Thesis/msc-agda-tactics/Agda

CODE_AGDA_MODULES=Basic\
                  CaseStudy1\
                  RelationsCore

COMPILER=pdflatex -etex


all: $(MAINPDF)

$(MAINPDF): \
	$(REFERENCES) $(MAINTEX) \
	$(TEXT_PARTS:%=$(TEXT_PARTS_SRC_GENTEX)/%.tex) \
	$(CODE_AGDA_STY) \
	$(CODE_AGDA_MODULES:%=$(CODE_AGDA_EXCERPTS)/%.tex)
	$(COMPILER) $(MAINTEX) #latexmk $(LATEXMKOPTS) $(MAINTEX)
	
force:
	$(COMPILER) $(MAINTEX)

$(CODE_AGDA_EXCERPTS)/%.tex: $(CODE_AGDA_SRC)/%.lagda
	$(DIRGUARD); agda --allow-unsolved-metas -i $(CODE_AGDA_STDLIB) -i $(CODE_AGDA_SRC) \
		-i $(CODE_AGDA_REL) --latex-dir=$(CODE_AGDA_EXCERPTS) --latex $<

bib: $(REFERENCES)
	rm -f thesis.bbl
	bibtex thesis

clean:
	rm -f *.log
	rm -f *.ptb
	rm -f *.aux
	rm -f *.toc
	rm -f *.blg
	
cleanall: clean
	rm -f thesis.pdf

veryclean: clean
	cd code/agda/excerpts && \
	rm -f *.tex

.PHONY: clean veryclean all

