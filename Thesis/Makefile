
DIRGUARD=@mkdir -p $(@D)

MAIN_NAME=thesis
REFERENCES_NAME=references
LATEXMKOPTS=-pdf -f -quiet
TEXT_PARTS_SRC_ROOT=text
TEXT_PARTS_SRC_GENTEX=$(TEXT_PARTS_SRC_ROOT)

MAINTEX=$(TEXT_PARTS_SRC_ROOT)/$(MAIN_NAME)_default.tex
UMTEX=$(TEXT_PARTS_SRC_ROOT)/$(MAIN_NAME)_um.tex
MAINPDF=./$(MAIN_NAME).pdf
REFERENCES=$(REFERENCES_NAME).bib
TEXT_PARTS=Agda_prelude \
           Background_prelude \
           Background_LambdaCalc \
           Background_MartinLof \
           Background_MartinLof_Derivation \
           RelationalAlgebra_prelude \
           RelationalAlgebra_SOTA \
           Problem \
           Intro \
           TermsAndRewriting_prelude \
           TANDR_EqReasoning \
           TANDR_Representation \
           TANDR_Reflection \
           TANDR_Tactic \
           TANDR_VAR_Transitivity \
           TANDR_VAR_Prelude \
           TANDR_VAR_Trie \
           thesis_core


CODE_AGDA_ROOT=code/agda
CODE_AGDA_SRC=$(CODE_AGDA_ROOT)/src
CODE_AGDA_EXCERPTS=$(CODE_AGDA_ROOT)/excerpts
CODE_AGDA_STY=./agda.sty
CODE_AGDA_STDLIB=/home/victor/Documents/UU/Thesis/agda-stdlib/src
CODE_AGDA_REL=/home/victor/Documents/UU/Thesis/msc-agda-tactics/Agda
CODE_AGDA_PRELUDE=/home/victor/Documents/UU/Thesis/msc-agda-tactics/Agda/stdlib-extensions
CODE_AGDA_RW=/home/victor/Documents/UU/Thesis/agda-rw

CODE_AGDA_MODULES=Basic\
                  MartinLof\
                  CaseStudy1\
                  RelationsCore\
                  ProofIrrel\
                  Universes\
                  RTerm\
                  RTerm-Examples\
                  Catas\
                  ReflectionExample\
                  FinTerm_Inst\
                  Strat\
                  RW\
                  Fin\
                  Transitivity

COMPILER=pdflatex -etex


all: $(MAINPDF)

$(MAINPDF): \
	$(REFERENCES) $(MAINTEX) \
	$(TEXT_PARTS:%=$(TEXT_PARTS_SRC_GENTEX)/%.tex) \
	$(CODE_AGDA_STY) \
	$(CODE_AGDA_MODULES:%=$(CODE_AGDA_EXCERPTS)/%.tex)
	$(COMPILER) $(MAINTEX) #latexmk $(LATEXMKOPTS) $(MAINTEX)
	
$(UMTEX):  \
	$(REFERENCES) $(UMTEX) \
	$(TEXT_PARTS:%=$(TEXT_PARTS_SRC_GENTEX)/%.tex) \
	$(CODE_AGDA_STY) \
	$(CODE_AGDA_MODULES:%=$(CODE_AGDA_EXCERPTS)/%.tex)
	$(COMPILER) $(UMTEX) #latexmk $(LATEXMKOPTS) $(MAINTEX)
  
	
force:
	$(COMPILER) $(MAINTEX)
	
um:
	$(COMPILER) $(UMTEX)

$(CODE_AGDA_EXCERPTS)/%.tex: $(CODE_AGDA_SRC)/%.lagda
	$(DIRGUARD); agda --allow-unsolved-metas -i $(CODE_AGDA_STDLIB) -i $(CODE_AGDA_SRC) \
		-i $(CODE_AGDA_REL) -i $(CODE_AGDA_PRELUDE) -i $(CODE_AGDA_RW) \
		--latex-dir=$(CODE_AGDA_EXCERPTS) --latex $<

bib: $(REFERENCES)
	rm -f thesis_default.bbl
	bibtex thesis_default
	
bibum : $(REFERENCES)
	rm -f thesis_um.bbl
	bibtex thesis_um

clean:
	rm -f *.log
	rm -f *.ptb
	rm -f *.aux
	rm -f *.toc
	rm -f *.blg
	
cleanall: clean
	rm -f thesis_default.pdf
	rm -f thesis_um.pdf

veryclean: cleanall
	cd code/agda/excerpts && \
	rm -f *.tex

.PHONY: clean veryclean all

