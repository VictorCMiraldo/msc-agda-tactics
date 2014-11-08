#	Template Makefile

OBJS=thesis.lagda\
     SectionAgdaLang.lagda\
     MartinLof_prelude.lagda
    
      	
OUT=thesis.pdf

#COMPILER=latexmk -f -pdf -use-make -e '$$pdflatex=q/xelatex %O %S/'
#COMPILER=vtex
COMPILER=pdflatex -etex
		
all: slow

fast:
	# ./latex-include-expand --output=megazord.lagda thesis.lagda && \
	lhs2TeX --agda -o latex/thesis.tex thesis.lagda && \
	# postprocess-latex.pl latex/thesis.tex > latex/thesis.pp && \
	# mv latex/thesis.pp latex/thesis.tex && \
	cd latex && \
	$(COMPILER) thesis.tex && \
	mv thesis.pdf ../thesis.pdf

slow: $(OBJS)
	latexpand --explain thesis.lagda > Megazord.lagda && \
	agda -i/home/victor/Documents/UU/Thesis/agda-stdlib/src -i. --latex Megazord.lagda && \
	# postprocess-latex.pl latex/thesis.tex > latex/thesis.pp && \
	# mv latex/thesis.pp latex/thesis.tex && \
	cd latex && \
	# lhs2TeX -o megazord2.tex megazord.tex \
	$(COMPILER) Megazord.tex && \
	mv Megazord.pdf ../thesis.pdf
	
bib: thesisbib.bib
	cd latex && \
	bibtex Megazord
  
	
#latexincludeexpand: LIE/Main.hs
#	cd LIE && \
#	ghc --make Main && \
#	mv Main ../latex-include-expand
  
clean:
	rm -f latex/*

cleanall: clean
	rm thesis.pdf
	
backup:
	tar -cf "thesis_bckp.tar" *.lagda Makefile LIE
