#	Template Makefile

OBJS=thesis.lagda\
     chap01.lagda
    
      	
OUT=thesis.pdf
		
all: megazord.lagda
	cd latex && \
	vtex megazord.tex && \
	mv megazord.pdf ../thesis.pdf	
	
megazord.lagda: latexincludeexpand megazord

megazord: $(OBJS)
	./latex-include-expand --output=megazord.lagda thesis.lagda && \
	lhs2TeX --agda -o latex/megazord.tex megazord.lagda && \
	postprocess-latex.pl latex/megazord.tex > latex/megazord.pp && \
	mv latex/megazord.pp latex/megazord.tex

megazordAGDA: $(OBJS)
	latex-include-expand --output=megazord.lagda thesis.lagda && \
	agda --latex megazord.lagda && \
	postprocess-latex.pl latex/megazord.tex > latex/megazord.pp && \
	mv latex/megazord.pp latex/megazord.tex
	
latexincludeexpand: LIE/Main.hs
	cd LIE && \
	ghc --make Main && \
	mv Main ../latex-include-expand
  
clean:
	rm -f megazord.lagda
	rm -f latex/*

cleanall: clean
	rm thesis.pdf
	
backup:
	tar -cf "thesis_bckp.tar" *.lagda Makefile LIE
