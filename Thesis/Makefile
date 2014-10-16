#	Template Makefile

OBJS=thesis.lagda\
     chap01.lagda
    
      	
OUT=thesis.pdf

COMPILER=latexmk -pdf -use-make -e '$$pdflatex=q/xelatex %O %S/'
		
all: fast

fast: $(OBJS)
	# ./latex-include-expand --output=megazord.lagda thesis.lagda && \
	lhs2TeX --agda -o latex/thesis.tex thesis.lagda && \
	postprocess-latex.pl latex/thesis.tex > latex/thesis.pp && \
	mv latex/thesis.pp latex/thesis.tex && \
	cd latex && \
	$(COMPILER) thesis.tex && \
	mv thesis.pdf ../thesis.pdf

slow: $(OBJS)
	# latex-include-expand --output=megazord.lagda thesis.lagda && \
	agda --latex thesis.lagda && \
	postprocess-latex.pl latex/thesis.tex > latex/thesis.pp && \
	mv latex/thesis.pp latex/thesis.tex && \
	cd latex && \
	$(COMPILER) thesis.tex && \
	mv thesis.pdf ../thesis.pdf
	
latexincludeexpand: LIE/Main.hs
	cd LIE && \
	ghc --make Main && \
	mv Main ../latex-include-expand
  
clean:
	rm -f latex/*

cleanall: clean
	rm thesis.pdf
	
backup:
	tar -cf "thesis_bckp.tar" *.lagda Makefile LIE
