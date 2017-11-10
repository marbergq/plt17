all:
	happy -gca ParCPPGrammar.y
	alex -g LexCPPGrammar.x
	ghc --make TestCPPGrammar.hs -o TestCPPGrammar

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi

distclean: clean
	-rm -f DocCPPGrammar.* LexCPPGrammar.* ParCPPGrammar.* LayoutCPPGrammar.* SkelCPPGrammar.* PrintCPPGrammar.* TestCPPGrammar.* AbsCPPGrammar.* TestCPPGrammar ErrM.* SharedString.* ComposOp.* CPPGrammar.dtd XMLCPPGrammar.* Makefile*
	
