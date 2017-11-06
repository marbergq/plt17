all:
	happy -gca ParCPPgrammar.y
	alex -g LexCPPgrammar.x
	ghc --make TestCPPgrammar.hs -o TestCPPgrammar

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi

distclean: clean
	-rm -f DocCPPgrammar.* LexCPPgrammar.* ParCPPgrammar.* LayoutCPPgrammar.* SkelCPPgrammar.* PrintCPPgrammar.* TestCPPgrammar.* AbsCPPgrammar.* TestCPPgrammar ErrM.* SharedString.* ComposOp.* CPPgrammar.dtd XMLCPPgrammar.* Makefile*
	
