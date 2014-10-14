MODULES := Basic Labels Terms \
	LBracketSyntax \
	LBracketBigStep \
	LBracketSmallStep \
	LThrowBigStep \
	LThrowSmallStep \
	LNaVSyntax \
	LNaVBigStep \
	LNaVSmallStep \
	LThrowDBigStep \
	LThrowDSmallStep \
	EncodeLNaVintoLThrow \
	EncodeLThrowIntoLNaV \
	EncodeLThrowIntoLNaVTakeTwo \
	EncodeLNaVintoLBracket \
	EncodeLThrowDIntoLThrow \
	EncodeLThrowIntoLThrowD \
	FourPoints \
	Everything \
	LBracketEquiv \
	LBracketNI \
	LThrowNI \
	LNaVNI \
	LThrowDNI \
	LNaVProgress

VS 	:= $(MODULES:%=%.v)

.PHONY: coq doc clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

all: coq doc extract

Makefile.coq: Makefile $(VS:%=%)
	echo $(VS)
	coq_makefile $(VS) -o Makefile.coq

extract: coq
	cd target; coqc ExtractLibraryHaskell.v; cd ..
	ghc -itarget Testing.hs

clean:
	rm -f Makefile.coq .depend *.v.d *.vo *.glob
	rm -fr html
	rm -f target/*.hs *.hi target/*.hi *.o target/*.o

doc:
	$(MAKE) -f Makefile.coq html
