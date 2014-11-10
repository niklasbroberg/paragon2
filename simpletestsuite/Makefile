all: Test

%: %.hs *.hs
	ghc -main-is $* -threaded --make $<

clean:
	rm -f Test
	rm -f *.hi *.o
	rm -f *~
	for l in `ls good` ; do \
		rm -f good/$$l/*.pi ; \
		rm -f good/$$l/*.java ; \
	done

test: Test
	./Test
