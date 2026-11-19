all: Makefile.rocq
	$(MAKE) -f Makefile.rocq

Makefile.rocq: _CoqProject
	rocq makefile -f _CoqProject -o Makefile.rocq

clean: Makefile.rocq
	$(MAKE) -f Makefile.rocq cleanall
	rm -f Makefile.rocq Makefile.rocq.conf

.PHONY: all clean
