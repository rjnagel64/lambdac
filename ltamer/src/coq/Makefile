MODULES    := Axioms Binding Util Tactics DepList Scratchpad LambdaTamer NatMap
VS         := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	make -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) \
		COQC = "coqc -R . LambdaTamer" \
		COQDEP = "coqdep -R . LambdaTamer" \
		-o Makefile.coq

clean:: Makefile.coq
	make -f Makefile.coq clean
	rm -f Makefile.coq .depend
