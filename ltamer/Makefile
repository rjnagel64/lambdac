.PHONY: all clean coqtop package

all: coq

coq:
	$(MAKE) -C src/coq

clean:
	$(MAKE) -C src/coq clean

coqtop:
	coqtop -impredicative-set -R src/coq LambdaTamer

package:
	hg archive -t tgz /tmp/ltamer.tgz
