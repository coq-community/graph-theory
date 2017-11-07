COQVERSION=$(shell coqc -v | grep version | cut -d' ' -f 6 )

EXTRA_DIR:=coqdocjs/extra
COQDOCFLAGS:= \
  --external 'http://math-comp.github.io/math-comp/htmldoc/' mathcomp \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage -s --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS

all: Makefile.coq
	+make -f Makefile.coq all

html: Makefile.coq
	+make -f Makefile.coq html
	cp $(EXTRA_DIR)/resources/* html/

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq .*.aux

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -arg -w -arg -notation-overridden >Makefile.coq

.PHONY: all html clean
