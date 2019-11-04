COQVERSION=$(shell coqc -v | grep version | cut -d' ' -f 6 )

EXTRA_DIR:=coqdocjs/extra
PACK:=graphs
VERSION:=current
PACKED_FILES:= \
 _CoqProject Makefile README files.txt html/ \
  depend-colors.gv

COQDOCFLAGS:= \
  -R . $(PACK) \
  --external 'http://math-comp.github.io/math-comp/htmldoc/' mathcomp \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage -s --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS

-include Makefile.coq.conf

all: Makefile.coq
	+make -f Makefile.coq all

quick: Makefile.coq
	+make -f Makefile.coq quick

vio2vo: Makefile.coq
	+make -f Makefile.coq vio2vo


html: Makefile.coq
	+make -f Makefile.coq html
	cp $(EXTRA_DIR)/resources/* html/

graph: Makefile.coq
	$(COQBIN)coqdep $(COQMF_COQLIBS) -dyndep var -c -dumpgraph depend-graph.gv $(COQMF_VFILES) >/dev/null
	sed -i '1d;s/\[label=\"\([^"]*\)\"]/[label="\1";URL=".\/$(VERSION)\/graphs.\1.html"]/g' depend-graph.gv
	cat depend-colors.gv depend-graph.gv | dot -o depend-graph.dot
	dot -Tsvg depend-graph.dot -o depend-graph.svg

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq .*.aux depend-graph.*

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

pack: html
	egrep '^[a-z1-9_]*\.v' _CoqProject | xargs tar czf $(PACK)-$(VERSION).tgz --transform "s,^,$(PACK)-$(VERSION)/," $(PACKED_FILES)

.PHONY: all html clean
