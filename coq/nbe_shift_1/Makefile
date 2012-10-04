
COQC=coqc
COQDOC=coqdoc
DVIPDF=dvipdf
FILES=syntax.v model_structure.v  model_validity_cbv.v  model_validity_cbn.v  model_validity_generic.v nbe_cbv_atomic.v nbe_cbn_atomic.v nbe_tests.v

all: main doc

main:
	$(COQC) $(FILES)

doc:
	$(COQDOC) -d html -g --utf8 --toc --no-index $(FILES)

# doc-pdf:
# 	$(COQDOC) -p "\usepackage{hyperref}\hypersetup{colorlinks=true,linkcolor=red}" -o kripke_completeness.dvi --dvi -toc -g *.v
# 	$(DVIPDF) kripke_completeness.dvi

clean:
	rm -f *.vo *.glob html/class*.html html/int*.html html/std*.html html/coqdoc.css html/toc.html *.dvi *.pdf

