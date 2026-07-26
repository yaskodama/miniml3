# MINIML3 -- ML-Lex / ML-Yacc 版
MLTON  = mlton
MLLEX  = mllex
MLYACC = mlyacc

all: miniml3

miniml.lex.sml: miniml.lex
	$(MLLEX) miniml.lex

miniml.grm.sml miniml.grm.sig: miniml.grm
	$(MLYACC) miniml.grm

miniml3: miniml3.mlb absyn.sml value.sml types.sml show.sml prims.sml main.sml \
         miniml.lex.sml miniml.grm.sml miniml.grm.sig
	$(MLTON) -output miniml3 miniml3.mlb

repl: miniml3
	./miniml3

samples: miniml3
	@for f in samples/*.mml; do \
	  echo "========== $$f =========="; \
	  ./miniml3 $$f; \
	done

clean:
	rm -f miniml3 miniml.lex.sml miniml.grm.sml miniml.grm.sig miniml.grm.desc

.PHONY: all repl samples clean
