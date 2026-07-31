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

# ---- 自作の生成器（第15章〜第17章） ----
# mlex.mml と myacc.mml は単体で走る。
# selfhost.mml と ccomp.mml は、この処理系にモジュールが無いため
# build_all.py が両生成器の本体と各章の本体を連結して作る。
GEN = selfhost.mml ccomp.mml

$(GEN): mlex.mml myacc.mml selfhost_tail.mml ccomp_tail.mml meta.mml \
        build_gen.py build_all.py
	python3 build_all.py

gen: $(GEN)

# 生成器と応用の一式を走らせる
tools: miniml3 $(GEN)
	@for f in mlex.mml myacc.mml selfhost.mml ccomp.mml prolog.mml; do \
	  echo "========== $$f =========="; \
	  ./miniml3 $$f; \
	done

samples: miniml3
	@for f in samples/*.mml; do \
	  echo "========== $$f =========="; \
	  ./miniml3 $$f; \
	done

clean:
	rm -f miniml3 miniml.lex.sml miniml.grm.sml miniml.grm.sig miniml.grm.desc $(GEN)

.PHONY: all repl samples clean gen tools
