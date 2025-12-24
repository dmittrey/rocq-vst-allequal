.PHONY: build generate-ast clean

build:
	eval $$(opam env) && \
	coqc allequal.v && \
	coqc Verif_allequal.v

generate-ast:
	eval $$(opam env) && \
	clightgen -normalize allequal.c

clean:
	rm -f *.vos *.vok *.glob *.cache
	rm -rf .coq-native .lia.cache
	rm -f .*aux .*d *.d