.PHONY: generate-ast

generate-ast:
	eval $$(opam env) && \
	clightgen -normalize allequal.c