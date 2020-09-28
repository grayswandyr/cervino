.PHONY: all fmt clean grammar-latex grammar-html

all:
	dune build

fmt:
	dune build @fmt --auto-promote

grammar-latex:
	obelisk latex -o grammar/grammar.tex -prefix C -i src/parser.mly

grammar-html:
	obelisk html -o grammar/grammar.html -i src/parser.mly

clean:
	dune clean
