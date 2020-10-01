.PHONY: all fmt clean grammar grammar-latex grammar-html

all:
	dune build

fmt:
	dune build @fmt --auto-promote

grammar:
	mkdir -p grammar

grammar-latex: grammar
	obelisk latex -o grammar/grammar.tex -prefix C -i src/parser.mly

grammar-html: grammar
	obelisk html -o grammar/grammar.html -i src/parser.mly

clean:
	dune clean
