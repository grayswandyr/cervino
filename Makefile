.PHONY: all fmt clean deps grammar grammar-latex grammar-html switch test watch

project_name = cervino

opam_file = $(project_name).opam

opam_switch = 4.11.0

all:
	dune build

watch:
	dune build @check @fmt --auto-promote -w

fmt:
	dune build @fmt --auto-promote

test:
	find . -name '*.coverage' | xargs rm -f
	dune runtest --instrument-with bisect_ppx --force
	bisect-ppx-report html
	bisect-ppx-report summary
	xdg-open _coverage/index.html

deps: $(opam_file)

$(opam_file): dune-project
	-dune build @install        # Update the $(project_name).opam file
	-git add $(opam_file)       # opam uses the state of master for it updates
	-git commit $(opam_file) -m "Updating package dependencies"
	opam install . --deps-only  # Install the new dependencies

grammar:
	mkdir -p grammar

grammar-latex: grammar
	obelisk latex -o grammar/grammar.tex -prefix C -i src/parser.mly

grammar-html: grammar
	obelisk html -o grammar/grammar.html -i src/parser.mly

switch: deps
	opam switch create . $(opam_switch) --deps-only

clean:
	dune clean
	rm -rf _coverage
