# CERVINO

The Cervino tool takes formal specifications as input and applies sound (but incomplete) verification procedures to check whether some temporal properties are satisfied. 

Note: technically, the tool compiles Cervino problems into Electrum models. In order to implement fully the verification made possible by Cervino, those must then be verified with the [Electrum Analyzer](http://haslab.github.io/Electrum/) using the [nuXmv](https://nuxmv.fbk.eu/) model checker, which must therefore also be installed.

## Building Cervino

To build Cervino, you first need a working installation of OCaml 4.11, supported by the [`opam` tool](https://opam.ocaml.org/doc/Install.html).

Then, download or clone this repository, `cd` into it and then type the following commands:
```sh
$ opam install . --deps-only -y

$ dune build
```
This will build a `cervino.exe` executable in the directory.

## Running Cervino

The syntax of a command is:

       cervino.exe [OPTIONS] PROPERTY CERVINO_FILE [OUTPUT_FILE]

with arguments:

       CERVINO_FILE (required)
           Input (Cervino) file.

       PROPERTY (required)
           Name of the property to check.

       OUTPUT_FILE
           Name of the file to generate.

Among OPTIONS, the following may be of interest:

       --electrum-jar=PATH, --ej=PATH (absent ELECTRUM_JAR env)
           Path to the Electrum Analyzer JAR file. Instead, the ELECTRUM_JAR environment variable may be set to the same effect.
       --java=PATH (absent=java)
           Path to the `java` program
       -s, --solve
           If present, let Cervino call the Electrum Analyzer solver (with the nuXmv model checker) on the generated Electrum file and report its result. The Electrum Analyzer and nuXmv must be properly installed. The path to the JAR containing the Electrum Analyzer must be set using the --ej option or ELECTRUM_JAR environment variable. The `java` program must also be in the PATH (or the --java option should be used). Notice also that, if this option is used, it's not necessary to provide the OUTPUT_FILE argument mentioned above (unless one wishes to read it later).

Other command-line options are *not* meant to be used.

## Running the Electrum Analyzer and nuXmv independantly from Cervino

After generating an Electrum file with Cervino, the latter should be analyzed using the Electrum Analyzer (relying on the nuXmv model-checker). The whole process can be automated using the `-s` option mentioned above.

Otherwise, provided the generated file is called `output.als`, the user may issue the following command:

        java -jar /path/to/electrum.jar --cli --nuXmv output.als

If the Electrum Analyzer prints `outcome UNSAT` (among other messages) then the original property is valid. Otherwise, we cannot conclude.

## Cervino models

For a detailed view of the syntax, please refer to files in the `benchmarks` directory, as well as our paper. Remark also that the syntax is heavily inspired by that of Alloy or Electrum. Finally, the grammar can be generated using the `make grammar-html` command (you must first install the `obelisk` tool through opam, using `opam install obelisk`).

A Cervino *specification*  is described by various paragraphs, separated by blank characters:

* data aspects
  * sorts
  * (flexible) sorted relations
  * (rigid) constants
  * "paths" specifications
* axioms
* event schemas 
* properties to check under a transformation

The main difference with our paper is the declaration of so-called *paths*. In our paper, if a binary relation *r* is declared, followed by the mention `using btw`, then the user can refer to a specific relation, written `btw[r]`, which satisfies certain axioms. It is also possible to refer to the reflexive-transitive closure of the relation by writing `r*`. In the current version of the tool, this is a bit different syntactically:

* the relations standing for `r*` and `btw[r]` must be explicitily declared by the user, like plain relations (e.g. `relation r_star in None * Node` and `relation r_btw in Node * Node * Node`)
* a specific `paths` command should be issued, as `paths[r, r_star]` if one only needs the reflexive-transitive closure, or as `paths[r, r_star, r_btw]` if one needs the "between" relation too.

Axioms, event bodies and checked properties are sets of formulas (again separated by blank characters). Classic propositional connectors are written: `&&`, `||` `=>`, `<=>`, `!` (for "not"). Existential quantification is written `some x: s | p(x)`, similarly for universal quantification (with quantifier `all`). "If c then t else e" is written `c => t else e`. The usual temporal connectives are written `G` ("always"), `F` ("eventually") and `X` ("next").

A property to be checked is introduced by the `check` keyword, followed by the body of the property and the transformation to apply (preceded by the keyword `using`). Three transformations are available; they all take different parameters so their syntax differs:

* TEA takes no parameters: `using TEA[]`.
* TFC takes a list of pairs, every pair is an event name followed by a "stability axiom" (as explained in the paper).
* TTC takes:
    * a binary relation
    * a distinguished variable and its sort
    * a list of *n** bound, sorted variables (for some *n*)
    * an atom (relation of arity *n+1* + its parameters)
