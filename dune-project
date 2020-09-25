(lang dune 2.7)
(using menhir 2.0)

(name cervino)

(allow_approximate_merlin)

(generate_opam_files true)

(license MPL-2.0)
(maintainers "David Chemouil <david.chemouil+git@onera.fr>")
(authors "David Chemouil" "Julien Brunel")
(source (github grayswandyr/cervino))

(package
 (name cervino)
 (depends
  (ocaml (>= 4.05.0))
  (dune (>= 2.7))
  dune-build-info
  (containers (>= 3.0)) 
  menhir
  )
 (synopsis "Proof of concept for complete verification of models expressed in a fragment of Electrum."))
