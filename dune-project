(lang dune 2.7)
(name cervino)

(using menhir 2.1)

(cram enable)

(allow_approximate_merlin)

(generate_opam_files true)

(license MPL-2.0)
(maintainers "David Chemouil <david.chemouil+git@onera.fr>")
(authors "David Chemouil" "Julien Brunel" "Quentin Peyras" "Jean-Paul Bodeveix" )
(source (github grayswandyr/cervino))

(package
 (name cervino)
 (depends
  (ocaml (>= 4.11.0))
  (dune (>= 2.7.0))
  cmdliner
  (containers (>= 3.0))
  containers-data
  dune-build-info
  fmt
  hashcons
  logs
  menhir
  ppx_deriving
  ppx_expect 
  ppx_sexp_conv
  sexplib
  ;; Dev dependencies
  (bisect_ppx (and :dev (>= 2.5.0)))
  (ocamlformat :dev)
  )
 (synopsis "Proof of concept for complete verification of models expressed in a fragment of MSFOLTL"))
