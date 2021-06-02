# REQUIRES: ocaml.sh desktop.sh

PACKAGES="libcairo2-dev libexpat1-dev libgmp-dev libgtk-3-dev libgtksourceview-3.0-dev adwaita-icon-theme-full"

sudo apt-get install -y --no-install-recommends $PACKAGES

opam install -y coq coqide