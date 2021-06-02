PACKAGES="opam m4 autoconf"

OPAM_PACKAGES="user-setup"

SWITCH="4.11.1+flambda"

sudo add-apt-repository ppa:avsm/ppa

sudo apt-get update

sudo apt-get install -y --no-install-recommends $PACKAGES

opam init -y -a --bare 

opam switch create -y $SWITCH

eval $(opam env)

opam install -y $OPAM_PACKAGES 

opam user-setup install
