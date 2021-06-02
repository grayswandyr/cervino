cd ~/ARTIFACT

wget -nv https://github.com/grayswandyr/cervino/archive/refs/heads/cav2021.zip

unzip cav2021.zip

rm cav2021.zip

mv cervino-cav2021 CERVINO

cd CERVINO

opam install . --deps-only -y

opam install -y obelisk

dune build

make grammar-html
