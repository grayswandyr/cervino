
cd ~/ARTIFACT

ln -s ~/ARTIFACT/CERVINO/coq ~/ARTIFACT/COQ

cd COQ

cat << EOF >> README

------------------------------------------------------------
LOCATION OF THE LEMMAS AND THEOREMS CITED IN THE PAPER
------------------------------------------------------------

EOF

grep -n Paper *.v >> README

coq_makefile -o makefile *.v

make
