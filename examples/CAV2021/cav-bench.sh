#!/usr/bin/bash

# call with:
# ./bench.sh 
#

SAFETY="
leader.cervino
lock.cervino
mailbox_token.cervino
philo.cervino
TLB.cervino
"

LIVENESS="
2pset.cervino
fifo.cervino
gset.cervino
leader.cervino
mailbox_token.cervino
"


for f in $SAFETY; do
  echo ---------------------------------------------------
  /usr/bin/time -f "%e real, %U user, %S sys" cervino.exe -s Safety $f
done

for f in $LIVENESS; do
  echo ---------------------------------------------------
  /usr/bin/time -f "%e real, %U user, %S sys" cervino.exe -s Liveness $f 
done
