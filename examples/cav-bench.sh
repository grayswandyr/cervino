#!/usr/bin/bash

# call with:
# ./bench.sh 
#

SAFETY="
CAV2021/leader.cervino
CAV2021/lock.cervino
CAV2021/mailbox_token.cervino
CAV2021/philo.cervino
CAV2021/TLB.cervino
"

LIVENESS="
CAV2021/2pset.cervino
CAV2021/fifo.cervino
CAV2021/gset.cervino
CAV2021/leader.cervino
CAV2021/mailbox_token.cervino
"


for f in $SAFETY; do
  echo ---------------------------------------------------
  /usr/bin/time -f "%e real, %U user, %S sys" cervino.exe -s Safety $f
done

for f in $LIVENESS; do
  echo ---------------------------------------------------
  /usr/bin/time -f "%e real, %U user, %S sys" cervino.exe -s Liveness $f 
done
