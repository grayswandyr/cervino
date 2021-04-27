#!/usr/bin/bash

# call with:
# ./bench.sh path/to/electrum/jar
#

export ELECTRUM_JAR=$1

SAFETY="
CAV2021/mailbox_token.cervino
CAV2021/leader.cervino
CAV2021/lock.cervino
CAV2021/TLB.cervino
CAV2021/philo.cervino
"

LIVENESS="
CAV2021/mailbox_token.cervino
CAV2021/leader.cervino
CAV2021/fifo.cervino
CAV2021/2pset.cervino
CAV2021/gset.cervino
"

for f in $SAFETY; do
  echo ---------------------------------------------------
  time cervino.exe -s Safety $f
done

for f in $LIVENESS; do
  echo ---------------------------------------------------
  time cervino.exe -s Liveness $f 
done
