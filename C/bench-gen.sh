#!/bin/zsh

# arguments:
#   $1 : highest sequence length
#   $2 : repeats

for i in `seq 10 10 $1`
for j in `seq 1 1 $2`
do
  S=`cat /dev/urandom | tr -dc 'ACGU' | head -c$i`
  echo $S
done

