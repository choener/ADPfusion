#!/bin/bash
echo "" > rnafold-1
echo "" > rnafold-2
for i in `seq -w 100 100 1000`
do
  echo $i && zcat $i.input.gz | /usr/bin/time -ao rnafold-1 RNAfold > /dev/null
done
for i in `seq -w 100 100 1000`
do
  echo $i && zcat $i.input.gz | /usr/bin/time -ao rnafold-2 /home/mescalin/ronny/WORK/ViennaRNA.work/Progs/RNAfold  > /dev/null
done
