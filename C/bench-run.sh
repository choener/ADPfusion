#!/usr/bin/env zsh

# arguments:
#   stdin: lines
#   $1: program to use

typeset -A k
typeset -A t
typeset -A m

while read i
do
  k[${#i}]="${#i}"
#  echo $i
#  t[${#i}]+=" ${#i}"
#  m[${#i}]+=" ${#i}"
#  echo $i | /usr/bin/time -f "%e %M" $1
  var1=`echo $i | time -f "%e %M" $1` 2>&1 | read var2
#  echo "O $var1"
#  echo "E $var2"
  a=("${(@s/ /)var2}")
  t[${#i}]+=" $a[1]"
  m[${#i}]+=" $a[2]"

  >&2 echo ${#i} $i
  >&2 echo $a
done

#print $k
#print $t
#print $m

echo "time"

for i in "${(@k)k}"; do
  # echo "$i -> $t[$i]"
  n=("${(@s/ /)t[$i]}")
  n[1]=0
  (( sum=${(j:+:)n} ))
  echo $i $(( $sum / $(( ${#n} - 1 )) ))
done | sort -n

echo "mem"

for i in "${(@k)k}"; do
  # echo "$i -> $t[$i]"
  n=("${(@s/ /)m[$i]}")
  n[1]=0
  (( sum=${(j:+:)n} ))
  echo $i $(( $sum / $(( ${#n} - 1 )) ))
done | sort -n

