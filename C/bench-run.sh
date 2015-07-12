#!/bin/zsh

# arguments:
#   stdin: lines
#   $1: program to use

typeset -A t
typeset -A m

while read i
do
#  echo $i
  t[${#i}]+=" ${#i}"
  m[${#i}]+=" ${#i}"
#  echo $i | /usr/bin/time -f "%e %M" $1
  var1=`echo $i | /usr/bin/time -f "%e %M" $1` 2>&1 | read var2
#  echo "O $var1"
#  echo "E $var2"
  a=("${(@s/ /)var2}")
  t[${#i}]+=" $a[1]"
  m[${#i}]+=" $a[2]"
done

print $t
print $m

