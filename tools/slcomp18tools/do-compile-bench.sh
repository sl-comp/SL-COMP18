#!/bin/bash

# ./do-compile-bench.sh dir-bench prefix-file
#
BENCH=$1
FILES=`ls $BENCH/$2*.smt2`

for f in $FILES
do
  # take action on each file. $f store current file name
  echo "===== $f"
  FN=`basename $f`
  ./slcomp-parser $f 
  echo "====="
done
