#!/bin/bash

# ./do-compile-bench.sh dir-bench prefix-file
#
BENCH=$1
FILES=`ls $BENCH/$2*.smt2`
SL2SL=../smtlib2Xparser-sl/slcomp-parser
LOGF=$BENCH-$2.org

for f in $FILES
do
  # take action on each file. $f store current file name
  FN=`basename $f`
  echo "===== $FN"
  echo "===== $FN" >> $LOGF
  $SL2SL --config input.prop $f &> _log
  tail -n 1 _log >> $LOGF
  echo "====="
done

NFILES=`grep -n smt2 $LOGF | wc -l`
NCHECK=`grep -n check $LOGF | wc -l`

echo "$NFILES files vs $NCHECK checks"

if [ "$NFILES" -eq "$NCHECK" ]
then
	echo "ok"
else
	echo "nok"
fi

