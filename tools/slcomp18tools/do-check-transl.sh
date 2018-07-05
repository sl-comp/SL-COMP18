#!/bin/bash

# ./do-compile-bench.sh dir-bench prefix-file
#
BENCH=$1
FILES=`ls $BENCH/$2*.smt2`
SL2SL=../smtlib2Xparser-sl/slcomp-parser
SL2SOLVER=../slcomp14tools/compile 
LOGF=$BENCH-$2.org
LOGFF=$BENCH-$2.sl14.org

for f in $FILES
do
  # take action on each file. $f store current file name
  FN=`basename $f`
  echo "===== $FN"
  echo "===== $FN" >> $LOGF
  echo "===== $FN" >> $LOGFF
  $SL2SL --config input.prop --output SL_COMP14 $f 1> $FN.sl14 2> _log
  tail -n 1 $FN.sl14 >> $LOGF
  $SL2SOLVER -sleek $FN.sl14 2> _log
  tail -n 4 _log >> $LOGFF
  # rm *.sl14*
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

TCHECK=`grep -n Done $LOGFF | wc -l`

echo "$NFILES files vs $TCHECK translated"

