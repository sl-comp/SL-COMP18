#!/bin/sh
# Included in bin

SOLVER=sleek
EXT=sle

FILE=`basename $1`
SL2SL=../smtlib2Xparser-sl/slcomp-parser
SL2SOLVER=../slcomp14tools/compile
CONFIG=./input.prop

echo "** $1"
cp $1 ${FILE}
rm -f $FILE.sl14*
$SL2SL --config $CONFIG --output SL_COMP14 $FILE 1> $FILE.sl14 2>/dev/null
$SL2SOLVER -$SOLVER $FILE.sl14 &>/dev/null
rm ${FILE} 
echo "** $FILE.sl14"
cat $FILE.sl14 
echo "** $FILE.sl14.$EXT"
cat ${FILE}.sl14.$EXT

