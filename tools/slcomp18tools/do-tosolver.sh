
## call by ./do-tosolver.sh [spen|sleek|cyclist|slp]

# Format
SOLVER=$1
FILE=$2
OFILE=`basename $FILE`
SL2SL=../smtlib2Xparser-sl/slcomp-parser 
SL2SOLVER=../slcomp14tools/compile 

echo "** translate to input format of SL-COMP'14"
$SL2SL --config input.prop --output SL_COMP14 $FILE > $OFILE.sl14
echo "** translate to input format of solver $SOLVER"
$SL2SOLVER -$SOLVER $OFILE.sl14 

