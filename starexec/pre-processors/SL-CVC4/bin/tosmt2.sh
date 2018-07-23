#!/bin/bash

echo ";; $1"

# change logics
#sed -i "" -e "s/QF_BSLLIA/ALL_SUPPORTED/g" $1
#sed -i "" -e "s/QF_BSL/ALL_SUPPORTED/g" $1
sed -i "" -e "s/BSLLIA/ALL_SUPPORTED/g" $1
sed -i "" -e "s/BSL/ALL_SUPPORTED/g" $1

# remove set-info
sed -i "" -e "s/(set-info /;;(set-info /g" $1
# remove 'declare-heap'
sed -i "" -e "s/^(declare-heap (\([a-zA-Z]*\) \([a-zA-Z]*\)))$//g" $1

ISDATA=`grep Node $1`
#echo $ISDATA
DATA='loc0'
if [ "$ISDATA" ]; then
	DATA='data0'
fi
#echo $DATA

# add 'sep.' to nil
sed -i "" -e "s/ nil / sep.nil /g" $1

# replace '(_emp Loc Node)' by '(emp loc0 data0)'
sed -i "" -e "s/(_ emp Loc \([a-zA-Z0-9]*\))/(emp loc0 $DATA)/g" $1

