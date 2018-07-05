
echo -ne "| Division | #problems |"
echo -ne "Asterix |"
echo -ne "CompSpen |"
echo -ne "CVC4 |"
echo -ne "Cyclist |"
echo -ne "Harrsh |"
echo -ne "Inductor |"
echo -ne "Sleek |"
echo -ne "Slide |"
echo -ne "Songbird |"
echo     "Spen |"
echo     "|-+-+-+-+-+-+-+-+-+-|"

ASTERIX="Perez"
COMPSPEN="Wu"
CVC4="Reynolds"
CYCLIST="cyclist"
HARRSH="harrsh"
INDUCTOR="Cristina"
SLEEK="Sleek"
SLIDE="Rogalewicz"
SB="Songbird"
SPEN="spen"

CONTS="($ASTERIX $COMPSPEN $CVC4 $CYCLIST $HARRSH $INDUCTOR $SLEEK $SLIDE $SB $SPEN)"

DIVS=`ls -d *_entl *_sat`
for d in $DIVS; 
do
	echo -ne "| =$d= "
	echo -ne "| `ls -l $d/*.smt2 | wc -l`"
	for c in $CONTS;
	do
		echo -ne "| `grep -l $c $d/*.smt2 | wc -l`"
	done
	echo "|"
done

echo     "|-+-+-+-+-+-+-+-+-+-|"

