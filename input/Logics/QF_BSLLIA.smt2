(logic QF_BSLLIA

 :smt-lib-version 2.6
 :written-by "Mihaela Sighireanu"
 :date "2018-06-21"
 :update-history
 "2018-06-21 Definition of the logic for SL-COMP 2018.
  2017-06-21 CVC4 supports SL.
 "

 :theories (SepLogicTyped Ints)

 :language
 "Closed quantifier-free formulas built over the SepLogicTyped signature,
  wih bounded heap and with the following restrictions:
  - formulas are any boolean combination of pure and spatial atoms,
  - no inductive definitions,
  - integers may be used as locations and heap content,
  - only linear constraints between integers.
 "

)

