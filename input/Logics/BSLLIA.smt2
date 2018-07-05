(logic BSLLIA

 :smt-lib-version 2.6
 :written-by "Mihaela Sighireanu"
 :date "2018-07-04"
 :update-history
 "2018-07-04 Definition of the logic for SL-COMP'18.
 "

 :theories (Ints SepLogicTyped)

 :language
 "Closed formulas built over the SepLogicTyped signature,
  with the following restrictions:
  - formulas are boolean combination of pure or spatial atoms, 
  - no inductive definitions, 
  - 'wand' is not used,
  - integers may apear as content of the heap and parameters of predicates,
  - only linear constraints are allowed on integers.
 "

 :extensions 
 "Possible extensions are:

  - magic wand.
  "
)

