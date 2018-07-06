(logic QF_SHIDLIA

 :smt-lib-version 2.6
 :written-by "Mihaela Sighireanu"
 :date "2014-05-22"
 :last-updated "2018-06-21"
 :update-history
 "2018-05-25 Definition of the logic for SL-COMP'18.
 "

 :theories (SepLogicTyped Ints)

 :language
 "Closed quantifier-free formulas built over the SepLogicTyped signature,
  with the following restrictions:
  - formulas are only conjunction of pure or spatial atoms, i.e., 
    they belong to the symbolic heap fragment,
  - 'wand' is not used, and
  - the inductively defined predicates are `well formed` like in SMT-LIB standard,
  - integers may apear as content of the heap and parameters of predicates,
  - only linear constraints are allowed on integers.
 "

 :extensions 
 "Possible extensions are:
 
  - boolean combination of atoms,
  
  - magic wand.
  "
)

