(logic SHIDLIA

 :smt-lib-version 2.5
 :written-by "Mihaela Sighireanu"
 :date "2018-06-21"
 :last-updated "2018-06-21"
 :update-history
 "2018-06-21 Definition of the logic for SL-COMP'18.
 "

 :theories (SepLogicTyped Ints)

 :language
 "Closed formulas built over the SepLogicTyped signature,
  with the following restrictions:
  - formulas are only conjunction of pure or spatial atoms, i.e., 
    they belong to the symbolic heap fragment,
  - 'wand' is not used, 
  - the inductively defined predicates are `well formed` like in SMT-LIB standard, and
  - integers may be used as variables and predicate parameters,
  - only linear constraints are allowed for integers.
 "

 :extensions 
 "Possible extensions are:
 
  - boolean combination of atoms,
  
  - magic wand.
  "
)

