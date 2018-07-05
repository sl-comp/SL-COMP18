(logic QF_SHID

 :smt-lib-version 2.6
 :written-by "Mihaela Sighireanu"
 :date "2014-05-25"
 :last-updated "2018-05-05"
 :update-history
 "2018-05-05 Updated to the new theory SepLog and SMT-LIB Version 2.6.
  2014-05-25 Definition of the logic for the UDB* division.
 "

 :theories (SepLogicTyped)

 :language
 "Closed quantifier-free formulas built over the SepLogTyped signature,
  with the following restrictions:
  - formulas are only conjunction of pure or spatial atoms, i.e., 
    they belong to the symbolic heap fragment,
  - 'wand' is not used, and
  - the inductively defined predicates are `well formed` like in the SMT-LIB standard.
 "

 :extensions 
 "Possible extensions are:
 
  - boolean combination of atoms,
  
  - data,
  
  - magic wand.
  "
)

