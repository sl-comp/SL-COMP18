(logic SHID

 :smt-lib-version 2.5
 :written-by "Mihaela Sighireanu"
 :date "2014-05-22"
 :last-updated "2018-05-05"
 :update-history
 "2018-05-05 Updated to the new theory SepLogicTyped and SMT-LIB Version 2.5.
  2014-05-25 Definition of the logic for the UDB* division.
 "

 :theories (SepLogicTyped)

 :language
 "Closed formulas built over the SepLogicTyped signature,
  with the following restrictions:
  - formulas are only conjunction of pure or spatial atoms, i.e., 
    they belong to the symbolic heap fragment,
  - 'wand' is not used, and
  - the inductively defined predicates are `well formed` like in SMT-LIB standard.
 "

 :extensions 
 "Possible extensions are:
 
  - boolean combination of atoms,
  
  - data,
  
  - magic wand.
  "
)

