(logic QF_SHLID

 :smt-lib-version 2.6
 :written-by "Mihaela Sighireanu"
 :date "2014-05-25"
 :last-updated "2018-05-05"
 :update-history
 "2018-05-05 Updated to the new theory SepLogTyped and SMT-LIB Version 2.5.
  2014-05-25 Definition of the logic for the FDB* division.
 "

 :theories (SepLogicTyped)

 :language
 "Closed quantifier-free formulas built over the SepLogTyped signature,
  with the following restrictions:
  - formulas are only conjunction of pure or spatial atoms, i.e., 
    they belong to the symbolic heap fragment,
  - 'wand' is not used, and
  - the inductively defined predicates are `linear`, i.e.,
    only one recursive case calling the defined predicate.
 "

 :extensions 
 "Possible extensions are:
 
  - boolean combination of atoms,
  
  - data,
  
  - cyclic lists.
  "
)

