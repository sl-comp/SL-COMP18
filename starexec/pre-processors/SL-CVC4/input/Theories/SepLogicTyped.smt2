(theory SepLogicTyped

 :funs ((emp Bool)
	(sep Bool Bool Bool :left-assoc)
	(wand Bool Bool Bool :right-assoc)
	(par (L D) (pto L D Bool))
	(par (L) (nil L))
	)
 
 :notes
 "The generic -- program independent -- signature for the Separation Logic
  with typed locations and typed heap."
 
 :definition
 "The SL-typed theory corresponds to signature of the SL logic in which: 
  - Memory locations are typed by using the 'declare-heap' command 
    which specifies a list of pairs of sort symbols (L D) denoting the
    sort of location L for a cell heap of type D

  - for any pair of sorts (L D) in the list of 'declare-heap' 

    - (as emp L D) denotes the empty heap space constraint typed by L -> D;

    - (sep sp ...) denotes the separating conjunction;

    - (wand sp sp') denotes the magic wand heap constraint;

    - (pto l d) denotes the points-to space constraint for location l to data cell d;

    - (as nil L) denotes the null location of sort L. 
 "
)
