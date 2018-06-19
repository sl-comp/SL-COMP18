(set-logic QF_SHID)

(set-info :source |
Jens Katelaan, Harrsh, https://bitbucket.org/jkatelaan/harrsh
|)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status sat)
(set-info :version "2018-06-18")

;; Lasso-shaped list structure

(declare-sort RefSll_t 0)

(declare-datatypes (
	(Sll_t 0)
	) (
	((c_Sll_t (next RefSll_t) ))
	)
)

(declare-heap (RefSll_t Sll_t) 
)

;; Underlying singly-linked list that forms the loop
(define-fun-rec sll ((x RefSll_t) (y RefSll_t)) Bool
	(or 
		(and (= x y)
		     (_ emp RefSll_t Sll_t)
		)

		(exists ((u RefSll_t))
	 
		(and 
			(distinct x y)
		(sep 
			(pto x (c_Sll_t u ))
			(sll u y )
		)
		)
		)
	)
)

;; Lasso-shaped list structure
(define-fun-rec lasso ((x RefSll_t)) Bool
	(or
		(exists ((y RefSll_t))
			(sep (pto x (c_Sll_t y)) (lasso y))
		)
		(exists ((y RefSll_t))
			(sep (pto x (c_Sll_t y)) (sll y x))
		)
	)
)

(check-sat)
;; variables
(declare-const x0 RefSll_t)

(assert (lasso x0)
)

(check-sat)
