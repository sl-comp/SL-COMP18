(set-logic QF_SHID)

(set-info :source |
Jens Katelaan, Harrsh, https://github.com/katelaan/harrsh/
|)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)
(set-info :version "2018-06-21")

;; Trees with linked leaves

(declare-sort RefTll_t 0)

(declare-datatypes (
	(Tll_t 0)
	) (
	((c_Tll_t (lson RefTll_t) (rson RefTll_t) (next RefTll_t) ))
	)
)

(declare-heap (RefTll_t Tll_t)
)

(define-fun-rec tll ((r RefTll_t) (ll RefTll_t) (rl RefTll_t)) Bool
	(or
		(and (= r ll)
		     (pto r (c_Tll_t (as nil RefTll_t) (as nil RefTll_t) rl))
		)

		(exists ((ls RefTll_t) (rs RefTll_t) (z RefTll_t))

		(sep
			(pto r (c_Tll_t ls rs (as nil RefTll_t)))
			(tll ls ll z)
			(tll rs z rl)
		)

		)

	)
)

(check-sat)

;; variables
(declare-const x0 RefTll_t)
(declare-const x1 RefTll_t)
(declare-const x2 RefTll_t)
(declare-const x3 RefTll_t)
(declare-const x4 RefTll_t)
(declare-const x5 RefTll_t)
(declare-const x6 RefTll_t)
(declare-const x7 RefTll_t)
(declare-const x8 RefTll_t)

(assert
 (and
  (sep (tll x0 x1 x2)
      (tll x2 x3 x4)
      (tll x4 x5 x6)
      (tll x6 x7 x8)
      )
  (= x0 x1)
  (distinct x2 x3)
  (= x4 x5)
  (distinct x6 x7)
  (= x8 x0)
  (= x2 x6))
)

(check-sat)
