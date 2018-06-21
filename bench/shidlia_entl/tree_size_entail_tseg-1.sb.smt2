(set-logic SHIDLIA)
(set-info :source | Songbird - https://songbird-prover.github.io/ |)
(set-info :smt-lib-version 2)
(set-info :category "crafted")
(set-info :status unsat)

;; singleton heap

(declare-sort Refnode 0)

(declare-datatypes
 ((node 0))
 (((c_node (left Refnode) (right Refnode)))))

(declare-heap (Refnode node))

;; heap predicates

(define-fun-rec tree ((x_5 Refnode) (s_6 Int)) Bool
  (or
   (and
    (_ emp Refnode node)
    (and
     (= (as nil Refnode) x_5)
     (= s_6 0)))
   (exists
    ((l_7 Refnode) (r_8 Refnode) (s2_10 Int))
    (and
     (sep
      (pto x_5 (c_node l_7 r_8))
      (tree l_7 (+ (* (- 1) s2_10) s_6 (- 1)))
      (tree r_8 (+ s2_10)))
     (and
      (<= 0 (+ s2_10))
      (<= 0 (+ (* (- 1) s2_10) s_6 (- 1))))))))

;; heap predicates

(define-fun-rec tseg ((x_11 Refnode) (y_12 Refnode) (s_13 Int)) Bool
  (or
   (and
    (_ emp Refnode node)
    (and
     (= s_13 0)
     (= x_11 y_12)))
   (exists
    ((l_14 Refnode) (r_15 Refnode) (s2_17 Int))
    (and
     (sep
      (pto x_11 (c_node l_14 r_15))
      (tree l_14 (+ (* (- 1) s2_17) s_13 (- 1)))
      (tseg r_15 y_12 (+ s2_17)))
     (<= 0 (+ (* (- 1) s2_17) s_13 (- 1)))))
   (exists
    ((l_18 Refnode) (r_19 Refnode) (s2_21 Int))
    (and
     (sep
      (pto x_11 (c_node l_18 r_19))
      (tree r_19 (+ s2_21))
      (tseg l_18 y_12 (+ (* (- 1) s2_21) s_13 (- 1))))
     (<= 0 (+ s2_21))))))

(check-sat)

;; entailment: tree(x,n) & 10<=n |- (exists v,m. tseg(x,v,m))

(declare-const x Refnode)
(declare-const n Int)

(assert
 (and
  (tree x n)
  (<= 10 n)))

(assert
 (not
  (exists
   ((v Refnode) (m Int))
   (tseg x v m))))

(check-sat)
