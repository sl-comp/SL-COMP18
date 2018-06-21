(set-logic SHIDLIA)
(set-info :source | Songbird - https://songbird-prover.github.io/ |)
(set-info :smt-lib-version 2)
(set-info :category "crafted")
(set-info :status unsat)

;; singleton heap

(declare-sort Refnode 0)

(declare-datatypes
 ((node 0))
 (((c_node (next Refnode) (prev Refnode)))))

(declare-heap (Refnode node))

;; heap predicates

(define-fun-rec dll_rev ((hd_1 Refnode) (p_2 Refnode) (tl_3 Refnode) (n_4 Refnode) (l_5 Int)) Bool
  (or
   (and
    (pto hd_1 (c_node n_4 p_2))
    (and
     (= (+ l_5 (- 1)) 0)
     (= hd_1 tl_3)))
   (exists
    ((x_6 Refnode))
    (and
     (sep
      (pto tl_3 (c_node n_4 x_6))
      (dll_rev hd_1 p_2 x_6 tl_3 (+ l_5 (- 1))))
     (<= 1 (+ l_5 (- 1)))))))

;; heap predicates

(define-fun-rec dllnull ((hd_7 Refnode) (p_8 Refnode) (l_9 Int)) Bool
  (or
   (and
    (pto hd_7 (c_node (as nil Refnode) p_8))
    (= (+ l_9 (- 1)) 0))
   (exists
    ((x_10 Refnode))
    (and
     (sep
      (pto hd_7 (c_node x_10 p_8))
      (dllnull x_10 hd_7 (+ l_9 (- 1))))
     (<= 1 (+ l_9 (- 1)))))))

(check-sat)

;; entailment: dllnull(x,y,n) & 100<=n |- (exists z,t. t->node{nil,z} * dll_rev(x,y,z,t,n-1))

(declare-const x Refnode)
(declare-const y Refnode)
(declare-const n Int)

(assert
 (and
  (dllnull x y n)
  (<= 100 n)))

(assert
 (not
  (exists
   ((z Refnode) (t Refnode))
   (sep
    (pto t (c_node (as nil Refnode) z))
    (dll_rev x y z t (+ n (- 1)))))))

(check-sat)
