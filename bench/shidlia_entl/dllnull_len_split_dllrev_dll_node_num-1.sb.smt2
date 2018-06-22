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

(define-fun-rec dll ((hd_1 Refnode) (p_2 Refnode) (tl_3 Refnode) (n_4 Refnode) (l_5 Int)) Bool
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
      (pto hd_1 (c_node x_6 p_2))
      (dll x_6 hd_1 tl_3 n_4 (+ l_5 (- 1))))
     (<= 1 (+ l_5 (- 1)))))))

;; heap predicates

(define-fun-rec dll_rev ((hd_7 Refnode) (p_8 Refnode) (tl_9 Refnode) (n_10 Refnode) (l_11 Int)) Bool
  (or
   (and
    (pto hd_7 (c_node n_10 p_8))
    (and
     (= (+ l_11 (- 1)) 0)
     (= hd_7 tl_9)))
   (exists
    ((x_12 Refnode))
    (and
     (sep
      (pto tl_9 (c_node n_10 x_12))
      (dll_rev hd_7 p_8 x_12 tl_9 (+ l_11 (- 1))))
     (<= 1 (+ l_11 (- 1)))))))

;; heap predicates

(define-fun-rec dllnull ((hd_13 Refnode) (p_14 Refnode) (l_15 Int)) Bool
  (or
   (and
    (pto hd_13 (c_node (as nil Refnode) p_14))
    (= (+ l_15 (- 1)) 0))
   (exists
    ((x_16 Refnode))
    (and
     (sep
      (pto hd_13 (c_node x_16 p_14))
      (dllnull x_16 hd_13 (+ l_15 (- 1))))
     (<= 1 (+ l_15 (- 1)))))))

(check-sat)

;; entailment: dllnull(x,y,101) |- (exists z,t,u,v,n1,n2. v->node{nil,u} * dll(t,z,u,v,n2) * dll_rev(x,y,z,t,n1) & n1+n2=100)

(declare-const x Refnode)
(declare-const y Refnode)

(assert
 (dllnull x y 101))

(assert
 (not
  (exists
   ((z Refnode) (t Refnode) (u Refnode) (v Refnode) (n1 Int) (n2 Int))
   (and
    (sep
     (pto v (c_node (as nil Refnode) u))
     (dll t z u v n2)
     (dll_rev x y z t n1))
    (= (+ n1 n2) 100)))))

(check-sat)
