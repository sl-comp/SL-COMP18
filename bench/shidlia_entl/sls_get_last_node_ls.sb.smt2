(set-logic SHIDLIA)
(set-info :source | Songbird - https://songbird-prover.github.io/ |)
(set-info :smt-lib-version 2)
(set-info :category "crafted")
(set-info :status unsat)

;; singleton heap

(declare-sort Refnode 0)

(declare-datatypes
 ((node 0))
 (((c_node (next Refnode) (val Int)))))

(declare-heap (Refnode node))

;; heap predicates

(define-fun-rec ls ((x_2 Refnode) (y_3 Refnode)) Bool
  (or
   (and
    (_ emp Refnode node)
    (= x_2 y_3))
   (exists
    ((anon_4 Int) (t_5 Refnode))
    (sep
     (pto x_2 (c_node t_5 (+ anon_4)))
     (ls t_5 y_3)))))

;; heap predicates

(define-fun-rec sls ((x_6 Refnode) (y_7 Refnode) (l_8 Int) (u_9 Int)) Bool
  (or
   (and
    (pto x_6 (c_node y_7 (+ l_8)))
    (= l_8 u_9))
   (exists
    ((t_10 Refnode) (a_11 Int))
    (and
     (sep
      (pto x_6 (c_node t_10 (+ l_8)))
      (sls t_10 y_7 (+ a_11) (+ u_9)))
     (and
      (<= 0 (+ (* (- 1) a_11) u_9))
      (<= (+ l_8) (+ a_11)))))))

(check-sat)

;; entailment: sls(x,y,l,u) |- (exists t. t->node{y,u} * ls(x,t))

(declare-const x Refnode)
(declare-const y Refnode)
(declare-const l Int)
(declare-const u Int)

(assert
 (sls x y l u))

(assert
 (not
  (exists
   ((t Refnode))
   (sep
    (pto t (c_node y u))
    (ls x t)))))

(check-sat)
