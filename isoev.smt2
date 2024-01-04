(set-logic QF_NIA)
(declare-fun a0 () Int)
(declare-fun a1 () Int)
(declare-fun a2 () Int)
(declare-fun a3 () Int)
(declare-fun a4 () Int)

(assert (>= (* a2 a0) a2))
(assert (>= (* a3 a0) a3))

(assert (>= (+ a1 (* a4 a0)) a4))

(assert (and (>= a0 1) (>= a1 0) (>= a2 1) (>= a3 1) (>= a4 0)))

(assert (or (and (> (* a2 a0) a2) (> (* a3 a0) a3)) (> (+ a1 (* a4 a0)) a4)))

(assert (and (or (> a0 1) (> a1 0)) (or (and (> a2 1) (> a3 1)) (> a4 0))))

(check-sat)
(get-model)
(exit)