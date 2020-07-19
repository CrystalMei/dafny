(set-option :smt.arith.solver 1) ; set diff logic solver
;(set-logic QF_IDL) 

(declare-const x Int)
(declare-const y Int)

; (push)
(assert (< x y))
(assert (< (+ x y) 10)); (smt.diff_logic: non-diff logic expression (+ x y))
;(assert (> (+ x y) 10))
(check-sat)
(get-model)
;(pop) ; remove the two assertions

;(push)
;(declare-const z Int)
;(assert (< (* x y) 10)); (smt.diff_logic: non-diff logic expression (* x y))
;(assert (< (+ x (* z y)) 10))
;(check-sat)
;(get-model)
;(pop) ; remove the two assertions

