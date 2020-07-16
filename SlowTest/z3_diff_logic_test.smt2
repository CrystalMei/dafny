(echo "Z3 with Diff Logic Solver ...")
(set-option :smt.arith.solver 1) ; set diff logic solver
; (set-logic QF_IDL) 

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
; (push)
; (assert (< (+ x 5) 10))
; (assert (> (+ x 7) 10))
; (check-sat)
; (get-model)
; (pop) ; remove the two assertions

(push)
(assert (< x y))
(assert (< (+ x y) 10)); (smt.diff_logic: non-diff logic expression (+ x y))
(assert (> (+ x y) 10))
(check-sat)
; (get-model)
(pop) ; remove the two assertions

(push)
(assert (< (* x y) 10)); (smt.diff_logic: non-diff logic expression (* x y))
(assert (< (+ x (* z y)) 10))
(check-sat)
(get-model)
(pop) ; remove the two assertions

