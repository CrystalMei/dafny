(echo "Z3 with Diff Logic Solver ...")
(set-option :smt.arith.solver 1) ; set diff logic solver
(set-logic QF_IDL) ; necessary, need to set the integer-diff-logic as well

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(push)
(assert (< (+ x 5) 10))
(assert (> (+ x 7) 10))
(check-sat)
(get-model)
(pop) ; remove the two assertions

(push)
(assert (< (+ x y) 10)); (smt.diff_logic: non-diff logic expression (+ x y))
(assert (> (+ x y) 10))
(check-sat)
(pop) ; remove the two assertions

(push)
(assert (< (* x y) 10)); (smt.diff_logic: non-diff logic expression (* x y))
(assert (< (+ x (* z y)) 10))
(check-sat)
(get-model)
(pop) ; remove the two assertions

; Z3 with Diff Logic Solver ...
; (error "line 9 column 22: logic only supports difference arithmetic")
; (error "line 10 column 23: logic only supports difference arithmetic")
; sat
; (error "line 15 column 22: logic does not support nonlinear arithmetic")
; (error "line 16 column 29: logic does not support nonlinear arithmetic")
; sat
; (model 
; )
