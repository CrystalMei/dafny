(echo "Z3 with Diff Logic Solver ...")
(set-option :smt.arith.solver 1)

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(push)
(assert (< (+ x y) 10)); (smt.diff_logic: non-diff logic expression (+ x y))
(assert (< (+ x (* 2 y)) 10))
(check-sat)
(pop) ; remove the two assertions
(push) 
(assert (< (+ (* 3 x) y) 10)) ; (smt.diff_logic: non-diff logic expression (+ (* 3 x) y))
(assert (< (+ (* 2 x) (* 2 y)) 21))
(check-sat)

(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(define-fun conjecture () Bool
	(=> (and (=> p q) (=> q r))
		(=> p r)))
(assert (not conjecture))
(check-sat)

(declare-const a Bool)
(declare-const b Bool)
(define-fun demorgan () Bool
    (= (and a b) (not (or (not a) (not b)))))
(assert (not demorgan))
(check-sat)