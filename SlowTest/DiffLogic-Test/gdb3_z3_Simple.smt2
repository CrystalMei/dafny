(set-option :smt.arith.solver 7) ; set diff logic solver

(declare-const x Int)
(declare-const y Int)

(push)
(assert (forall ((a Int) (b Int)) (=> (< a (- b 10)) (< a b))) ) ; sat
(assert (forall ((a Int) (b Int) (c Int)) (=> (and (< a (- b 10)) (< b c)) (< a c))) ) ; sat
(assert (forall ((a Int) (b Int)) (=> (<= 0 a) (<= 0 (+ a 1)))) ) ; sat
(assert (forall ((a Int) (b Int)) (=> (and (<= a y) (= y (- x 1))) (<= (+ a 1) x))) ) ; sat
; (assert (forall ((a Int) (b Int)) (=> (< a (+ b 10)) (< a b))) ) ; unsat
(check-sat)
; (get-model)