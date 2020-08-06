(set-option :smt.arith.solver 7) ; set diff logic solver

(push)
; (assert (forall ((a Int) (b Int)) (=> (< a (- b 10)) (< a b))) )
; (assert (forall ((a Int) (b Int) (c Int)) (=> (and (< a (- b 10)) (< b c)) (< a c))) )
(assert (forall ((a Int) (b Int)) (=> (<= 0 a) (<= 0 (+ a 1)))) )
; (assert (forall ((a Int) (b Int)) (=> (< a (+ b 10)) (< a b))) )
(check-sat)
; (get-model)