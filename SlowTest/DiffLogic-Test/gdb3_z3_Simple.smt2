(set-option :smt.arith.solver 7) ; set diff logic solver
(set-option :smt.MBQI false)

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)

(push)
; equation problem
(assert (not
    (let ((anon0_correct 
        (=> (= y x) 
            (! (forall ((i Int)) (!  (=> (< i x) (< i y))) ))) ))
    anon0_correct) ))

;(assert (not
;    (let ((anon0_correct 
;        (=> (= y (+ x 1)) 
;            (! (forall ((i Int)) (!  (=> (< i x) (< (+ i 1) (+ x 1)))) ))) ))
;    anon0_correct) ))

;(assert (not
;    (let ((anon0_correct 
;        (! (forall ((i Int)) (! (=> (<= 0 i) (<= 0 (+ i 1))) ))) ))
;    anon0_correct) ))

;(assert (<= x y))
;(assert (<= y z))
;(assert (not (<= x z)))
;(assert (forall ((a Int)) true))

;(assert (<= x (+ y 1)))
;(assert (<= y z))
;(assert (not (<= x (+ z 1))))
;(assert (not (<= x z)))

;(assert (<= 0 x))
;(assert (<= 0 (+ x 1)))

;(assert (forall ((a Int) (b Int)) (=> (< a (- b 10)) (< a b))) ) ; sat
;(assert (forall ((a Int) (b Int) (c Int)) (=> (and (< a (- b 10)) (< b c)) (< a c))) ) ; sat
;(assert (forall ((a Int) (b Int)) (=> (<= 0 a) (<= 0 (+ a 1)))) ) ; sat
;(assert (forall ((a Int) (b Int)) (=> (and (<= a y) (= y (- x 1))) (<= (+ a 1) x))) ) ; sat
; (assert (forall ((a Int) (b Int)) (=> (< a (+ b 10)) (< a b))) ) ; unsat
; (assert (=> (< x (+ y 10)) (< x y)) ) ; unsat

(check-sat)
(get-model)