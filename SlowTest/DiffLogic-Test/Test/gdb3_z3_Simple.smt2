(set-option :smt.arith.solver 7) ; set diff logic solver
(set-option :smt.MBQI false)

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)


(push)
(assert (not
    (let ((anon0_correct 
        (=> (= y (+ x 1))
            (! (forall ((i Int)) (! (ite (= i x) (<= (+ i 1) y) (ite (< i x) (< (+ i 1) y) (>= i y) ) )) ))
        ) ))
    anon0_correct) ))
(check-sat) ; unsat
(pop)
(push)
(assert (not
    (let ((anon0_correct 
        (=> (and (= y (+ x 1)) (= z (+ y 1)))
            (! (forall ((i Int)) (!  (=> (< i x) (< (+ i 3) z))) ))) ))
    anon0_correct) ))
(check-sat) ; sat
(pop)
(push)
(assert (not
    (let ((anon0_correct 
        (=> (and (= y (+ x 1)) (= z (+ y 1)))
            (! (forall ((i Int)) (!  (=> (< i x) (< (+ i 2) z))) ))) ))
    anon0_correct) ))
(check-sat) ; unsat
(pop)
(push)
(assert (not
    (let ((anon0_correct 
        (=> (= y (+ x 1))
            (! (forall ((i Int)) (!  (=> (< i x) (< (+ i 1) y))) ))) ))
    anon0_correct) ))
(check-sat) ; unsat
(pop)
(push)
(assert (not
    (let ((anon0_correct 
        (=> (= y (- x 1))
            (! (forall ((i Int)) (!  (=> (< i x) (< (+ i 1) y))) ))) ))
    anon0_correct) ))
(check-sat) ; sat
(pop)
(push)
(assert (not
    (let ((anon0_correct 
        (=> (and (= y 1) (= y (- x 1)))
            (! (forall ((i Int)) (!  (=> (< i x) (< i 2))) ))) ))
    anon0_correct) ))
(check-sat) ; unsat
(pop)
(push)
(assert (not
    (let ((anon0_correct 
        (=> (= y (+ x 1))
            (! (forall ((i Int)) (!  (=> (= i x) (<= (+ i 1) y) )) )) ) ))
    anon0_correct) ))
(check-sat) ; unsat
(pop)
;(assert (ite (= y (- x 1)) (=> (= y z) (= z (- x 1))) (=> (= y (- z 1)) (< y z))) )
;(check-sat)
;(get-model)
;(pop)

; equation problem
;(assert (not
;    (let ((anon0_correct 
;        (=> (= y (+ x 1)) 
;            (! (forall ((i Int)) (!  (=> (< i x) (< (+ i 1) y))) ))) ))
;    anon0_correct) ))

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

;(check-sat)
;(get-model)