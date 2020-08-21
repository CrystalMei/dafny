(set-option :smt.arith.solver 1) ; set diff logic solver
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
(assert (not
    (let ((anon0_correct 
        (=> (= z (+ x 1))
            (! (forall ((i Int)) (! (ite (= i z) (<= (- i 1) x) (ite (< i z) (< (- i 1) x) (> i x) ) )) ))
        ) ))
    anon0_correct) ))
(check-sat) ; unsat
(pop)



;(assert (not
;    (let ((anon0_correct 
;        (=> (= y (- x 1))
;            (! (forall ((i Int)) (! (ite (= i x) (<= (- i 1) y) (ite (< i x) (< (- i 1) y) (>= i y) ) )) ))
;        ) ))
;    anon0_correct) ))