; (set-option :produce-proofs true)
; (set-option :smt.arith.solver 3) ; set diff logic solver
(set-logic DLA) 

(declare-const a Int)
(declare-const b Int)

;(push)
(assert (=> (and (= a 10) (= b 11)) (= (+ a b) 21)))

(check-sat)
;(get-model)
; (check-sat-using qflia)
; (get-model)
; (pop) ; remove the two assertions

; (assert (=> (and (< 0 (* x y)) (< (* x y) 10)) (< x 10)))
; (push)
; (assert (< 0 x))
; (assert (< 0 y))
; (assert (< (+ x y) (* x y)))
; (assert (=> (< (* x y) (* 2 y)) (> (* 3 x) (* 3 y))))
; (assert (< x y))
; (assert (> (+ x y) 10)); (smt.diff_logic: non-diff logic expression (+ x y))
;(assert (< (* x y) 10))
;(assert (> (+ x y) 10))
;(push)
;(declare-const z Int)
;(assert (< (* x y) 10)); (smt.diff_logic: non-diff logic expression (* x y))
;(assert (< (+ x (* z y)) 10))
;(check-sat)
;(get-model)
;(pop) ; remove the two assertions

