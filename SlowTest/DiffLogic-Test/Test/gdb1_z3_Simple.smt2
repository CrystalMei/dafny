(set-option :smt.arith.solver 7)

(declare-sort |T@[Int]Bool| 0)
(declare-fun a@0 () |T@[Int]Bool|)
(declare-fun |Store_[$int]$bool| (|T@[Int]Bool| Int Bool) |T@[Int]Bool|)
(declare-fun |Select_[$int]$bool| (|T@[Int]Bool| Int) Bool)
(assert (forall ( ( ?x0 |T@[Int]Bool|) ( ?x1 Int) ( ?x2 Bool)) (= (|Select_[$int]$bool| (|Store_[$int]$bool| ?x0 ?x1 ?x2) ?x1)  ?x2)))
; (assert (forall ( ( ?x0 |T@[Int]Bool|) ( ?x1 Int) ( ?y1 Int) ( ?x2 Bool)) (=>  (not (= ?x1 ?y1)) (= (|Select_[$int]$bool| (|Store_[$int]$bool| ?x0 ?x1 ?x2) ?y1) (|Select_[$int]$bool| ?x0 ?y1)))))
(declare-fun a () |T@[Int]Bool|)
(declare-fun i () Int)
(push 1)
(assert (not
    (let ((anon0_correct 
        (=> (= a@0 (|Store_[$int]$bool| a 0 true))
            (=> (= i 0) (|Select_[$int]$bool| a@0 i))) ))
    anon0_correct )
    )
)
(check-sat)
(get-info :reason-unknown)
(pop 1)