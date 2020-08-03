; (set-logic DLA)

(declare-sort T@t 0)
(assert (forall ((x T@t) ) (! true
 :qid |gdb2Boog.4:15|
 :skolemid |0|
)))
(declare-fun %lbl%+0 () Bool)
(declare-fun %lbl%@1 () Bool)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun %lbl%+2 () Bool)
(push 1)
(assert (not
    (let ((anon0_correct  
        (! (or %lbl%@1  (=> (and (= a 10) (= b 11)) (= (+ a b) 21))) :lblneg @1) ))
    anon0_correct) ))
(check-sat)
(get-info :reason-unknown)
(pop 1)
