(set-option :print-success false)
(set-info :smt-lib-version 2.0)
(set-option :smt.arith.solver 3)
(set-option :AUTO_CONFIG false)
(set-option :pp.bv_literals false)
(set-option :MODEL.V2 true)
(set-option :smt.PHASE_SELECTION 0)
(set-option :smt.RESTART_STRATEGY 0)
(set-option :smt.RESTART_FACTOR |1.5|)
(set-option :smt.ARITH.RANDOM_INITIAL_VALUE true)
(set-option :smt.CASE_SPLIT 3)
(set-option :smt.DELAY_UNITS true)
(set-option :NNF.SK_HACK true)
(set-option :smt.MBQI false)
(set-option :smt.QI.EAGER_THRESHOLD 100)
(set-option :TYPE_CHECK true)
(set-option :smt.BV.REFLECT true)
(set-option :model.compact false)
(set-logic DLA)
; done setting options


(declare-fun tickleBool (Bool) Bool)
(assert (and (tickleBool true) (tickleBool false)))
(declare-fun add (Int Int) Int)
(assert (forall ((x Int) (y Int) ) (! (= (add x y) (+ x y))
 :qid |seq2Boog.1:14|
 :skolemid |0|
 :pattern ( (add x y))
)))
(declare-fun %lbl%+0 () Bool)
(declare-fun %lbl%+1 () Bool)
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun %lbl%@2 () Bool)
(declare-fun %lbl%@3 () Bool)
(declare-fun l () Int)
(declare-fun %lbl%+4 () Bool)
(declare-fun %lbl%+5 () Bool)
(push 1)
(set-info :boogie-vc-id P)
(assert (not
(let ((anon2_Else_correct  (=> (! (and %lbl%+0 true) :lblpos +0) true)))
(let ((anon2_Then_correct  (=> (! (and %lbl%+1 true) :lblpos +1) (=> (and (and (<= 0 i) (< i j)) (< j 5)) (and (! (or %lbl%@2 (<= 0 (add i j))) :lblneg @2) (=> (<= 0 (add i j)) (! (or %lbl%@3 (< (add i j) l)) :lblneg @3)))))))
(let ((anon0_correct  (=> (! (and %lbl%+4 true) :lblpos +4) (=> (and (forall ((i@@0 Int) (j@@0 Int) ) (!  (=> (and (>= i@@0 0) (>= j@@0 0)) (< (+ 0 0) (add i@@0 j@@0)))
 :qid |seq2Boog.9:21|
 :skolemid |1|
)) (forall ((i@@1 Int) (j@@1 Int) ) (!  (=> (and (< i@@1 5) (< j@@1 5)) (< (add i@@1 j@@1) (+ 5 5)))
 :qid |seq2Boog.10:21|
 :skolemid |2|
))) (and anon2_Then_correct anon2_Else_correct)))))
(let ((PreconditionGeneratedEntry_correct  (=> (! (and %lbl%+5 true) :lblpos +5) (=> (> l 10) anon0_correct))))
PreconditionGeneratedEntry_correct))))
))
(check-sat)
(pop 1)
; Valid
