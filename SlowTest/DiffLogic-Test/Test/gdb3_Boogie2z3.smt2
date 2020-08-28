(set-option :print-success false)
(set-info :smt-lib-version 2.0)
(set-option :smt.arith.solver 7)
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
; done setting options


(declare-fun tickleBool (Bool) Bool)
(assert (and (tickleBool true) (tickleBool false)))
(declare-fun Sub (Int Int) Int)
(assert (forall ((x Int) (y Int) ) (! (= (Sub x y) (- x y))
 :qid |gdb3Boog.1:14|
 :skolemid |0|
 :pattern ( (Sub x y))
)))
(declare-fun %lbl%+0 () Bool)
(declare-fun %lbl%@1 () Bool)
(declare-fun x@@0 () Int)
(declare-fun %lbl%+2 () Bool)
(push 1)
(set-info :boogie-vc-id test)
(assert (not
(let ((anon0_correct  (=> (! (and %lbl%+0 true) :lblpos +0) (! (or %lbl%@1 (< (Sub x@@0 1) x@@0)) :lblneg @1))))
(let ((PreconditionGeneratedEntry_correct  (=> (! (and %lbl%+2 true) :lblpos +2) anon0_correct)))
PreconditionGeneratedEntry_correct))
))
(check-sat)
(get-info :reason-unknown)
(labels)
(assert %lbl%@1)
(check-sat)
(pop 1)
; Invalid