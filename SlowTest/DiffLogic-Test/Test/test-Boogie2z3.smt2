(set-option :print-success false)
(set-info :smt-lib-version 2.0)
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
(declare-fun %lbl%+0 () Bool)
(declare-fun %lbl%@1 () Bool)
(declare-fun |a#0| () Int)
(declare-fun |b#0| () Int)
(declare-fun %lbl%+2 () Bool)
(declare-fun %lbl%+3 () Bool)
(declare-fun %lbl%+4 () Bool)
(declare-fun %lbl%+5 () Bool)
(declare-fun %lbl%+6 () Bool)
(push 1)
(set-info :boogie-vc-id Impl$$_module.__default.myAdd)
(assert (not
(let ((anon4_correct  (=> (! (and %lbl%+0 true) :lblpos +0) (! (or %lbl%@1  (=> (and (= |a#0| 10) (= |b#0| 11)) (= (+ |a#0| |b#0|) 21))) :lblneg @1))))
(let ((anon6_Else_correct  (=> (! (and %lbl%+2 true) :lblpos +2) (=> (not (and (= |a#0| 10) (= |b#0| 11))) anon4_correct))))
(let ((anon6_Then_correct  (=> (! (and %lbl%+3 true) :lblpos +3) (=> (and (= |a#0| 10) (= |b#0| 11)) anon4_correct))))
(let ((anon5_Else_correct  (=> (! (and %lbl%+4 true) :lblpos +4) (=> (not (= |a#0| 10)) (and anon6_Then_correct anon6_Else_correct)))))
(let ((anon5_Then_correct  (=> (! (and %lbl%+5 true) :lblpos +5) (=> (= |a#0| 10) (and anon6_Then_correct anon6_Else_correct)))))
(let ((anon0_correct  (=> (! (and %lbl%+6 true) :lblpos +6) (and anon5_Then_correct anon5_Else_correct))))
anon0_correct))))))
))
(check-sat)
(pop 1)
; Valid
