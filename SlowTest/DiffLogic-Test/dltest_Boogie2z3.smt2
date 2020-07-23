(set-option :print-success false)
(set-info :smt-lib-version 2.0)
(set-option :smt.arith.solver 1)
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
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun %lbl%@2 () Bool)
(declare-fun %lbl%+3 () Bool)
(push 1)
(set-info :boogie-vc-id P1)
(assert (not
(let ((anon0_correct  (=> (! (and %lbl%+0 true) :lblpos +0) (and (! (or %lbl%@1  (=> (< x y) (< (* 2 x) (* 2 y)))) :lblneg @1) (=> (=> (< x y) (< (* 2 x) (* 2 y))) (! (or %lbl%@2  (=> (<= (* 2 x) (* 2 y)) (<= (* 3 x) (* 3 y)))) :lblneg @2))))))
(let ((PreconditionGeneratedEntry_correct  (=> (! (and %lbl%+3 true) :lblpos +3) anon0_correct)))
PreconditionGeneratedEntry_correct))
))
(check-sat)
(pop 1)
; Valid
(reset)
(set-option :print-success false)
(set-info :smt-lib-version 2.0)
(set-option :smt.arith.solver 1)
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
; Valid

(declare-fun %lbl%+0 () Bool)
(declare-fun %lbl%@1 () Bool)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun %lbl%+2 () Bool)
(push 1)
(set-info :boogie-vc-id P2)
(assert (not
(let ((anon0_correct  (=> (! (and %lbl%+0 true) :lblpos +0) (! (or %lbl%@1 (= (* x y) (* y x))) :lblneg @1))))
(let ((PreconditionGeneratedEntry_correct  (=> (! (and %lbl%+2 true) :lblpos +2) anon0_correct)))
PreconditionGeneratedEntry_correct))
))
(check-sat)
(pop 1)
; Valid
(reset)
(set-option :print-success false)
(set-info :smt-lib-version 2.0)
(set-option :smt.arith.solver 1)
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
; Valid

(declare-fun %lbl%+0 () Bool)
(declare-fun %lbl%@1 () Bool)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun %lbl%+2 () Bool)
(push 1)
(set-info :boogie-vc-id P3)
(assert (not
(let ((anon0_correct  (=> (! (and %lbl%+0 true) :lblpos +0) (=> (forall ((i Int) (j Int) ) (!  (=> (and (< 0 (* i j)) (< (* i j) 10)) (and (< i 10) (< j 10)))
 :qid |dltestBo.25:20|
 :skolemid |0|
)) (! (or %lbl%@1  (=> (and (< 0 (* x y)) (< (* x y) 10)) (< x 10))) :lblneg @1)))))
(let ((PreconditionGeneratedEntry_correct  (=> (! (and %lbl%+2 true) :lblpos +2) anon0_correct)))
PreconditionGeneratedEntry_correct))
))
(check-sat)
(pop 1)
; Valid
(reset)
(set-option :print-success false)
(set-info :smt-lib-version 2.0)
(set-option :smt.arith.solver 1)
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
; Valid

(declare-fun %lbl%+0 () Bool)
(declare-fun %lbl%@1 () Bool)
(declare-fun y () Int)
(declare-fun x () Int)
(declare-fun %lbl%+2 () Bool)
(push 1)
(set-info :boogie-vc-id P4)
(assert (not
(let ((anon0_correct  (=> (! (and %lbl%+0 true) :lblpos +0) (! (or %lbl%@1  (=> (and (>= y 0) (> (- x y) 0)) (> x 0))) :lblneg @1))))
(let ((PreconditionGeneratedEntry_correct  (=> (! (and %lbl%+2 true) :lblpos +2) anon0_correct)))
PreconditionGeneratedEntry_correct))
))
(check-sat)
(pop 1)
; Valid
(reset)
(set-option :print-success false)
(set-info :smt-lib-version 2.0)
(set-option :smt.arith.solver 1)
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
; Valid

(declare-fun %lbl%+0 () Bool)
(declare-fun %lbl%@1 () Bool)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun %lbl%+2 () Bool)
(push 1)
(set-info :boogie-vc-id P5)
(assert (not
(let ((anon0_correct  (=> (! (and %lbl%+0 true) :lblpos +0) (=> (forall ((i1 Int) (i2 Int) ) (!  (=> (and (> (+ i1 i2) 10) (> i2 0)) (> (+ (+ i1 i2) i2) 10))
 :qid |dltestBo.46:20|
 :skolemid |1|
 :pattern ( (+ i1 i2))
)) (! (or %lbl%@1  (=> (and (> (+ x y) 10) (> y 0)) (> (+ (+ x y) y) 9))) :lblneg @1)))))
(let ((PreconditionGeneratedEntry_correct  (=> (! (and %lbl%+2 true) :lblpos +2) anon0_correct)))
PreconditionGeneratedEntry_correct))
))
(check-sat)
(pop 1)
; Valid
(reset)
(set-option :print-success false)
(set-info :smt-lib-version 2.0)
(set-option :smt.arith.solver 1)
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
; Valid

(declare-fun %lbl%+0 () Bool)
(declare-fun %lbl%@1 () Bool)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun %lbl%@2 () Bool)
(declare-fun %lbl%@3 () Bool)
(declare-fun %lbl%@4 () Bool)
(declare-fun %lbl%@5 () Bool)
(declare-fun %lbl%@6 () Bool)
(declare-fun %lbl%+7 () Bool)
(push 1)
(set-info :boogie-vc-id P6)
(assert (not
(let ((anon0_correct  (=> (! (and %lbl%+0 true) :lblpos +0) (and (! (or %lbl%@1  (=> (<= (* 2 x) (* 2 y)) (<= (* 3 x) (* 3 y)))) :lblneg @1) (=> (=> (<= (* 2 x) (* 2 y)) (<= (* 3 x) (* 3 y))) (and (! (or %lbl%@2 (forall ((i Int) (j Int) ) (!  (=> (<= 0 j) (<= i (+ i j)))
 :qid |dltestBo.60:20|
 :skolemid |2|
 :pattern ( (+ i j))
))) :lblneg @2) (=> (forall ((i@@0 Int) (j@@0 Int) ) (!  (=> (<= 0 j@@0) (<= i@@0 (+ i@@0 j@@0)))
 :qid |dltestBo.60:20|
 :skolemid |2|
 :pattern ( (+ i@@0 j@@0))
)) (and (! (or %lbl%@3  (=> (<= 0 y) (<= (* 3 y) (* 4 y)))) :lblneg @3) (=> (=> (<= 0 y) (<= (* 3 y) (* 4 y))) (and (! (or %lbl%@4  (=> (and (<= (* 3 x) (* 3 y)) (<= (* 3 y) (* 4 y))) (<= (* 3 x) (* 4 y)))) :lblneg @4) (=> (=> (and (<= (* 3 x) (* 3 y)) (<= (* 3 y) (* 4 y))) (<= (* 3 x) (* 4 y))) (and (! (or %lbl%@5  (=> (and (<= (* 3 x) (* 3 y)) (<= 0 y)) (<= (* 3 x) (* 4 y)))) :lblneg @5) (=> (=> (and (<= (* 3 x) (* 3 y)) (<= 0 y)) (<= (* 3 x) (* 4 y))) (! (or %lbl%@6  (=> (and (and (<= 0 x) (<= 0 y)) (<= (* 2 x) (* 2 y))) (<= (* 3 x) (* 4 y)))) :lblneg @6))))))))))))))
(let ((PreconditionGeneratedEntry_correct  (=> (! (and %lbl%+7 true) :lblpos +7) anon0_correct)))
PreconditionGeneratedEntry_correct))
))
(check-sat)
(get-info :reason-unknown)
(labels)
(assert %lbl%@4)
(check-sat)
(pop 1)
; Invalid
(reset)
(set-option :print-success false)
(set-info :smt-lib-version 2.0)
(set-option :smt.arith.solver 1)
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
; Invalid

(declare-fun %lbl%+0 () Bool)
(declare-fun %lbl%@1 () Bool)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun %lbl%+2 () Bool)
(push 1)
(set-info :boogie-vc-id P7)
(assert (not
(let ((anon0_correct  (=> (! (and %lbl%+0 true) :lblpos +0) (! (or %lbl%@1  (=> (and (<= 0 (* x y)) (<= (+ (* x y) 10) z)) (<= 0 z))) :lblneg @1))))
(let ((PreconditionGeneratedEntry_correct  (=> (! (and %lbl%+2 true) :lblpos +2) anon0_correct)))
PreconditionGeneratedEntry_correct))
))
(check-sat)
(pop 1)
; Valid
