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
; done setting options


(declare-fun tickleBool (Bool) Bool)
(assert (and (tickleBool true) (tickleBool false)))
(declare-fun %lbl%+0 () Bool)
(declare-fun %lbl%@1 () Bool)
(declare-fun len () Int)
(declare-sort |T@[Int]Bool| 0)
(declare-fun |Select_[$int]$bool| (|T@[Int]Bool| Int) Bool)
(declare-fun a@3 () |T@[Int]Bool|)
(declare-fun %lbl%+2 () Bool)
(declare-fun i@0 () Int)
(declare-fun %lbl%@3 () Bool)
(declare-fun a@1 () |T@[Int]Bool|)
(declare-fun %lbl%+4 () Bool)
(declare-fun a@2 () |T@[Int]Bool|)
(declare-fun |Store_[$int]$bool| (|T@[Int]Bool| Int Bool) |T@[Int]Bool|)
(assert (forall ( ( ?x0 |T@[Int]Bool|) ( ?x1 Int) ( ?x2 Bool)) (= (|Select_[$int]$bool| (|Store_[$int]$bool| ?x0 ?x1 ?x2) ?x1)  ?x2)))
(assert (forall ( ( ?x0 |T@[Int]Bool|) ( ?x1 Int) ( ?y1 Int) ( ?x2 Bool)) (=>  (not (= ?x1 ?y1)) (= (|Select_[$int]$bool| (|Store_[$int]$bool| ?x0 ?x1 ?x2) ?y1) (|Select_[$int]$bool| ?x0 ?y1)))))
(declare-fun i@1 () Int)
(declare-fun %lbl%@5 () Bool)
(declare-fun %lbl%@6 () Bool)
(declare-fun %lbl%+7 () Bool)
(declare-fun %lbl%+8 () Bool)
(declare-fun a@0 () |T@[Int]Bool|)
(declare-fun a () |T@[Int]Bool|)
(declare-fun %lbl%@9 () Bool)
(declare-fun %lbl%@10 () Bool)
(declare-fun %lbl%+11 () Bool)
(push 1)
(set-info :boogie-vc-id S)
(assert (not
(let ((GeneratedUnifiedExit_correct  (=> (! (and %lbl%+0 true) :lblpos +0) (! (or %lbl%@1 (forall ((j Int) ) (!  (=> (and (<= 0 j) (< j len)) (|Select_[$int]$bool| a@3 j))
 :qid |seqBoogi.3:19|
 :skolemid |0|
))) :lblneg @1))))
(let ((anon3_LoopDone_correct  (=> (! (and %lbl%+2 true) :lblpos +2) (=> (<= len i@0) (and (! (or %lbl%@3 (forall ((j@@0 Int) ) (!  (=> (and (<= 0 j@@0) (< j@@0 len)) (|Select_[$int]$bool| a@1 j@@0))
 :qid |seqBoogi.17:20|
 :skolemid |2|
))) :lblneg @3) (=> (forall ((j@@1 Int) ) (!  (=> (and (<= 0 j@@1) (< j@@1 len)) (|Select_[$int]$bool| a@1 j@@1))
 :qid |seqBoogi.17:20|
 :skolemid |2|
)) (=> (= a@3 a@1) GeneratedUnifiedExit_correct)))))))
(let ((anon3_LoopBody_correct  (=> (! (and %lbl%+4 true) :lblpos +4) (=> (< i@0 len) (=> (and (= a@2 (|Store_[$int]$bool| a@1 i@0 true)) (= i@1 (+ i@0 1))) (and (! (or %lbl%@5  (and (<= 0 i@1) (<= i@1 len))) :lblneg @5) (=> (and (<= 0 i@1) (<= i@1 len)) (! (or %lbl%@6 (forall ((j@@2 Int) ) (!  (=> (and (<= 0 j@@2) (< j@@2 i@1)) (|Select_[$int]$bool| a@2 j@@2))
 :qid |seqBoogi.12:27|
 :skolemid |1|
))) :lblneg @6))))))))
(let ((anon3_LoopHead_correct  (=> (! (and %lbl%+7 true) :lblpos +7) (=> (<= 0 i@0) (=> (and (and (<= 0 i@0) (<= i@0 len)) (forall ((j@@3 Int) ) (!  (=> (and (<= 0 j@@3) (< j@@3 i@0)) (|Select_[$int]$bool| a@1 j@@3))
 :qid |seqBoogi.12:27|
 :skolemid |1|
))) (and anon3_LoopDone_correct anon3_LoopBody_correct))))))
(let ((anon0_correct  (=> (! (and %lbl%+8 true) :lblpos +8) (=> (= a@0 (|Store_[$int]$bool| a 0 true)) (and (! (or %lbl%@9  (and (<= 0 0) (<= 0 len))) :lblneg @9) (=> (and (<= 0 0) (<= 0 len)) (and (! (or %lbl%@10 (forall ((j@@4 Int) ) (!  (=> (and (<= 0 j@@4) (< j@@4 0)) (|Select_[$int]$bool| a@0 j@@4))
 :qid |seqBoogi.12:27|
 :skolemid |1|
))) :lblneg @10) (=> (forall ((j@@5 Int) ) (!  (=> (and (<= 0 j@@5) (< j@@5 0)) (|Select_[$int]$bool| a@0 j@@5))
 :qid |seqBoogi.12:27|
 :skolemid |1|
)) anon3_LoopHead_correct))))))))
(let ((PreconditionGeneratedEntry_correct  (=> (! (and %lbl%+11 true) :lblpos +11) (=> (< 0 len) anon0_correct))))
PreconditionGeneratedEntry_correct))))))
))
(check-sat)
(pop 1)
; Valid
