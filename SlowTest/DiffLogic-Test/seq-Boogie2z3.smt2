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
(declare-sort |T@[Int]Int| 0)
(declare-fun |Select_[$int]$int| (|T@[Int]Int| Int) Int)
(declare-fun out@3 () |T@[Int]Int|)
(declare-fun in () |T@[Int]Int|)
(declare-fun %lbl%+2 () Bool)
(declare-fun i@2 () Int)
(declare-fun out@1 () |T@[Int]Int|)
(declare-fun %lbl%+3 () Bool)
(declare-fun i@3 () Int)
(declare-fun %lbl%@4 () Bool)
(declare-fun %lbl%@5 () Bool)
(declare-fun %lbl%+6 () Bool)
(declare-fun %lbl%+7 () Bool)
(declare-fun i@0 () Int)
(declare-fun %lbl%@8 () Bool)
(declare-fun %lbl%@9 () Bool)
(declare-fun %lbl%+10 () Bool)
(declare-fun out@2 () |T@[Int]Int|)
(declare-fun |Store_[$int]$int| (|T@[Int]Int| Int Int) |T@[Int]Int|)
(assert (forall ( ( ?x0 |T@[Int]Int|) ( ?x1 Int) ( ?x2 Int)) (= (|Select_[$int]$int| (|Store_[$int]$int| ?x0 ?x1 ?x2) ?x1)  ?x2)))
(assert (forall ( ( ?x0 |T@[Int]Int|) ( ?x1 Int) ( ?y1 Int) ( ?x2 Int)) (=>  (not (= ?x1 ?y1)) (= (|Select_[$int]$int| (|Store_[$int]$int| ?x0 ?x1 ?x2) ?y1) (|Select_[$int]$int| ?x0 ?y1)))))
(declare-fun i@1 () Int)
(declare-fun %lbl%@11 () Bool)
(declare-fun %lbl%@12 () Bool)
(declare-fun %lbl%+13 () Bool)
(declare-fun %lbl%+14 () Bool)
(declare-fun out@0 () |T@[Int]Int|)
(declare-fun out () |T@[Int]Int|)
(declare-fun %lbl%@15 () Bool)
(declare-fun %lbl%@16 () Bool)
(declare-fun %lbl%+17 () Bool)
(push 1)
(set-info :boogie-vc-id S2)
(assert (not
(let ((GeneratedUnifiedExit_correct  (=> (! (and %lbl%+0 true) :lblpos +0) (! (or %lbl%@1 (forall ((j Int) ) (!  (=> (and (<= 0 j) (< j len)) (= (|Select_[$int]$int| out@3 j) (|Select_[$int]$int| in j)))
 :qid |seqBoogi.24:19|
 :skolemid |1|
))) :lblneg @1))))
(let ((anon5_LoopDone_correct  (=> (! (and %lbl%+2 true) :lblpos +2) (=> (and (<= len i@2) (= out@3 out@1)) GeneratedUnifiedExit_correct))))
(let ((anon5_LoopBody_correct  (=> (! (and %lbl%+3 true) :lblpos +3) (=> (and (< i@2 len) (= i@3 (+ i@2 1))) (and (! (or %lbl%@4  (and (<= 0 i@3) (<= i@3 len))) :lblneg @4) (=> (and (<= 0 i@3) (<= i@3 len)) (! (or %lbl%@5 (forall ((j@@0 Int) ) (!  (=> (and (<= 0 j@@0) (< j@@0 i@3)) (= (|Select_[$int]$int| out@1 j@@0) (|Select_[$int]$int| in j@@0)))
 :qid |seqBoogi.44:25|
 :skolemid |4|
))) :lblneg @5)))))))
(let ((anon5_LoopHead_correct  (=> (! (and %lbl%+6 true) :lblpos +6) (=> (<= 0 i@2) (=> (and (and (<= 0 i@2) (<= i@2 len)) (forall ((j@@1 Int) ) (!  (=> (and (<= 0 j@@1) (< j@@1 i@2)) (= (|Select_[$int]$int| out@1 j@@1) (|Select_[$int]$int| in j@@1)))
 :qid |seqBoogi.44:25|
 :skolemid |4|
))) (and anon5_LoopDone_correct anon5_LoopBody_correct))))))
(let ((anon4_LoopDone_correct  (=> (! (and %lbl%+7 true) :lblpos +7) (=> (<= len i@0) (and (! (or %lbl%@8  (and (<= 0 0) (<= 0 len))) :lblneg @8) (=> (and (<= 0 0) (<= 0 len)) (and (! (or %lbl%@9 (forall ((j@@2 Int) ) (!  (=> (and (<= 0 j@@2) (< j@@2 0)) (= (|Select_[$int]$int| out@1 j@@2) (|Select_[$int]$int| in j@@2)))
 :qid |seqBoogi.44:25|
 :skolemid |4|
))) :lblneg @9) (=> (forall ((j@@3 Int) ) (!  (=> (and (<= 0 j@@3) (< j@@3 0)) (= (|Select_[$int]$int| out@1 j@@3) (|Select_[$int]$int| in j@@3)))
 :qid |seqBoogi.44:25|
 :skolemid |4|
)) anon5_LoopHead_correct))))))))
(let ((anon4_LoopBody_correct  (=> (! (and %lbl%+10 true) :lblpos +10) (=> (and (and (< i@0 len) (= out@2 (|Store_[$int]$int| out@1 i@0 (|Select_[$int]$int| in i@0)))) (and (forall ((j@@4 Int) ) (!  (=> (= i@0 j@@4) (= (|Select_[$int]$int| out@2 j@@4) (|Select_[$int]$int| in j@@4)))
 :qid |seqBoogi.37:24|
 :skolemid |3|
)) (= i@1 (+ i@0 1)))) (and (! (or %lbl%@11  (and (<= 0 i@1) (<= i@1 len))) :lblneg @11) (=> (and (<= 0 i@1) (<= i@1 len)) (! (or %lbl%@12  (and (= (|Select_[$int]$int| out@2 0) 0) (forall ((j@@5 Int) ) (!  (=> (and (<= 0 j@@5) (< j@@5 i@1)) (= (|Select_[$int]$int| out@2 j@@5) (|Select_[$int]$int| in j@@5)))
 :qid |seqBoogi.34:40|
 :skolemid |2|
)))) :lblneg @12)))))))
(let ((anon4_LoopHead_correct  (=> (! (and %lbl%+13 true) :lblpos +13) (=> (<= 0 i@0) (=> (and (and (<= 0 i@0) (<= i@0 len)) (and (= (|Select_[$int]$int| out@1 0) 0) (forall ((j@@6 Int) ) (!  (=> (and (<= 0 j@@6) (< j@@6 i@0)) (= (|Select_[$int]$int| out@1 j@@6) (|Select_[$int]$int| in j@@6)))
 :qid |seqBoogi.34:40|
 :skolemid |2|
)))) (and anon4_LoopDone_correct anon4_LoopBody_correct))))))
(let ((anon0_correct  (=> (! (and %lbl%+14 true) :lblpos +14) (=> (= out@0 (|Store_[$int]$int| out 0 0)) (and (! (or %lbl%@15  (and (<= 0 0) (<= 0 len))) :lblneg @15) (=> (and (<= 0 0) (<= 0 len)) (and (! (or %lbl%@16  (and (= (|Select_[$int]$int| out@0 0) 0) (forall ((j@@7 Int) ) (!  (=> (and (<= 0 j@@7) (< j@@7 0)) (= (|Select_[$int]$int| out@0 j@@7) (|Select_[$int]$int| in j@@7)))
 :qid |seqBoogi.34:40|
 :skolemid |2|
)))) :lblneg @16) (=> (and (= (|Select_[$int]$int| out@0 0) 0) (forall ((j@@8 Int) ) (!  (=> (and (<= 0 j@@8) (< j@@8 0)) (= (|Select_[$int]$int| out@0 j@@8) (|Select_[$int]$int| in j@@8)))
 :qid |seqBoogi.34:40|
 :skolemid |2|
))) anon4_LoopHead_correct))))))))
(let ((PreconditionGeneratedEntry_correct  (=> (! (and %lbl%+17 true) :lblpos +17) (=> (and (and (= (|Select_[$int]$int| in 0) 0) (forall ((i Int) ) (!  (=> (and (<= 0 i) (< i (- len 1))) (= (|Select_[$int]$int| in (+ i 1)) (+ (|Select_[$int]$int| in i) 1)))
 :qid |seqBoogi.21:34|
 :skolemid |0|
))) (< 0 len)) anon0_correct))))
PreconditionGeneratedEntry_correct)))))))))
))
(check-sat)
(pop 1)
; Valid
