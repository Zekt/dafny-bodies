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
; done setting options


(declare-fun %lbl%+0 () Bool)
(declare-fun %lbl%@1 () Bool)
(declare-fun n () Int)
(declare-fun r@2 () Int)
(declare-fun %lbl%+2 () Bool)
(declare-fun r@1 () Int)
(declare-fun %lbl%+3 () Bool)
(declare-fun r@0 () Int)
(declare-fun %lbl%+4 () Bool)
(set-info :boogie-vc-id F)
(assert (not
(let ((GeneratedUnifiedExit_correct  (=> (! (and %lbl%+0 true) :lblpos +0) (! (or %lbl%@1  (=> (< 100 n) (> r@2 90))) :lblneg @1))))
(let ((anon3_Else_correct  (=> (! (and %lbl%+2 true) :lblpos +2) (=> (<= n 100) (=> (and (= r@1 (+ n 100)) (= r@2 r@1)) GeneratedUnifiedExit_correct)))))
(let ((anon3_Then_correct  (=> (! (and %lbl%+3 true) :lblpos +3) (=> (< 100 n) (=> (and (= r@0 (- n 10)) (= r@2 r@0)) GeneratedUnifiedExit_correct)))))
(let ((anon0_correct  (=> (! (and %lbl%+4 true) :lblpos +4) (and anon3_Then_correct anon3_Else_correct))))
anon0_correct))))
))
(check-sat)
; Valid
