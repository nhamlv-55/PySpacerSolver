(set-logic HORN)
(declare-fun INV (Real Real Real Bool Bool Bool) Bool)
(assert (forall ((s0 Real)
         (s1 Real)
         (s2 Real)
         (RELU0 Real)
         (RELU1 Real)
         (RELU2 Real)
         (sp0 Real)
         (sp1 Real)
         (sp2 Real)
         (i0 Real)
         (i1 Real)
         (s_is_neg0 Bool)
         (s_is_neg1 Bool)
         (s_is_neg2 Bool)
         (s_is_neg_p0 Bool)
         (s_is_neg_p1 Bool)
         (s_is_neg_p2 Bool)
         (nd0 Real)
         (nd1 Real)
         (nd2 Real))
  (=> (and (= s0 0.0)
           (= s1 (/ 3.0 32.0))
           (= s2 (/ 3.0 32.0))
           (= s_is_neg0 false)
           (= s_is_neg1 false)
           (= s_is_neg2 false))
      (INV s0 s1 s2 s_is_neg0 s_is_neg1 s_is_neg2))))
(assert (forall ((s0 Real)
         (s1 Real)
         (s2 Real)
         (RELU0 Real)
         (RELU1 Real)
         (RELU2 Real)
         (sp0 Real)
         (sp1 Real)
         (sp2 Real)
         (i0 Real)
         (i1 Real)
         (s_is_neg0 Bool)
         (s_is_neg1 Bool)
         (s_is_neg2 Bool)
         (s_is_neg_p0 Bool)
         (s_is_neg_p1 Bool)
         (s_is_neg_p2 Bool)
         (nd0 Real)
         (nd1 Real)
         (nd2 Real))
  (let ((a!1 (+ 0.0
                (* (/ 1.0 4.0) RELU0)
                (* (/ 11.0 32.0) RELU1)
                (* (- (/ 73.0 64.0)) RELU2)
                (* (- (/ 1.0 16.0)) i0)
                (* (/ 39.0 64.0) i1)
                (/ 1.0 16.0)))
        (a!2 (+ (+ 0.0 (* (- (/ 5.0 16.0)) RELU0))
                (* (- (/ 7.0 64.0)) RELU1)
                (* (/ 59.0 64.0) RELU2)
                (* (- (/ 5.0 16.0)) i0)
                (* (/ 31.0 64.0) i1)
                (/ 1.0 32.0)))
        (a!3 (+ (+ 0.0 (* (- (/ 5.0 16.0)) RELU0))
                (* 0.0 RELU1)
                (* (/ 57.0 64.0) RELU2)
                (* (/ 3.0 32.0) i0)
                (* (/ 3.0 16.0) i1)
                (/ 1.0 64.0))))
  (let ((a!4 (and (INV s0 s1 s2 s_is_neg0 s_is_neg1 s_is_neg2)
                  (= RELU0 (ite s_is_neg0 0.0 s0))
                  (= RELU1 (ite s_is_neg1 0.0 s1))
                  (= RELU2 (ite s_is_neg2 0.0 s2))
                  (= sp0 (ite (>= a!1 0.0) a!1 nd0))
                  (= s_is_neg_p0 (< a!1 0.0))
                  (= sp1 (ite (>= a!2 0.0) a!2 nd1))
                  (= s_is_neg_p1 (< a!2 0.0))
                  (= sp2 (ite (>= a!3 0.0) a!3 nd2))
                  (= s_is_neg_p2 (< a!3 0.0))
                  (>= i0 (/ 1.0 64.0))
                  (<= i0 (/ 1.0 32.0))
                  (= i1 0.0))))
    (=> a!4 (INV sp0 sp1 sp2 s_is_neg_p0 s_is_neg_p1 s_is_neg_p2))))))
(assert (forall ((s0 Real)
         (s1 Real)
         (s2 Real)
         (RELU0 Real)
         (RELU1 Real)
         (RELU2 Real)
         (sp0 Real)
         (sp1 Real)
         (sp2 Real)
         (i0 Real)
         (i1 Real)
         (s_is_neg0 Bool)
         (s_is_neg1 Bool)
         (s_is_neg2 Bool)
         (s_is_neg_p0 Bool)
         (s_is_neg_p1 Bool)
         (s_is_neg_p2 Bool)
         (nd0 Real)
         (nd1 Real)
         (nd2 Real))
  (=> (and (INV s0 s1 s2 s_is_neg0 s_is_neg1 s_is_neg2) (or s_is_neg1)) false)))
(check-sat)