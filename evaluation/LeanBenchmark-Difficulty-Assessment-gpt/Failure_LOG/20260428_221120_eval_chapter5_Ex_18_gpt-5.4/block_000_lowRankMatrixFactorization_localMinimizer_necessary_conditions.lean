theorem lowRankMatrixFactorization_localMinimizer_necessary_conditions
    {m n r : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]
    [InnerProductSpace ℝ (Matrix m r ℝ × Matrix r n ℝ)]
    (p : LowRankMatrixFactorizationProblem m n r)
    (XStar : Matrix m r ℝ) (YStar : Matrix r n ℝ)
    (hloc :
      IsLocalMinimizer
        (fun Z : Matrix m r ℝ × Matrix r n ℝ =>
          ‖p.A - Z.1 * Z.2‖ ^ 2)
        (XStar, YStar)) :
    fderiv ℝ (fun X : Matrix m r ℝ => ‖p.A - X * YStar‖ ^ 2) XStar = 0 ∧
      fderiv ℝ (fun Y : Matrix r n ℝ => ‖p.A - XStar * Y‖ ^ 2) YStar = 0 ∧
      (ContDiffAt ℝ 2
          (fun Z : Matrix m r ℝ × Matrix r n ℝ =>
            ‖p.A - Z.1 * Z.2‖ ^ 2)
          (XStar, YStar) →
        ∀ d : Matrix m r ℝ × Matrix r n ℝ,
          0 ≤
            ⟪d,
              (fderiv ℝ
                (gradient
                  (fun Z : Matrix m r ℝ × Matrix r n ℝ =>
                    ‖p.A - Z.1 * Z.2‖ ^ 2))
                (XStar, YStar)) d⟫) := by
  sorry
