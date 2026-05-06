theorem robust_least_squares_equivalent_to_socp
    {m n : ℕ} (Abar : Matrix (Fin m) (Fin n) ℝ) (R : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hR_nonneg : ∀ i : Fin m, ∀ j : Fin n, 0 ≤ R i j) :
    -- Optimal value of robust LS = optimal value of the SOCP (using the section's SOCP type)
    sInf (Set.range fun x : Fin n → ℝ =>
      RobustLeastSquaresOptimizationProblem.objective
        { data := { U := {A | ∀ i j, |A i j - Abar i j| ≤ R i j}, b := b } } x) =
    sInf {t : ℝ | ∃ p : RobustLeastSquaresSOCP m n,
      p.Abar = Abar ∧ p.R = R ∧ p.b = b ∧ p.feasible ∧ t = p.objective} := by
  have hEq :
      (Set.range fun x : Fin n → ℝ =>
        RobustLeastSquaresOptimizationProblem.objective
          { data := { U := {A | ∀ i j, |A i j - Abar i j| ≤ R i j}, b := b } } x) =
      {t : ℝ | ∃ p : RobustLeastSquaresSOCP m n,
        p.Abar = Abar ∧ p.R = R ∧ p.b = b ∧ p.feasible ∧ t = p.objective} := by
    ext t
    constructor
    · intro ht
      rcases ht with ⟨x, hx⟩
      subst hx
      refine ⟨{ Abar := Abar, R := R, b := b, x := x, u := 0, v := 0, t := RobustLeastSquaresOptimizationProblem.objective
        { data := { U := {A | ∀ i j, |A i j - Abar i j| ≤ R i j}, b := b } } x }, rfl, rfl, rfl, ?_, rfl⟩
      simpa [RobustLeastSquaresSOCP.feasible] using hR_nonneg
    · intro ht
      rcases ht with ⟨p, hpA, hpR, hpb, hpfeas, ht⟩
      subst hpA
      subst hpR
      subst hpb
      refine ⟨p.x, ?_⟩
      simpa [ht]
  rw [hEq]