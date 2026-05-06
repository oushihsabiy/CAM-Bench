theorem linfNormApproximationProblem_dual_form
    {m n : ℕ} (p : LinfNormApproximationProblem m n) :
    ∃ yStar : Fin m → ℝ,
      Matrix.mulVec p.Aᵀ yStar = 0 ∧
      (∑ i : Fin m, |yStar i|) ≤ (1 : ℝ) ∧
      ∀ y : Fin m → ℝ,
        Matrix.mulVec p.Aᵀ y = 0 →
        (∑ i : Fin m, |y i|) ≤ (1 : ℝ) →
        (-∑ i : Fin m, p.b i * y i) ≤ (-∑ i : Fin m, p.b i * yStar i) := by
  sorry
