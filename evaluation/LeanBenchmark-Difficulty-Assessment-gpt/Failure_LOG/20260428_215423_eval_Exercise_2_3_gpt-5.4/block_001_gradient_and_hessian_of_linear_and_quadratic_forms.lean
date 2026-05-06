theorem gradient_and_hessian_of_linear_and_quadratic_forms
    {n : ℕ} (hn : 1 ≤ n)
    (a : EuclideanSpace ℝ (Fin n)) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.transpose = A) :
    ∀ x : EuclideanSpace ℝ (Fin n),
      gradient (fun y => ⟪a, y⟫) x = a ∧
      hessian (fun y => ⟪a, y⟫) x = (0 : Matrix (Fin n) (Fin n) ℝ) ∧
      gradient (fun y => ⟪y, (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) y⟫) x =
        (2 : ℝ) • ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) x) ∧
      hessian (fun y => ⟪y, (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) y⟫) x =
        ((2 : ℝ) • A : Matrix (Fin n) (Fin n) ℝ) := by
  sorry
