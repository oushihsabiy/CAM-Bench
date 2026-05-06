theorem exists_stepSize_satisfying_wolfe_conditions
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x p : EuclideanSpace ℝ (Fin n)) (c₁ c₂ : ℝ)
    (hf : Differentiable ℝ f)
    (hdesc : IsDescentDirection f x p)
    (hbounded : BddBelow (Set.range fun α : Set.Ici (0 : ℝ) => f (x + (α : ℝ) • p)))
    (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    ∃ α : ℝ, SatisfiesWolfeConditions f x p c₁ c₂ α := by
  sorry
