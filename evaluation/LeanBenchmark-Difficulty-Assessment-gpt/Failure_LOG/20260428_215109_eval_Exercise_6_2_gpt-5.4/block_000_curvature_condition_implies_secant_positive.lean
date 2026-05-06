theorem curvature_condition_implies_secant_positive {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (x_k p_k : Fin n → ℝ) (α_k c₂ : ℝ)
    (hpk : p_k ≠ 0) (hα : 0 < α_k)
    (hdesc : IsDescentDirectionAt f x_k p_k)
    (hfdx : DifferentiableAt ℝ f x_k)
    (hfd : DifferentiableAt ℝ f (x_k + α_k • p_k))
    (hc₂ : 0 < c₂ ∧ c₂ < 1)
    (hwolfe : |fderiv ℝ f (x_k + α_k • p_k) p_k| ≤ c₂ * |fderiv ℝ f x_k p_k|) :
    let s_k := α_k • p_k
    let y_k : Fin n → ℝ := fun i =>
      fderiv ℝ f (x_k + s_k) (fun j : Fin n => if j = i then (1 : ℝ) else 0) -
      fderiv ℝ f x_k (fun j : Fin n => if j = i then (1 : ℝ) else 0)
    fderiv ℝ f (x_k + s_k) s_k - fderiv ℝ f x_k s_k > 0 := by
  sorry
