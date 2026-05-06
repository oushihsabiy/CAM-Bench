theorem penalty_minimizer_yields_dual_lower_bound
    {m : ℕ} (P : ConvexInequalityConstrainedProblem m) (alpha : ℝ) (xtilde : Fin P.n → ℝ)
    (halpha : 0 < alpha)
    (hxtilde_min :
      IsLeast (Set.range (fun x : Fin P.n → ℝ => P.f0 x + alpha * ∑ i, max 0 (P.f i x) ^ (2 : ℕ)))
        (P.f0 xtilde + alpha * ∑ i, max 0 (P.f i xtilde) ^ (2 : ℕ))) :
    ConvexOn ℝ Set.univ
      (fun x => P.f0 x + alpha * ∑ i, max 0 (P.f i x) ^ (2 : ℕ)) ∧
    (∀ i, 0 ≤ (2 * alpha * max 0 (P.f i xtilde))) ∧
    IsLeast
      (Set.range
        (fun x : Fin P.n → ℝ =>
          (Lagrangian P.f0 P.f x (fun i => 2 * alpha * max 0 (P.f i xtilde)) : ℝ)))
      (Lagrangian P.f0 P.f xtilde (fun i => 2 * alpha * max 0 (P.f i xtilde))) ∧
    -- g(λ̃) = L(x̃,λ̃) = f₀(x̃) + 2α∑ max(0,fᵢ(x̃))²
    (P.dualFunction (fun i => 2 * alpha * max 0 (P.f i xtilde)) =
      (Lagrangian P.f0 P.f xtilde (fun i => 2 * alpha * max 0 (P.f i xtilde)) : EReal)) ∧
    ((Lagrangian P.f0 P.f xtilde (fun i => 2 * alpha * max 0 (P.f i xtilde)) : EReal) =
      (P.f0 xtilde + 2 * alpha * ∑ i, max 0 (P.f i xtilde) ^ (2 : ℕ) : EReal)) ∧
    -- p★ ≥ g(λ̃) = f₀(x̃) + 2α∑ max(0,fᵢ(x̃))²
    P.objectiveValue ≥ P.dualFunction (fun i => 2 * alpha * max 0 (P.f i xtilde)) ∧
    P.objectiveValue ≥
      (P.f0 xtilde + 2 * alpha * ∑ i, max 0 (P.f i xtilde) ^ (2 : ℕ) : EReal) := by
  sorry
