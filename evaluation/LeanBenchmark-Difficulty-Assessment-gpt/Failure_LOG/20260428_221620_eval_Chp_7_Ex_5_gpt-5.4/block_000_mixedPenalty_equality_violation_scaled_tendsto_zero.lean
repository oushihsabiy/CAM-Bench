theorem mixedPenalty_equality_violation_scaled_tendsto_zero
    {n : ℕ}
    (baseProblem : ConstrainedOptimizationProblem n)
    (sigma : ℕ → ℝ)
    (sigma_pos : ∀ k, 0 < sigma k)
    (hsigma_tendsto_atTop : Tendsto sigma atTop atTop)
    (x : ℕ → (Fin n → ℝ))
    (hΩ_nonempty : Set.Nonempty baseProblem.feasibleSet)
    (hΩ_bounded : Bornology.IsBounded (baseProblem.feasibleSet))
    (hΩ_closed : IsClosed (baseProblem.feasibleSet))
    (xStar : Fin n → ℝ)
    (hxStar_feasible : baseProblem.isFeasible xStar)
    (hxStar_opt : IsMinOn baseProblem.objective (baseProblem.feasibleSet) xStar)
    (hopt_strict : ∀ k, IsMinOn
      (fun y => mixedPenaltyFunction
        baseProblem.f
        baseProblem.E
        baseProblem.I
        baseProblem.c
        y
        (sigma k)
        (sigma_pos k))
      {y | ∀ i ∈ baseProblem.I, baseProblem.c i y < 0}
      (x (k + 1))) :
    Tendsto
      (fun k => sigma k * ∑ i ∈ baseProblem.E, (baseProblem.c i (x (k + 1)))^2)
      atTop
      (𝓝 0) := by
  sorry

/- [BLOCK Chp.7 Ex.5 | 24 | thm]
Let f:ℝ^n → ℝ and cᵢ:ℝ^n → ℝ (i ∈ EcupI) be continuous functions. Consider the constrained
optimization problem min_{x∈ ℝ^n} f(x) quad s.t.quad cᵢ(x)=0,\ i∈ E, cᵢ(x)≤ 0,\ i∈ I. Denote its
feasible set by ω={x∈ ℝ^n | cᵢ(x)=0,\ i∈ E,\ cᵢ(x)≤ 0,\ i∈ I}. Assume that ω is nonempty and is a
bounded closed set, and assume that the original problem has an optimal solution x*∈ ω. For any σ>0,
define the mixed penalty function P(x,σ)=f(x)+(σ)/(2)sum_{i∈ E} cᵢ^2(x)-(1)/(σ)sum_{i∈ I}ln(-cᵢ(x)),
whose domain is dom P={x∈ ℝ^n | cᵢ(x)<0,\ i∈ I}. Let {σ_k} be a sequence of positive numbers
satisfying σ_k→ +∞, and for each k, suppose that mixed penalty minimization has an optimal solution;
denote one such optimal solution by x^{k+1}. Prove that lim_{k→∞}(1)/(σ_k)sum_{i∈
I}ln(-cᵢ(x^{k+1}))=0.
-/
