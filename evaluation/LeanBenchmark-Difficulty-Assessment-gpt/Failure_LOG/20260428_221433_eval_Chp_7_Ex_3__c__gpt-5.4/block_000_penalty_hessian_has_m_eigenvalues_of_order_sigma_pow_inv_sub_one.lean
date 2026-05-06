theorem penalty_hessian_has_m_eigenvalues_of_order_sigma_pow_inv_sub_one
    (P : EqualityConstrainedOptimizationProblem)
    (it : GeneralPenaltyIteration P)
    (φ : ℝ → ℝ)
    (s : ℕ)
    (hs : 2 ≤ s)
    (hzero : HasZeroOfOrderAtZero s φ)
    (xStar : Fin P.n → ℝ)
    (hxconv : Tendsto it.x atTop (𝓝 xStar))
    (hσtendsto : Tendsto it.σ atTop atTop)
    (hσpos : ∃ N₀ : ℕ, ∀ k ≥ N₀, 0 < it.σ k)
    (hfeas : P.isFeasible xStar)
    (hlicq : LinearIndependent ℝ (fun i : Fin P.m => fderiv ℝ (P.c i) xStar))
    (lambdaStar : Fin P.m → ℝ)
    (hlagrange : fderiv ℝ P.f xStar + ∑ i : Fin P.m, lambdaStar i • fderiv ℝ (P.c i) xStar = 0)
    (hlambda_ne : ∀ i : Fin P.m, lambdaStar i ≠ 0)
    (hphi_smooth : ContDiff ℝ s φ)
    (hf_twice : ContDiff ℝ 2 P.f)
    (hc_twice : ∀ i : Fin P.m, ContDiff ℝ 2 (P.c i)) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ N : ℕ, ∀ k ≥ N,
      let penaltyFunction : (Fin P.n → ℝ) → ℝ :=
        fun x => P.f x + it.σ k * ∑ i : Fin P.m, φ (P.c i x)
      let penaltyHessian : Matrix (Fin P.n) (Fin P.n) ℝ :=
        fun i j =>
          fderiv ℝ
            (fun y => (fderiv ℝ penaltyFunction y) (Pi.single j (1 : ℝ)))
            (it.x k) (Pi.single i (1 : ℝ))
      ∃ μ : Fin P.m → ℂ,
        (∀ i : Fin P.m, μ i ∈ spectrum ℂ (penaltyHessian.map (algebraMap ℝ ℂ))) ∧
        (∀ i : Fin P.m,
          c₁ * (it.σ k) ^ (((1 : ℝ) / (s - 1 : ℝ))) ≤ ‖μ i‖ ∧
          ‖μ i‖ ≤ c₂ * (it.σ k) ^ (((1 : ℝ) / (s - 1 : ℝ)))) := by
  sorry
