theorem multivariateNormalDensity_exponentialFamily
    (n : ℕ)
    (mu z : Fin n → ℝ)
    (Sigma : Matrix (Fin n) (Fin n) ℝ)
    (hSigma_posDef : Sigma.PosDef)
    (x : Fin n → ℝ)
    (Y : Matrix (Fin n) (Fin n) ℝ)
    (hY : Y = Sigma⁻¹)
    (hx : x = Y.mulVec mu) :
    multivariateNormalDensity n mu z Sigma =
      (Real.sqrt (Matrix.det Y) / (2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) *
        Real.exp
          ((dotProduct x z) +
            Matrix.trace (Y * Matrix.of fun i j => (-(1 : ℝ) / 2) * z i * z j) -
            (1 / 2 : ℝ) * dotProduct x (Y⁻¹.mulVec x)) := by
  sorry

/- [BLOCK Exercise 6.3-(c) | 18 | thm]
Let n ∈ ℕ. For μ ∈ ℝ^n and symmetric positive definite σ ∈ S^n, define x = σ^{-1}μ ∈ ℝ^n and Y =
σ^{-1} ∈ S^n. Equivalently, with c₁(z)=z and C₂(z)=-frac12 zzᵀ ∈ S^n, prove that
θᵀ c(z)=xᵀ c₁(z)+trbig(YC_2(z)big).
-/

-- This is the natural-parameter pairing for the multivariate normal exponential family:
-- θᵀ c(z) = xᵀ c₁(z) + tr(Y C₂(z)), where c₁(z) = z, C₂(z) = -1/2 zzᵀ
