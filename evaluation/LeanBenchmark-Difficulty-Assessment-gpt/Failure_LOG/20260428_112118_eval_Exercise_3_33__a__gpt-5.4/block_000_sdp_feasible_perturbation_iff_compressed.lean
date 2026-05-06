theorem sdp_feasible_perturbation_iff_compressed
    {n m r : ℕ}
    (p : SemidefiniteProgram n m)
    (Xhat V : Matrix (Fin n) (Fin n) ℝ)
    (Q₁ : Matrix (Fin n) (Fin r) ℝ)
    (Q₂ : Matrix (Fin n) (Fin (n - r)) ℝ)
    (Λ₁ : Matrix (Fin r) (Fin r) ℝ)
    (hV_symm : V.IsSymm)
    (hQ₁_orthonormal : Q₁.transpose * Q₁ = 1)
    (hQ₂_orthonormal : Q₂.transpose * Q₂ = 1)
    (hQ₁Q₂_orthogonal : Q₁.transpose * Q₂ = 0)
    (hQ₂Q₁_orthogonal : Q₂.transpose * Q₁ = 0)
    (h_complete : Q₁ * Q₁.transpose + Q₂ * Q₂.transpose = 1)
    (hΛ₁_diag : Λ₁.IsDiag)
    (hΛ₁_pos : ∀ i : Fin r, 0 < Λ₁ i i)
    (hXhat_decomp : Xhat = Q₁ * Λ₁ * Q₁.transpose)
    (hXhat_feas : p.isFeasible Xhat) :
    ((∀ i : Fin m, Matrix.trace (p.A i * V) = 0) ∧
      Matrix.PosSemidef (Xhat + V) ∧
      Matrix.PosSemidef (Xhat - V)) ↔
    ∃ Y : Matrix (Fin r) (Fin r) ℝ,
      Y.IsSymm ∧
      V = Q₁ * Y * Q₁.transpose ∧
      (∀ i : Fin m, Matrix.trace (Q₁.transpose * p.A i * Q₁ * Y) = 0) ∧
      Matrix.PosSemidef (Λ₁ + Y) ∧
      Matrix.PosSemidef (Λ₁ - Y) := by
  sorry
