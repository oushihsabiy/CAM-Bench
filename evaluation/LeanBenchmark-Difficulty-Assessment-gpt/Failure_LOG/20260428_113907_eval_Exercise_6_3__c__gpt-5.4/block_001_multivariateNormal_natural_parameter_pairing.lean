theorem multivariateNormal_natural_parameter_pairing
    (n : ℕ)
    (mu z : Fin n → ℝ)
    (Sigma : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ)
    (Y : Matrix (Fin n) (Fin n) ℝ)
    (hY : Y = Sigma⁻¹)
    (hx : x = Y.mulVec mu) :
    dotProduct x z + Matrix.trace (Y * Matrix.of fun i j => (-(1 : ℝ) / 2) * z i * z j) =
      -(1 / 2 : ℝ) * ∑ i : Fin n,
        (z i - mu i) * ∑ j : Fin n, Sigma⁻¹ i j * (z j - mu j)
        + (dotProduct x z - (1 / 2 : ℝ) * dotProduct x (Sigma⁻¹.mulVec mu)) := by
  subst hY
  subst hx
  classical
  simp only [dotProduct, Matrix.mulVec, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
  ring_nf