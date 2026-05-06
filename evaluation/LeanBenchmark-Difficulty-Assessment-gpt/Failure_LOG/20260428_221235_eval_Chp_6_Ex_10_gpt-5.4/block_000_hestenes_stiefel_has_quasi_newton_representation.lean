theorem hestenes_stiefel_has_quasi_newton_representation
    {n : ℕ}
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (α : ℕ → ℝ)
    (d : ℕ → EuclideanSpace ℝ (Fin n))
    (g : ℕ → EuclideanSpace ℝ (Fin n))
    (s : ℕ → EuclideanSpace ℝ (Fin n))
    (y : ℕ → EuclideanSpace ℝ (Fin n))
    (hg : ∀ k : ℕ, g k = ∇ (f k) (x k))
    (hs : ∀ k : ℕ, s k = x (k + 1) - x k)
    (hy : ∀ k : ℕ, y k = g (k + 1) - g k)
    (hstep : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    (hdir : ∀ k : ℕ,
      d (k + 1) =
        - g (k + 1) + (⟪g (k + 1), y k⟫ / ⟪d k, y k⟫) • d k)
    (hdenom : ∀ k : ℕ, ⟪d k, y k⟫ ≠ 0)
    (hortho : ∀ k : ℕ, ⟪g (k + 1), s k⟫ = 0)
    (hcurv : ∀ k : ℕ, 0 < ⟪s k, y k⟫) :
    ∀ k : ℕ, ∃ H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n),
      d (k + 1) = - H (∇ (f (k + 1)) (x (k + 1))) ∧
      LinearMap.IsSymmetric H ∧
      (∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 → 0 < ⟪v, H v⟫) ∧
      H (y k) = s k := by
  sorry
