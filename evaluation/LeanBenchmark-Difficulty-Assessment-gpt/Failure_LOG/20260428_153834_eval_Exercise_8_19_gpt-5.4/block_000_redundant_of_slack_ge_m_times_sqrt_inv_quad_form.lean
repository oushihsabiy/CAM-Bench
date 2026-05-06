theorem redundant_of_slack_ge_m_times_sqrt_inv_quad_form
    {n m : ℕ}
    (a : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (x_ac : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ)
    (k : Fin m)
    (hint_nonempty :
      ∃ x : Fin n → ℝ, ∀ i : Fin m, ∑ j : Fin n, a i j * x j < b i)
    (hx_ac :
      ∀ i : Fin m, ∑ j : Fin n, a i j * x_ac j < b i)
    (hmin :
      ∀ x : {x : Fin n → ℝ // ∀ i : Fin m, ∑ j : Fin n, a i j * x j < b i},
        logarithmicBarrier a b ⟨x_ac, hx_ac⟩ ≤ logarithmicBarrier a b x)
    (hH :
      H =
        ∑ i : Fin m,
          (((b i - ∑ j : Fin n, a i j * x_ac j) ^ (2 : ℕ))⁻¹) •
            Matrix.vecMulVec (a i) (a i))
    (hHinv : Invertible H)
    (hcond :
      b k - ∑ j : Fin n, a k j * x_ac j ≥
        (m : ℝ) *
          Real.sqrt
            (∑ i : Fin n,
              a k i * ∑ j : Fin n, (⅟ H) i j * a k j)) :
    isRedundantInequality a b k := by
  intro x hx
  have hxk : ∑ j : Fin n, a k j * x j ≤ b k := by
    by_contra hk
    have hxall : ∀ i : Fin m, i ≠ k → ∑ j : Fin n, a i j * x j ≤ b i := by
      intro i hi
      exact hx i hi
    exact not_isEmpty (α := Fin m)
  exact hxk