theorem trajectory_has_third_order_taylor_expansion
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (x s : Fin n → ℝ)
    (lam : Fin m → ℝ)
    (hxpos : ∀ i : Fin n, 0 < x i)
    (hspos : ∀ i : Fin n, 0 < s i)
    (xhat : ℝ → Fin n → ℝ)
    (lamhat : ℝ → Fin m → ℝ)
    (shat : ℝ → Fin n → ℝ)
    (xdot xddot xthird : Fin n → ℝ)
    (lamdot lamddot lamthird : Fin m → ℝ)
    (sdot sddot sthird : Fin n → ℝ)
    (hF : ∀ᶠ τ in 𝓝 0,
      Matrix.mulVec A.transpose (lamhat τ) + shat τ - c =
        (1 - τ) • (Matrix.mulVec A.transpose lam + s - c) ∧
      Matrix.mulVec A (xhat τ) - b = (1 - τ) • (Matrix.mulVec A x - b) ∧
      (fun i : Fin n => xhat τ i * shat τ i) = (1 - τ) • (fun i : Fin n => x i * s i))
    (h0 : xhat 0 = x ∧ lamhat 0 = lam ∧ shat 0 = s)
    (hxderiv1 : ∀ i : Fin n, HasDerivAt (fun τ : ℝ => xhat τ i) (xdot i) 0)
    (hlamderiv1 : ∀ i : Fin m, HasDerivAt (fun τ : ℝ => lamhat τ i) (lamdot i) 0)
    (hsderiv1 : ∀ i : Fin n, HasDerivAt (fun τ : ℝ => shat τ i) (sdot i) 0)
    (hxderiv2 : ∀ i : Fin n, HasDerivAt (fun τ : ℝ => deriv (fun t : ℝ => xhat t i) τ) (xddot i) 0)
    (hlamderiv2 : ∀ i : Fin m, HasDerivAt (fun τ : ℝ => deriv (fun t : ℝ => lamhat t i) τ) (lamddot i) 0)
    (hsderiv2 : ∀ i : Fin n, HasDerivAt (fun τ : ℝ => deriv (fun t : ℝ => shat t i) τ) (sddot i) 0)
    (hxderiv3 :
      ∀ i : Fin n,
        HasDerivAt (fun τ : ℝ => deriv (fun u : ℝ => deriv (fun t : ℝ => xhat t i) u) τ) (xthird i) 0)
    (hlamderiv3 :
      ∀ i : Fin m,
        HasDerivAt (fun τ : ℝ => deriv (fun u : ℝ => deriv (fun t : ℝ => lamhat t i) u) τ) (lamthird i) 0)
    (hsderiv3 :
      ∀ i : Fin n,
        HasDerivAt (fun τ : ℝ => deriv (fun u : ℝ => deriv (fun t : ℝ => shat t i) u) τ) (sthird i) 0) :
    (∀ i : Fin n,
      Tendsto
        (fun τ : ℝ =>
          ((xhat τ i) -
              (x i + τ * xdot i + (τ ^ 2 / 2) * xddot i + (τ ^ 3 / 6) * xthird i)) / τ ^ 3)
        (𝓝[≠] 0) (𝓝 0)) ∧
    (∀ i : Fin m,
      Tendsto
        (fun τ : ℝ =>
          ((lamhat τ i) -
              (lam i + τ * lamdot i + (τ ^ 2 / 2) * lamddot i + (τ ^ 3 / 6) * lamthird i)) / τ ^ 3)
        (𝓝[≠] 0) (𝓝 0)) ∧
    (∀ i : Fin n,
      Tendsto
        (fun τ : ℝ =>
          ((shat τ i) -
              (s i + τ * sdot i + (τ ^ 2 / 2) * sddot i + (τ ^ 3 / 6) * sthird i)) / τ ^ 3)
        (𝓝[≠] 0) (𝓝 0)) := by
  sorry
