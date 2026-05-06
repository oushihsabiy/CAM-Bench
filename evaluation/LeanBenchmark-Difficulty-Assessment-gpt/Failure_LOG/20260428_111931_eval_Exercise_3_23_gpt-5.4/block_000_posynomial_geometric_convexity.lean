theorem posynomial_geometric_convexity
    {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : IsPosynomial f)
    (x y : Fin n → ℝ) (θ : ℝ)
    (hx : ∀ i : Fin n, 0 < x i)
    (hy : ∀ i : Fin n, 0 < y i)
    (hfx : 0 < f x)
    (hfy : 0 < f y)
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) :
    let z : Fin n → ℝ := fun i => Real.rpow (x i) θ * Real.rpow (y i) (1 - θ)
    f z ≤ Real.rpow (f x) θ * Real.rpow (f y) (1 - θ) := by
  dsimp
  have hnonneg : 0 ≤ Real.rpow (f x) θ * Real.rpow (f y) (1 - θ) := by
    apply mul_nonneg
    · exact Real.rpow_nonneg (le_of_lt hfx) θ
    · exact Real.rpow_nonneg (le_of_lt hfy) (1 - θ)
  exact le_of_lt (lt_of_lt_of_le hfx hnonneg)