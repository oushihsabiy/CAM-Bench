theorem loewnerJohnEllipsoid_unique_of_exists
    (n : ℕ) (S : Set (Fin n → ℝ))
    (c₁ c₂ : Fin n → ℝ)
    (A₁ A₂ : {A : Matrix (Fin n) (Fin n) ℝ //
      A.IsSymm ∧ ∀ y : Fin n → ℝ, y ≠ 0 → 0 < dotProduct y (A.mulVec y)})
    (h₁ : isLoewnerJohnEllipsoid n S c₁ A₁)
    (h₂ : isLoewnerJohnEllipsoid n S c₂ A₂) :
    ellipsoid n c₁ A₁ = ellipsoid n c₂ A₂ := by
  sorry
