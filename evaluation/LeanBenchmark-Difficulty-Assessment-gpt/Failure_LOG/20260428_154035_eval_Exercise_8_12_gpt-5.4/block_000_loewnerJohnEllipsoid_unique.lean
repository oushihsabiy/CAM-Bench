theorem loewnerJohnEllipsoid_unique
    (n : ℕ) (S : Set (Fin n → ℝ)) :
    (∃ c : Fin n → ℝ, ∃ A : {A : Matrix (Fin n) (Fin n) ℝ //
      A.IsSymm ∧ ∀ y : Fin n → ℝ, y ≠ 0 → 0 < dotProduct y (A.mulVec y)},
      isLoewnerJohnEllipsoid n S c A) →
    ∀ c₁ c₂ : Fin n → ℝ,
      ∀ A₁ A₂ : {A : Matrix (Fin n) (Fin n) ℝ //
        A.IsSymm ∧ ∀ y : Fin n → ℝ, y ≠ 0 → 0 < dotProduct y (A.mulVec y)},
      isLoewnerJohnEllipsoid n S c₁ A₁ →
      isLoewnerJohnEllipsoid n S c₂ A₂ →
      ellipsoid n c₁ A₁ = ellipsoid n c₂ A₂ := by
  intro hExists c₁ c₂ A₁ A₂ h₁ h₂
  rcases hExists with ⟨c, A, hA⟩
  exact h₁.2.2 c₂ A₂ h₂.1 h₂

/- [BLOCK Exercise 8.12 | 17 | thm]
Let S be a subset of ℝ^n. Prove that whenever the Loewner-John ellipsoid of S exists, it is unique.
-/