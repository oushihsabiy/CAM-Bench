theorem generalizedInequality_smul {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsProperCone K) {x y : Fin n → ℝ}
    (hxy : x ≼[K] y) {a : ℝ} (ha : 0 ≤ a) : (a • x) ≼[K] (a • y) := by
  rw [generalizedInequality_def] at hxy ⊢
  simpa [sub_eq_add_neg, smul_add, smul_neg] using hK.1 hxy ha

/-- The strict generalized inequality induced by a proper cone is irreflexive. -/