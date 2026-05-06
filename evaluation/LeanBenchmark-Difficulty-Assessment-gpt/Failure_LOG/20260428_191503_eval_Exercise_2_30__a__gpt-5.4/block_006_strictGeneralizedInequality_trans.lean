theorem strictGeneralizedInequality_trans {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsProperCone K)
    {x y z : Fin n → ℝ} :
    StrictGeneralizedInequality K x y →
      StrictGeneralizedInequality K y z → StrictGeneralizedInequality K x z := by
  intro hxy hyz
  simpa [StrictGeneralizedInequality, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    add_mem (hxy : x - y ∈ interior K) (hyz : y - z ∈ interior K)

/-- Strict generalized inequality is preserved under addition. -/