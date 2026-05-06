theorem le_largestEigenvalue_iff_sub_posSemidef
    {n m : ℕ} (A : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, IsSymm (A i))
    (z : Fin m → ℝ) (η : ℝ) :
    η ≥
        sSup
          {μ : ℝ |
            ∃ x : EuclideanSpace ℝ (Fin n),
              ‖x‖ = 1 ∧
                μ = dotProduct x (fun j => ((A 0 + ∑ i : Fin m, z i • A i.succ) *ᵥ x) j)} ↔
      PosSemidef (η • (1 : Matrix (Fin n) (Fin n) ℝ) - (A 0 + ∑ i : Fin m, z i • A i.succ)) := by
  sorry
