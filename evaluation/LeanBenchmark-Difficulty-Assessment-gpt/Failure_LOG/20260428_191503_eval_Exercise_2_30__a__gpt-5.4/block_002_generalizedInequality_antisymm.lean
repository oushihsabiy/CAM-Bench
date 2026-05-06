theorem generalizedInequality_antisymm {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsProperCone K) :
    ∀ ⦃x y : Fin n → ℝ⦄,
      GeneralizedInequality K x y → GeneralizedInequality K y x → x = y := by
  intro x y hxy hyx
  have hanti : K ∩ -K = ({0} : Set (Fin n → ℝ)) := hK.2.2.2.2.2
  have hxy' : y - x ∈ K := by
    simpa [GeneralizedInequality] using hxy
  have hyx' : x - y ∈ K := by
    simpa [GeneralizedInequality] using hyx
  have hneg : y - x ∈ -K := by
    change -(y - x) ∈ K
    simpa using hyx'
  have hmem : y - x ∈ K ∩ -K := ⟨hxy', hneg⟩
  have hzeroMem : y - x ∈ ({0} : Set (Fin n → ℝ)) := by
    rw [← hanti]
    exact hmem
  have hzero : y - x = 0 := by
    simpa using hzeroMem
  exact sub_eq_zero.mp hzero

/-- Generalized inequality is preserved under addition. -/