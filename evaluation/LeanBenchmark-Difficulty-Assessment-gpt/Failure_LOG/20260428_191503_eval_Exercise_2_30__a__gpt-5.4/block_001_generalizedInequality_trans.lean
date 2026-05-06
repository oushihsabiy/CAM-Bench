theorem generalizedInequality_trans {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsProperCone K)
     {x y z : Fin n → ℝ} :
     GeneralizedInequality K x y → GeneralizedInequality K y z → GeneralizedInequality K x z := by
      intro hxy hyz
      dsimp [GeneralizedInequality] at hxy hyz ⊢
      have hsum : (y - x) + (z - y) ∈ K := hK.2.1 hxy hyz
      convert hsum using 1
      funext i
      simp