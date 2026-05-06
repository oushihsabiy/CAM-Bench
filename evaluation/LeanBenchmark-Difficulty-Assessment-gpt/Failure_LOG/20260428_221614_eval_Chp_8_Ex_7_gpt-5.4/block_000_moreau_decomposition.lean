theorem moreau_decomposition
    {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf : IsClosedConvexFunction f)
    {lam : ℝ}
    (hlam : 0 < lam)
    (x : Fin n → ℝ) :
    let prox_f :=
      ProximalMapping
        (fun y : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) y))
        lam
        ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
    let prox_fc :=
      ProximalMapping
        (FenchelConjugate
          (fun y : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) y)))
        (lam⁻¹)
        ((1 / lam) • ((EuclideanSpace.equiv (Fin n) ℝ).symm x))
    ∃ u ∈ prox_f, ∃ v ∈ prox_fc,
      ((EuclideanSpace.equiv (Fin n) ℝ).symm x) = u + lam • v := by
  sorry
