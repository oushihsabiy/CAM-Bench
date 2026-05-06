theorem log_transformedDualFunction_lowerBound
    (P : ConvexProgramPair)
    (lam : Fin P.m → ℝ)
    (h_lam_nonneg : ∀ i, 0 ≤ lam i) :
    let transformedDualFunction : (Fin P.m → ℝ) → ℝ :=
      fun tlam =>
        sInf (Set.range (fun x : Fin P.n → ℝ => Real.exp (P.objective x) + ∑ i, tlam i * P.funcs i.succ x))
    let tildeLam : Fin P.m → ℝ :=
      fun i => Real.exp (lagrangeDualFunction P.objective (fun i x => P.funcs i.succ x) lam) * lam i
    Real.log (transformedDualFunction tildeLam) ≥
      lagrangeDualFunction P.objective (fun i x => P.funcs i.succ x) lam := by
  sorry
