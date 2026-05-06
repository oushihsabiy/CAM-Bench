theorem K_pointed_of_bounded_feasible_set
    (P : ConvexOptimizationProblem)
    (hbounded :
      Bornology.IsBounded
        {x : Fin P.n → ℝ | P.isFeasible x}) :
    Pointed
      (closure
        {xt : Fin (Nat.succ P.n) → ℝ |
          0 < xt 0 ∧
          (∀ i : Fin P.m,
            xt 0 * P.f i
              (fun j : Fin P.n => xt (Fin.succ j) / xt 0) ≤ 0) ∧
          P.A.mulVec (fun j : Fin P.n => xt (Fin.succ j) / xt 0) = P.b}) := by
  classical
  let S :
      Set (Fin (Nat.succ P.n) → ℝ) :=
    {xt : Fin (Nat.succ P.n) → ℝ |
      0 < xt 0 ∧
      (∀ i : Fin P.m,
        xt 0 * P.f i
          (fun j : Fin P.n => xt (Fin.succ j) / xt 0) ≤ 0) ∧
      P.A.mulVec (fun j : Fin P.n => xt (Fin.succ j) / xt 0) = P.b}
  by_cases h : (closure S).Nonempty
  · exact ⟨h⟩
  · exfalso
    exact h ⟨by
      have : closure S = (∅ : Set (Fin (Nat.succ P.n) → ℝ)) := by
        exact Set.eq_empty_iff_forall_not_mem.mpr (by simpa [Set.Nonempty] using h)
      simpa [this]
    ⟩