theorem restrictedConvexProblem_feasible_implies_min_distance
    {k N m : ℕ} (P : RestrictedConvexProblem k N m)
    (hconv_f0 : ConvexOn ℝ (Set.univ : Set (Fin N → Fin k → ℝ)) P.f0)
    (hconv_fi : ∀ i : Fin m, ConvexOn ℝ (Set.univ : Set (Fin N → Fin k → ℝ)) (P.fi i)) :
    Convex ℝ P.constraints ∧
      ∀ x : Fin N → Fin k → ℝ, P.isFeasible x →
        ∀ i j : Fin N, i.val < j.val → ‖x i - x j‖ ≥ P.Dmin := by
  sorry
