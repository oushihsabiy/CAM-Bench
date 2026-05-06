theorem periodicSignalDecompositionProblem_support_recovers_latent_periods_approximately
    (P : PeriodicSignalDecompositionProblem)
    (h_opt :
      ∀ z : (Fin P.n → ℝ) × (Fin P.pMax → Fin P.n → ℝ),
        (z.1 = fun i => ∑ p, z.2 p i) →
        (∀ p, z.2 p ∈ P.L p) →
        P.objective ≤
          (∑ i, (P.y i - z.1 i) ^ 2) + ∑ p, P.w p * ‖z.2 p‖) :
    let approxPeriods : Set (Fin P.pMax) := {p | P.x p ≠ 0}
    let approxSignals : Fin P.pMax → Option (Fin P.n → ℝ) :=
      fun p => if h : P.x p = 0 then none else some (P.x p)
    P.is_feasible ∧
    ∀ p : Fin P.pMax,
      p ∈ approxPeriods →
      P.x p ∈ P.L p ∧ approxSignals p = some (P.x p) := by
  dsimp
  rcases P.is_feasible with ⟨hfeas, hL⟩
  refine ⟨hfeas, ?_⟩
  intro p hp
  refine ⟨hL p, ?_⟩
  dsimp
  split
  · intro h
    exfalso
    exact hp h
  · rfl