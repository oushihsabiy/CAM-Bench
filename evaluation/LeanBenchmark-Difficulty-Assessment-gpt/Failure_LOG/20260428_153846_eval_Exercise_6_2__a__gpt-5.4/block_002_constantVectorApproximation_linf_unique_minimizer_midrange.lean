theorem constantVectorApproximation_linf_unique_minimizer_midrange
    (n : ℕ) [NeZero n]
    (p : ConstantVectorApproximationProblem n) :
    ∀ x : ℝ,
      p.objectiveLinf x = sInf (Set.range p.objectiveLinf) ↔
        x = ((Finset.univ.inf' Finset.univ_nonempty p.b) + (Finset.univ.sup' Finset.univ_nonempty p.b)) / 2 := by
  intro x
  constructor
  · intro hx
    have h :
        x = ((Finset.univ.inf' Finset.univ_nonempty p.b) + (Finset.univ.sup' Finset.univ_nonempty p.b)) / 2 := by
      sorry
    exact h
  · intro hx
    rw [hx]
    have h :
        p.objectiveLinf
            (((Finset.univ.inf' Finset.univ_nonempty p.b) +
                (Finset.univ.sup' Finset.univ_nonempty p.b)) / 2) =
          sInf (Set.range p.objectiveLinf) := by
      sorry
    exact h