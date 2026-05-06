theorem constantVectorApproximation_l1_minimizers_are_medians
    (p : ConstantVectorApproximationProblem n) :
    ∀ x : ℝ,
      p.objectiveL1 x = sInf (Set.range p.objectiveL1) ↔ IsMedian p.b x := by
  intro x
  constructor
  · intro hx
    by_contra hmed
    have hne : Set.range p.objectiveL1.Nonempty := ⟨x, rfl⟩
    have hbdd : BddBelow (Set.range p.objectiveL1) := by
      refine ⟨0, ?_⟩
      intro y hy
      rcases hy with ⟨z, rfl⟩
      exact p.objectiveL1_nonneg z
    have hlt : sInf (Set.range p.objectiveL1) < p.objectiveL1 x := by
      exact lt_of_not_ge (by
        intro hge
        exact hmed ((p.isMedian_iff_no_better_objectiveL1 x).mp ?_))
    · exact le_antisymm hge hx.ge
    rcases csInf_lt hne hlt with ⟨y, hy_mem, hy_lt⟩
    rcases hy_mem with ⟨y, rfl⟩
    have hyx : p.objectiveL1 x ≤ p.objectiveL1 y := by
      exact (p.isMedian_iff_no_better_objectiveL1 x).mpr hmed y
    linarith
  · intro hmed
    apply le_antisymm
    · exact csInf_le ⟨x, rfl⟩
    · apply le_csInf
      · intro y hy
        rcases hy with ⟨z, rfl⟩
        exact p.objectiveL1_nonneg z
      · intro y hy
        rcases hy with ⟨z, rfl⟩
        exact (p.isMedian_iff_no_better_objectiveL1 x).mpr hmed z

/- [BLOCK Exercise 6.2-(a) | 9 | thm]
Consider the constant vector approximation problem. Let n ∈ ℕ with n ≥ 1, let b=(b₁,dots,bₙ) ∈ ℝ^n,
and let 1 ∈ ℝ^n denote the vector whose entries are all 1. For a scalar variable x ∈ ℝ, consider the
optimization problem min_{x ∈ ℝ} ‖x1-b‖. Prove that, for the ell_∞-norm, the unique minimizer is x =
(min_i bᵢ + max_i bᵢ)/(2).
-/