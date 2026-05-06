theorem linear_min_on_closure_nonnegative_compl_attained_on_axis
    (n : ℕ)
    (C : Set (Fin n → ℝ))
    (hC_nonempty : C.Nonempty)
    (hC_closed : IsClosed C)
    (hC_bdd : Bornology.IsBounded C)
    (hC_convex : Convex ℝ C)
    (h0C : (0 : Fin n → ℝ) ∈ C)
    (hC_nonneg : ∀ x ∈ C, ∀ i, 0 ≤ x i)
    (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hn : 0 < n) :
    let Ctilde : Set (Fin n → ℝ) := closure ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} \ C)
    ∃ α : ℝ, ∃ k : Fin n,
      0 ≤ α ∧
        (α • (fun i => if i = k then (1 : ℝ) else 0)) ∈ Ctilde ∧
        (∀ y ∈ Ctilde,
          ∑ i, c i * ((α • (fun j => if j = k then (1 : ℝ) else 0)) i) ≤
            ∑ i, c i * y i) := by
  dsimp
  obtain ⟨k⟩ := Fin.exists_iff_nonempty.mpr hn
  refine ⟨0, k, le_rfl, ?_, ?_⟩
  · have hmem_nonneg : (0 : Fin n → ℝ) ∈ {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
      intro i
      exact le_rfl
    have hsubset :
        {x : Fin n → ℝ | ∀ i, 0 ≤ x i} ⊆
          closure ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} \ C) := by
      intro x hx
      by_cases hxC : x ∈ C
      · have hx0 : x = 0 := by
          have hseg := hC_convex.segment_subset h0C hxC
          have hclosed_nonmem :
              IsClosed ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} \ C) := by
            exact isClosed_setOf_continuous_finset.mp sorry
          sorry
      · exact subset_closure ⟨hx, hxC⟩
    simpa using hsubset hmem_nonneg
  · intro y hy
    have hy_nonneg : ∀ i, 0 ≤ y i := by
      have h_closed_nonneg : IsClosed ({x : Fin n → ℝ | ∀ i, 0 ≤ x i}) := by
        rw [show ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} : Set (Fin n → ℝ)) =
            ⋂ i : Fin n, {x : Fin n → ℝ | 0 ≤ x i} by
              ext x; simp]
        exact isClosed_iInter fun i => isClosed_le continuous_const continuous_apply
      have h_subset :
          closure ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} \ C) ⊆ {x : Fin n → ℝ | ∀ i, 0 ≤ x i} :=
        closure_minimal (by intro x hx; exact hx.1) h_closed_nonneg
      exact h_subset hy
    have hsum_nonneg : 0 ≤ ∑ i, c i * y i := by
      refine Finset.sum_nonneg ?_
      intro i hi
      exact mul_nonneg (hc i) (hy_nonneg i)
    simpa using hsum_nonneg

/- [BLOCK Exercise 3.22 | 26 | thm]
Let n ∈ ℕ, let ℝ_+^n := {x=(x₁,dots,xₙ)∈ ℝ^n | xᵢ ≥ 0 for i=1,dots,n}, and let C ⊆ ℝ_+^n be a
nonempty closed, bounded, convex set with 0 ∈ C. Let c ∈ ℝ_+^n, and for k=1,dots,n, let eₖ ∈ ℝ^n be
the k-th standard unit vector. Define tilde C := cl(ℝ_+^n setminus C), where cl(·) denotes closure ∈
ℝ^n. Conclude that minimizing cᵀ x over tilde C reduces to solving n one-dimensional optimization
problems.
-/