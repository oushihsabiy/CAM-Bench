theorem quasiconvexOn_perspective_of_convex
    {n : ℕ}
    (c : Fin n → ℝ)
    (d : ℝ)
    (f0 : (Fin n → ℝ) → WithTop ℝ)
    (hf0 : Convex ℝ {xt : (Fin n → ℝ) × ℝ | f0 xt.1 ≤ (xt.2 : WithTop ℝ)})
    (hC :
      Convex ℝ
        {x : Fin n → ℝ | f0 x < ⊤ ∧ 0 < (∑ j : Fin n, c j * x j) + d}) :
    QuasiconvexOn
      {x : Fin n → ℝ | f0 x < ⊤ ∧ 0 < (∑ j : Fin n, c j * x j) + d}
      hC
      (fun x => ((f0 x.1).getD 0 / ((∑ j : Fin n, c j * x.1 j) + d) : ℝ)) := by
  intro r
  by_cases hr : r < 0
  · have hEq :
      {x |
          x ∈ {x : Fin n → ℝ | f0 x < ⊤ ∧ 0 < (∑ j : Fin n, c j * x j) + d} ∧
            ((f0 x).getD 0 / ((∑ j : Fin n, c j * x j) + d) : ℝ) ≤ r} = (∅ : Set (Fin n → ℝ)) := by
        apply Set.eq_empty_iff_forall_not_mem.mpr
        intro x hx
        rcases hx with ⟨hxC, hxle⟩
        rcases hxC with ⟨hxfin, hxpos⟩
        rcases WithTop.ne_top_iff_exists.mp (ne_of_lt hxfin) with ⟨a, ha⟩
        have hget : (f0 x).getD 0 = a := by simp [ha]
        have ha_nonneg : 0 ≤ a := by
          have hle : (0 : WithTop ℝ) ≤ a := by
            simpa [ha] using (bot_le : (⊥ : WithTop ℝ) ≤ f0 x)
          exact_mod_cast hle
        have hdiv_nonneg : 0 ≤ ((f0 x).getD 0 / ((∑ j : Fin n, c j * x j) + d) : ℝ) := by
          rw [hget]
          exact div_nonneg ha_nonneg (le_of_lt hxpos)
        have : ¬ 0 ≤ r := not_le.mpr hr
        exact this (le_trans hdiv_nonneg hxle)
      rw [hEq]
      exact convex_empty
  · let s : Set (Fin n → ℝ) :=
      {x : Fin n → ℝ | f0 x ≤ (((r * ((∑ j : Fin n, c j * x j) + d)) : ℝ) : WithTop ℝ)}
    have hs : Convex ℝ s := by
      rw [convex_iff_add_mem]
      intro x hx y hy a b ha hb hab
      have hx' :
          ((x, r * ((∑ j : Fin n, c j * x j) + d)) : (Fin n → ℝ) × ℝ) ∈
            {xt : (Fin n → ℝ) × ℝ | f0 xt.1 ≤ (xt.2 : WithTop ℝ)} := hx
      have hy' :
          ((y, r * ((∑ j : Fin n, c j * y j) + d)) : (Fin n → ℝ) × ℝ) ∈
            {xt : (Fin n → ℝ) × ℝ | f0 xt.1 ≤ (xt.2 : WithTop ℝ)} := hy
      have hxy := hf0 hx' hy' ha hb hab
      have hsum :
          (∑ j : Fin n, c j * (a • x + b • y) j) =
            a * (∑ j : Fin n, c j * x j) + b * (∑ j : Fin n, c j * y j) := by
        simp [smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_comm, mul_left_comm,
          mul_assoc, add_comm, add_left_comm, add_assoc]
      have hright :
          r * ((∑ j : Fin n, c j * (a • x + b • y) j) + d) =
            a * (r * ((∑ j : Fin n, c j * x j) + d)) +
              b * (r * ((∑ j : Fin n, c j * y j) + d)) := by
        rw [hsum]
        nlinarith
      simpa [s, Prod.smul_mk, hright] using hxy
    have hEq :
        {x |
            x ∈ {x : Fin n → ℝ | f0 x < ⊤ ∧ 0 < (∑ j : Fin n, c j * x j) + d} ∧
              ((f0 x).getD 0 / ((∑ j : Fin n, c j * x j) + d) : ℝ) ≤ r}
          =
        {x : Fin n → ℝ | x ∈ {x : Fin n → ℝ | f0 x < ⊤ ∧ 0 < (∑ j : Fin n, c j * x j) + d} ∧ x ∈ s} := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨hxC, hxle⟩
        rcases hxC with ⟨hxfin, hxpos⟩
        refine ⟨⟨hxfin, hxpos⟩, ?_⟩
        rcases WithTop.ne_top_iff_exists.mp (ne_of_lt hxfin) with ⟨a, ha⟩
        have hget : (f0 x).getD 0 = a := by simp [ha]
        have hmul : a ≤ r * ((∑ j : Fin n, c j * x j) + d) := by
          rw [hget] at hxle
          exact (le_div_iff₀ hxpos).mp hxle
        simpa [s, ha] using hmul
      · intro hx
        rcases hx with ⟨hxC, hsx⟩
        rcases hxC with ⟨hxfin, hxpos⟩
        refine ⟨⟨hxfin, hxpos⟩, ?_⟩
        rcases WithTop.ne_top_iff_exists.mp (ne_of_lt hxfin) with ⟨a, ha⟩
        have hget : (f0 x).getD 0 = a := by simp [ha]
        have hmul : a ≤ r * ((∑ j : Fin n, c j * x j) + d) := by
          simpa [s, ha] using hsx
        rw [hget]
        exact (le_div_iff₀ hxpos).2 hmul
    rw [hEq]
    simpa [Set.sep_inter] using hC.inter hs

/- [BLOCK Exercise 3.7-(a) | 1 | thm]
Let D = {p ∈ ℝ_+^m | a_iᵀ p > 0 for i = 1, ..., n}.
Define
f(p) = max_{i = 1, ..., n} |log(a_iᵀ p) - log(I_des)|
for p in D, where aᵢ ∈ ℝ^m for i = 1, ..., n and I_des > 0.
Show that the function p -> exp(f(p)) is convex on D.
-/
open scoped RealInnerProductSpace