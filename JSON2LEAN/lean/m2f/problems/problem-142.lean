import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-142»

-- Exercise_3_22

/-- The nonnegative orthant in `(Fin n → ℝ)`. -/
private def nonnegativeOrthant (n : ℕ) : Set (Fin n → ℝ) :=
  {x : Fin n → ℝ | ∀ i, 0 ≤ x i}

/-- The `k`-th axis slice of `C`. -/
private def axisSlice {n : ℕ} (C : Set (Fin n → ℝ)) (k : Fin n) : Set ℝ :=
  {a : ℝ | 0 ≤ a ∧ a • (Pi.single k (1 : ℝ) : Fin n → ℝ) ∈ C}

/-- Scaling the `k`-th coordinate axis vector inserts the scalar in the `k`-th coordinate. -/
private lemma smul_axis_eq_single {n : ℕ} (k : Fin n) (a : ℝ) :
    a • (Pi.single k (1 : ℝ) : Fin n → ℝ) = Pi.single k a := by
  -- This is just the coordinatewise description of the standard basis vector.
  ext i
  by_cases h : i = k <;> simp [Pi.single_apply, h]

/-- The indicator form of the `k`-th axis vector agrees with `Pi.single`. -/
private lemma axisIndicator_eq_single {n : ℕ} (k : Fin n) :
    (fun i => if i = k then (1 : ℝ) else 0) = Pi.single k (1 : ℝ) := by
  -- We rewrite the exercise's explicit basis vector into mathlib's `Pi.single` form.
  ext i
  by_cases h : i = k <;> simp [Pi.single_apply, h]

/-- A weighted sum of the axis vectors with coordinates `y i / r i` recovers `y`. -/
private lemma sum_weighted_axis_eq {n : ℕ} (y r : Fin n → ℝ) (hr : ∀ i, r i ≠ 0) :
    (∑ i, (y i / r i) • ((r i) • (Pi.single i (1 : ℝ) : Fin n → ℝ))) = y := by
  -- After expanding each axis term, the sum is just the coordinatewise reconstruction of `y`.
  ext j
  simp [smul_axis_eq_single, Pi.single_apply, hr]

/-- Closure of the orthant complement still lies in the orthant. -/
private lemma mem_closure_nonnegativeOrthant {n : ℕ} {C : Set (Fin n → ℝ)} {y : Fin n → ℝ}
    (hy : y ∈ closure (nonnegativeOrthant n \ C)) :
    ∀ i, 0 ≤ y i := by
  -- The orthant is closed, so its closure inside the difference cannot leave the orthant.
  have hclosed : IsClosed (nonnegativeOrthant n) := by
    simpa [nonnegativeOrthant, Set.setOf_forall] using
      isClosed_iInter (fun i : Fin n => isClosed_Ici.preimage (continuous_apply i))
  exact closure_minimal (by intro x hx; exact hx.1) hclosed hy

/-
Exercise 3.22 | 25 | thm

Let n ∈ ℕ, let ℝ₊ⁿ := {x = (x₁, …, xₙ) ∈ ℝⁿ ∣ xᵢ ≥ 0 for i = 1, …, n}, and let C ⊆ ℝ₊ⁿ be a nonempty
closed, bounded, convex set with 0 ∈ C. Let c ∈ ℝ₊ⁿ, and for k = 1, …, n, let eₖ ∈ ℝⁿ be the k-th
standard unit vector. Define C̃ := cl(ℝ₊ⁿ ∖ C), where cl(·) denotes closure ∈ ℝⁿ. Show that the
linear function x ↦ cᵀx attains a minimum over C̃ at some point αeₖ with α ≥ 0 and k ∈ {1, …, n}.
-/
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
  classical
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  dsimp
  set Ctilde : Set (Fin n → ℝ) := closure (nonnegativeOrthant n \ C) with hCtilde
  have hCtilde_nonneg : ∀ y ∈ Ctilde, ∀ i, 0 ≤ y i := by
    -- Any closure point of the orthant complement still has nonnegative coordinates.
    intro y hy
    simpa [hCtilde] using mem_closure_nonnegativeOrthant (C := C) hy
  by_cases h0tilde : (0 : Fin n → ℝ) ∈ Ctilde
  · obtain ⟨k⟩ := (show Nonempty (Fin n) from inferInstance)
    refine ⟨0, k, le_rfl, ?_, ?_⟩
    · simpa using h0tilde
    intro y hy
    -- In the trivial branch, the zero axis point wins because both `c` and `y` are coordinatewise nonnegative.
    have hy_nonneg := hCtilde_nonneg y hy
    have hsum_nonneg : 0 ≤ ∑ i, c i * y i := by
      refine Finset.sum_nonneg ?_
      intro i hi
      exact mul_nonneg (hc i) (hy_nonneg i)
    simpa using hsum_nonneg
  · have hCtilde_closed : IsClosed Ctilde := by
      -- `Ctilde` is a closure by definition.
      simpa [hCtilde] using isClosed_closure
    obtain ⟨ε, hε_pos, hε_ball⟩ :=
      Metric.isOpen_iff.mp hCtilde_closed.isOpen_compl 0 h0tilde
    let S : Fin n → Set ℝ := fun k => axisSlice C k
    have hS_closed : ∀ k, IsClosed (S k) := by
      intro k
      -- Each slice is an intersection of the closed half-line with the closed preimage of `C`.
      have h_nonneg : IsClosed {a : ℝ | 0 ≤ a} := isClosed_Ici
      have h_memC : IsClosed {a : ℝ | a • (Pi.single k (1 : ℝ) : Fin n → ℝ) ∈ C} := by
        simpa using hC_closed.preimage (continuous_id.smul continuous_const)
      simpa [S, axisSlice, Set.setOf_and] using h_nonneg.inter h_memC
    have hS_nonempty : ∀ k, (S k).Nonempty := by
      intro k
      -- The origin belongs to every slice because `0 ∈ C`.
      refine ⟨0, ?_⟩
      simpa [S, axisSlice] using h0C
    have hS_bdd : ∀ k, BddAbove (S k) := by
      intro k
      -- Boundedness of `C` gives a uniform upper bound on each axis parameter.
      obtain ⟨R, hR⟩ := hC_bdd.subset_closedBall (0 : Fin n → ℝ)
      refine ⟨R, ?_⟩
      intro a ha
      have h_ball : a • (Pi.single k (1 : ℝ) : Fin n → ℝ) ∈ Metric.closedBall 0 R := hR ha.2
      have h_norm : ‖a • (Pi.single k (1 : ℝ) : Fin n → ℝ)‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using h_ball
      rw [smul_axis_eq_single, Pi.norm_single] at h_norm
      exact (abs_of_nonneg ha.1) ▸ h_norm
    have hhalf_mem : ∀ k, ε / 2 ∈ S k := by
      intro k
      have hhalf_pos : 0 < ε / 2 := by positivity
      have hball_mem :
          ((ε / 2) • (Pi.single k (1 : ℝ) : Fin n → ℝ)) ∈ Metric.ball 0 ε := by
        have hnorm :
            ‖((ε / 2) • (Pi.single k (1 : ℝ) : Fin n → ℝ))‖ = ε / 2 := by
          rw [smul_axis_eq_single, Pi.norm_single, Real.norm_eq_abs, abs_of_pos hhalf_pos]
        rw [Metric.mem_ball, dist_eq_norm, sub_zero, hnorm]
        linarith
      have hnot_mem : ((ε / 2) • (Pi.single k (1 : ℝ) : Fin n → ℝ)) ∉ Ctilde := hε_ball hball_mem
      have hnonneg :
          ∀ i, 0 ≤ (((ε / 2) • (Pi.single k (1 : ℝ) : Fin n → ℝ)) i) := by
        intro i
        rw [smul_axis_eq_single]
        by_cases h : i = k <;> simp [Pi.single_apply, h, le_of_lt hhalf_pos]
      have hmemC : ((ε / 2) • (Pi.single k (1 : ℝ) : Fin n → ℝ)) ∈ C := by
        -- Route correction: the useful contradiction is with membership in the closure of the orthant complement.
        by_contra hnotC
        have hdiff :
            ((ε / 2) • (Pi.single k (1 : ℝ) : Fin n → ℝ)) ∈ nonnegativeOrthant n \ C :=
          ⟨hnonneg, hnotC⟩
        have hmemCtilde :
            ((ε / 2) • (Pi.single k (1 : ℝ) : Fin n → ℝ)) ∈ Ctilde := by
          simpa [hCtilde] using (subset_closure hdiff)
        exact hnot_mem hmemCtilde
      exact ⟨le_of_lt hhalf_pos, hmemC⟩
    let r : Fin n → ℝ := fun k => sSup (S k)
    have hr_mem_slice : ∀ k, r k ∈ S k := by
      intro k
      -- Closed bounded slices attain their supremum.
      exact (hS_closed k).csSup_mem (hS_nonempty k) (hS_bdd k)
    have hr_pos : ∀ k, 0 < r k := by
      intro k
      -- The small positive axis point produced above forces the slice supremum to be positive.
      exact lt_of_lt_of_le (by positivity) (le_csSup (hS_bdd k) (hhalf_mem k))
    have hr_nonzero : ∀ k, r k ≠ 0 := fun k => ne_of_gt (hr_pos k)
    have hr_mem_Ctilde : ∀ k, (r k) • (Pi.single k (1 : ℝ) : Fin n → ℝ) ∈ Ctilde := by
      intro k
      have hr_closure :
          r k ∈ closure {a : ℝ | 0 ≤ a ∧ a • (Pi.single k (1 : ℝ) : Fin n → ℝ) ∉ C} := by
        -- We approximate the boundary radius from outside by slightly larger axis points.
        refine Metric.mem_closure_iff.2 ?_
        intro δ hδ
        refine ⟨r k + δ / 2, ?_, ?_⟩
        · constructor
          · linarith [hr_pos k]
          · intro hmemC
            have hnot :
                r k + δ / 2 ∉ S k := notMem_of_csSup_lt (by linarith) (hS_bdd k)
            exact hnot ⟨by linarith [hr_pos k], hmemC⟩
        · rw [Real.dist_eq]
          have hhalf_pos : 0 < δ / 2 := by positivity
          rw [show r k - (r k + δ / 2) = -(δ / 2) by ring, abs_neg, abs_of_pos hhalf_pos]
          linarith
      have himage_closure :
          (r k) • (Pi.single k (1 : ℝ) : Fin n → ℝ) ∈
            closure ((fun a : ℝ => a • (Pi.single k (1 : ℝ) : Fin n → ℝ)) ''
              {a : ℝ | 0 ≤ a ∧ a • (Pi.single k (1 : ℝ) : Fin n → ℝ) ∉ C}) := by
        exact mem_closure_image ((continuous_id.smul continuous_const).continuousAt) hr_closure
      have hsub :
          ((fun a : ℝ => a • (Pi.single k (1 : ℝ) : Fin n → ℝ)) ''
            {a : ℝ | 0 ≤ a ∧ a • (Pi.single k (1 : ℝ) : Fin n → ℝ) ∉ C}) ⊆
            nonnegativeOrthant n \ C := by
        intro x hx
        rcases hx with ⟨a, ha, rfl⟩
        refine ⟨?_, ha.2⟩
        intro i
        change 0 ≤ (a • (Pi.single k (1 : ℝ) : Fin n → ℝ)) i
        rw [smul_axis_eq_single]
        by_cases h : i = k <;> simp [Pi.single_apply, h, ha.1]
      simpa [hCtilde] using closure_mono hsub himage_closure
    have hsum_lt_mem_C :
        ∀ z : Fin n → ℝ, (∀ i, 0 ≤ z i) → (∑ i, z i / r i) < 1 → z ∈ C := by
      intro z hz_nonneg hz_sum
      have hweights_nonneg : ∀ i, 0 ≤ z i / r i := by
        intro i
        exact div_nonneg (hz_nonneg i) (hr_pos i).le
      have hcombo :
          (∑ j ∈ Finset.insertNone (Finset.univ : Finset (Fin n)),
            Option.elim j (1 - ∑ i, z i / r i) (fun i => z i / r i) •
              Option.elim j (0 : Fin n → ℝ)
                (fun i => (r i) • (Pi.single i (1 : ℝ) : Fin n → ℝ))) ∈ C := by
        -- A point whose normalized axis weights sum to less than one is a convex combination of
        -- the origin and the axis boundary points.
        refine hC_convex.sum_mem (Finset.forall_mem_insertNone.2 ?_) ?_
          (Finset.forall_mem_insertNone.2 ?_)
        · exact ⟨sub_nonneg.mpr hz_sum.le, fun i hi => hweights_nonneg i⟩
        · simp [Option.elim]
        · exact ⟨h0C, fun i hi => (hr_mem_slice i).2⟩
      have hz_eq :
          (∑ j ∈ Finset.insertNone (Finset.univ : Finset (Fin n)),
            Option.elim j (1 - ∑ i, z i / r i) (fun i => z i / r i) •
              Option.elim j (0 : Fin n → ℝ)
                (fun i => (r i) • (Pi.single i (1 : ℝ) : Fin n → ℝ))) = z := by
        -- The convex-combination formula is exactly the coordinate expansion of `z`.
        simp [Option.elim, sum_weighted_axis_eq, hr_nonzero]
      simpa [hz_eq] using hcombo
    have hone_le : ∀ y ∈ Ctilde, 1 ≤ ∑ i, y i / r i := by
      intro y hy
      by_contra hlt
      let U : Set (Fin n → ℝ) := {z : Fin n → ℝ | ∑ i, z i / r i < 1}
      have hyU : y ∈ U := by
        simpa [U] using hlt
      have hU_open : IsOpen U := by
        -- The strict sublevel set of the continuous affine functional is open.
        let f : (Fin n → ℝ) → ℝ := fun z => ∑ i, z i / r i
        have hf : Continuous f := by
          continuity
        simpa [U, f] using isOpen_lt hf continuous_const
      obtain ⟨z, hzU, hzmem⟩ := (mem_closure_iff.mp hy) U hU_open hyU
      exact hzmem.2 (hsum_lt_mem_C z hzmem.1 (by simpa [U] using hzU))
    obtain ⟨k, -, hkmin⟩ :=
      Finset.exists_min_image (Finset.univ : Finset (Fin n)) (fun i => c i * r i)
        Finset.univ_nonempty
    refine ⟨r k, k, (hr_pos k).le, ?_, ?_⟩
    · -- The chosen axis boundary point belongs to `Ctilde`.
      simpa [axisIndicator_eq_single] using hr_mem_Ctilde k
    · intro y hy
      have hy_nonneg := hCtilde_nonneg y hy
      have hy_weights_nonneg : ∀ i, 0 ≤ y i / r i := by
        intro i
        exact div_nonneg (hy_nonneg i) (hr_pos i).le
      have hk_nonneg : 0 ≤ c k * r k := mul_nonneg (hc k) (hr_pos k).le
      have hrewrite :
          (∑ i, c i * y i) = ∑ i, (c i * r i) * (y i / r i) := by
        -- We rewrite the objective in terms of the normalized axis weights.
        refine Finset.sum_congr rfl ?_
        intro i hi
        field_simp [hr_nonzero i]
      have hbound : c k * r k ≤ ∑ i, c i * y i := by
        calc
          c k * r k = (c k * r k) * 1 := by ring
          _ ≤ (c k * r k) * ∑ i, y i / r i :=
            mul_le_mul_of_nonneg_left (hone_le y hy) hk_nonneg
          _ = ∑ i, (c k * r k) * (y i / r i) := by rw [Finset.mul_sum]
          _ ≤ ∑ i, (c i * r i) * (y i / r i) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            exact mul_le_mul_of_nonneg_right (hkmin i (Finset.mem_univ i)) (hy_weights_nonneg i)
          _ = ∑ i, c i * y i := hrewrite.symm
      -- We now translate the bound back to the exercise's explicit axis notation.
      simpa [axisIndicator_eq_single, Pi.single_apply] using hbound

/- [BLOCK Exercise 3.22 | 26 | thm]
Let n ∈ ℕ, let ℝ_+^n := {x=(x₁,dots,xₙ)∈ ℝ^n | xᵢ ≥ 0 for i=1,dots,n}, and let C ⊆ ℝ_+^n be a
nonempty closed, bounded, convex set with 0 ∈ C. Let c ∈ ℝ_+^n, and for k=1,dots,n, let eₖ ∈ ℝ^n be
the k-th standard unit vector. Define tilde C := cl(ℝ_+^n setminus C), where cl(·) denotes closure ∈
ℝ^n. Conclude that minimizing cᵀ x over tilde C reduces to solving n one-dimensional optimization
problems.
-/
theorem linear_min_on_closure_nonnegative_compl_reduces_to_axis_problems
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
    ∃ k : Fin n, ∃ α : ℝ,
      0 ≤ α ∧
        (α • (fun i => if i = k then (1 : ℝ) else 0)) ∈
          closure ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} \ C) ∧
        (∀ y ∈ closure ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} \ C),
          ∑ i, c i * ((α • (fun j => if j = k then (1 : ℝ) else 0)) i) ≤
            ∑ i, c i * y i) := by
  -- The reduction statement is exactly the previous theorem with the witnesses reordered.
  obtain ⟨α, k, hα, hmem, hmin⟩ :=
    linear_min_on_closure_nonnegative_compl_attained_on_axis n C hC_nonempty hC_closed hC_bdd
      hC_convex h0C hC_nonneg c hc hn
  exact ⟨k, α, hα, hmem, hmin⟩

end «problem-142»
