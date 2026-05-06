import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-83»
/-
Consider the entropy minimization problem: minimize f(x) = \sum_{i = 1}^n xᵢ log xᵢ subject to A x =
b, with domain R_{+ +}^n. Here A is p by n with rank(A) = p < n, and assume there exists a strictly
positive feasible point x with A x = b.
-/
open BigOperators

/-
b, with domain R_{+ +}^n. Here A is p by n with rank(A) = p < n, and assume there exists a strictly
-/
structure EntropyMinimizationProblem where
  n : ℕ
  p : ℕ
  hpn : p < n
  A : Matrix (Fin p) (Fin n) ℝ
  rank_eq : A.rank = p
  b : Fin p → ℝ
  strictFeasiblePointExists : ∃ x : Fin n → ℝ, (∀ i : Fin n, 0 < x i) ∧ A.mulVec x = b

/-
b, with domain R_{+ +}^n. Here A is p by n with rank(A) = p < n, and assume there exists a strictly
-/
def EntropyMinimizationProblem.objective (P : EntropyMinimizationProblem) (x : Fin P.n → ℝ) : ℝ :=
  ∑ i : Fin P.n, x i * Real.log (x i)

/-
b, with domain R_{+ +}^n. Here A is p by n with rank(A) = p < n, and assume there exists a strictly
-/
def EntropyMinimizationProblem.isFeasible (P : EntropyMinimizationProblem) (x : Fin P.n → ℝ) : Prop :=
  (∀ i : Fin P.n, 0 < x i) ∧ P.A.mulVec x = P.b

/-- Nonnegative vectors satisfy the standard entropy coercive bound
`∑ i, x i ≤ objective x + n`. -/
lemma sum_le_objective_add_card (P : EntropyMinimizationProblem) (x : Fin P.n → ℝ)
    (hx : ∀ i : Fin P.n, 0 ≤ x i) :
    (∑ i : Fin P.n, x i) ≤ P.objective x + P.n := by
  -- Each coordinate satisfies `x ≤ x log x + 1` because `klFun x = x log x + 1 - x` is nonnegative.
  have hcoord : ∀ i : Fin P.n, x i ≤ x i * Real.log (x i) + 1 := by
    intro i
    have hkl : 0 ≤ InformationTheory.klFun (x i) := InformationTheory.klFun_nonneg (hx i)
    have hkl' : 0 ≤ x i * Real.log (x i) + 1 - x i := by
      simpa [InformationTheory.klFun] using hkl
    linarith
  -- Summing the scalar inequality gives the global bound.
  calc
    ∑ i : Fin P.n, x i ≤ ∑ i : Fin P.n, (x i * Real.log (x i) + 1) := by
      exact Finset.sum_le_sum fun i _ => hcoord i
    _ = P.objective x + P.n := by
      rw [Finset.sum_add_distrib]
      simp [EntropyMinimizationProblem.objective, add_comm]

/-- The entropy objective is continuous on the full ambient space. -/
lemma continuous_objective (P : EntropyMinimizationProblem) :
    Continuous P.objective := by
  -- The sum is finite, so continuity reduces to the coordinatewise continuity of `x ↦ x log x`.
  simpa [EntropyMinimizationProblem.objective] using
    continuous_finset_sum Finset.univ
      (fun i _ => Real.continuous_mul_log.comp (continuous_apply i))

/-- The entropy objective attains a minimum on the closed nonnegative affine slice. -/
lemma exists_relaxed_entropy_minimizer (P : EntropyMinimizationProblem) :
    ∃ x : Fin P.n → ℝ,
      (∀ i : Fin P.n, 0 ≤ x i) ∧
      P.A.mulVec x = P.b ∧
      ∀ y : Fin P.n → ℝ,
        ((∀ i : Fin P.n, 0 ≤ y i) ∧ P.A.mulVec y = P.b) → P.objective x ≤ P.objective y := by
  rcases P.strictFeasiblePointExists with ⟨x0, hx0_pos, hx0_eq⟩
  let K : Set (Fin P.n → ℝ) :=
    {x | (∀ i : Fin P.n, 0 ≤ x i) ∧ P.A.mulVec x = P.b ∧ P.objective x ≤ P.objective x0}
  have hx0_mem : x0 ∈ K := by
    -- The given strictly feasible point belongs to the relaxed slice and its own sublevel set.
    refine ⟨fun i => (hx0_pos i).le, hx0_eq, le_rfl⟩
  have hNonnegClosed : IsClosed {x : Fin P.n → ℝ | ∀ i : Fin P.n, 0 ≤ x i} := by
    -- Coordinatewise nonnegativity is the closed order interval `Ici 0` in the function space.
    simpa using (isClosed_Ici : IsClosed (Set.Ici (fun _ : Fin P.n => (0 : ℝ))))
  have hAffineClosed : IsClosed {x : Fin P.n → ℝ | P.A.mulVec x = P.b} := by
    -- The affine constraint is a singleton preimage under a continuous linear map.
    simpa [Matrix.coe_mulVecLin] using
      (isClosed_singleton.preimage (LinearMap.continuous_of_finiteDimensional P.A.mulVecLin))
  have hSublevelClosed : IsClosed {x : Fin P.n → ℝ | P.objective x ≤ P.objective x0} := by
    -- Sublevel sets of a continuous real-valued map are closed.
    simpa using (isClosed_Iic.preimage (continuous_objective P))
  have hKClosed : IsClosed K := by
    -- `K` is the intersection of the three closed conditions above.
    simpa [K] using hNonnegClosed.inter (hAffineClosed.inter hSublevelClosed)
  have hK_subset_box :
      K ⊆ Set.Icc (fun _ : Fin P.n => (0 : ℝ)) (fun _ : Fin P.n => P.objective x0 + P.n) := by
    intro x hx
    refine Set.mem_Icc.mpr ?_
    constructor
    · exact hx.1
    · intro i
      -- The entropy coercive bound controls every coordinate on the fixed sublevel set.
      have hsingle : x i ≤ ∑ j : Fin P.n, x j := by
        exact Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
      have hsum : ∑ j : Fin P.n, x j ≤ P.objective x + P.n :=
        sum_le_objective_add_card P x hx.1
      linarith [hsingle, hsum, hx.2.2]
  have hKCompact : IsCompact K := by
    -- The sublevel set sits inside a compact box and is closed there.
    exact IsCompact.of_isClosed_subset
      (isCompact_Icc : IsCompact
        (Set.Icc (fun _ : Fin P.n => (0 : ℝ)) (fun _ : Fin P.n => P.objective x0 + P.n)))
      hKClosed hK_subset_box
  obtain ⟨xStar, hxStar_mem, hxStar_min⟩ :=
    hKCompact.exists_isMinOn ⟨x0, hx0_mem⟩ (continuous_objective P).continuousOn
  refine ⟨xStar, hxStar_mem.1, hxStar_mem.2.1, ?_⟩
  intro y hy
  by_cases hy_sublevel : P.objective y ≤ P.objective x0
  · -- Inside the same compact sublevel set, minimality on `K` gives the desired inequality.
    exact hxStar_min ⟨hy.1, hy.2, hy_sublevel⟩
  · -- Outside the chosen sublevel set, `xStar` already wins by its own sublevel membership.
    have hxStar_le : P.objective xStar ≤ P.objective x0 := hxStar_mem.2.2
    linarith

/-- Distinct nonnegative feasible points have strictly smaller entropy at their midpoint. -/
lemma objective_midpoint_lt (P : EntropyMinimizationProblem) (x y : Fin P.n → ℝ)
    (hx : ∀ i : Fin P.n, 0 ≤ x i) (hy : ∀ i : Fin P.n, 0 ≤ y i) (hxy : x ≠ y) :
    P.objective ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) < (P.objective x + P.objective y) / 2 := by
  have hcoord_ne : ∃ i : Fin P.n, x i ≠ y i := by
    -- Distinct vectors differ at some coordinate.
    by_contra hcoord_ne
    apply hxy
    ext i
    by_contra hij
    exact hcoord_ne ⟨i, hij⟩
  obtain ⟨i0, hi0⟩ := hcoord_ne
  have hstrict :
      (((1 / 2 : ℝ) * x i0 + (1 / 2 : ℝ) * y i0) *
          Real.log (((1 / 2 : ℝ) * x i0 + (1 / 2 : ℝ) * y i0))) <
        (1 / 2 : ℝ) * (x i0 * Real.log (x i0)) +
          (1 / 2 : ℝ) * (y i0 * Real.log (y i0)) := by
    -- Strict convexity of `t ↦ t log t` supplies the strict inequality at the differing coordinate.
    simpa [one_div, add_comm, add_left_comm, add_assoc, mul_add, add_mul, two_mul] using
      (Real.strictConvexOn_mul_log.2 (show x i0 ∈ Set.Ici (0 : ℝ) by exact hx i0)
        (show y i0 ∈ Set.Ici (0 : ℝ) by exact hy i0) hi0 (by positivity) (by positivity)
        (by norm_num : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1))
  have hweak :
      ∀ i : Fin P.n,
        (((1 / 2 : ℝ) * x i + (1 / 2 : ℝ) * y i) * Real.log
            (((1 / 2 : ℝ) * x i + (1 / 2 : ℝ) * y i))) ≤
          (1 / 2 : ℝ) * (x i * Real.log (x i)) + (1 / 2 : ℝ) * (y i * Real.log (y i)) := by
    intro i
    -- Convexity gives the weak inequality at every coordinate.
    simpa [one_div, add_comm, add_left_comm, add_assoc, mul_add, add_mul, two_mul] using
      (Real.convexOn_mul_log.2 (show x i ∈ Set.Ici (0 : ℝ) by exact hx i)
        (show y i ∈ Set.Ici (0 : ℝ) by exact hy i) (by positivity) (by positivity)
        (by norm_num : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1))
  have hsum :
      (∑ i : Fin P.n,
          ((1 / 2 : ℝ) * x i + (1 / 2 : ℝ) * y i) *
            Real.log ((1 / 2 : ℝ) * x i + (1 / 2 : ℝ) * y i)) <
        ∑ i : Fin P.n,
          ((1 / 2 : ℝ) * (x i * Real.log (x i)) + (1 / 2 : ℝ) * (y i * Real.log (y i))) := by
    -- Summing the coordinate inequalities keeps strictness because one coordinate is strict.
    exact Finset.sum_lt_sum (fun i _ => hweak i) ⟨i0, Finset.mem_univ i0, hstrict⟩
  calc
    P.objective ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)
      = ∑ i : Fin P.n,
          ((1 / 2 : ℝ) * x i + (1 / 2 : ℝ) * y i) *
            Real.log ((1 / 2 : ℝ) * x i + (1 / 2 : ℝ) * y i) := by
        simp [EntropyMinimizationProblem.objective, Pi.smul_apply, Pi.add_apply]
    _ < ∑ i : Fin P.n,
          ((1 / 2 : ℝ) * (x i * Real.log (x i)) + (1 / 2 : ℝ) * (y i * Real.log (y i))) :=
        hsum
    _ = (P.objective x + P.objective y) / 2 := by
        rw [EntropyMinimizationProblem.objective, EntropyMinimizationProblem.objective,
          Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        ring

/-- Convexity of `x log x` gives a linear upper bound along nonnegative segments. -/
lemma entropy_coordinate_segment_le (a b t : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (((1 - t) * a + t * b) * Real.log ((1 - t) * a + t * b)) - a * Real.log a
      ≤ t * (b * Real.log b - a * Real.log a) := by
  -- Convexity controls the entropy value along the segment between `a` and `b`.
  have hconv :
      ((1 - t) * a + t * b) * Real.log ((1 - t) * a + t * b) ≤
        (1 - t) * (a * Real.log a) + t * (b * Real.log b) := by
    simpa [smul_eq_mul] using
      (Real.convexOn_mul_log.2
        (show a ∈ Set.Ici (0 : ℝ) by simpa using ha)
        (show b ∈ Set.Ici (0 : ℝ) by simpa using hb)
        (show 0 ≤ 1 - t by linarith)
        ht0
        (by linarith : (1 - t) + t = 1))
  -- Subtracting the left endpoint isolates the standard affine interpolation error term.
  have hsub := sub_le_sub_right hconv (a * Real.log a)
  have hrewrite :
      (1 - t) * (a * Real.log a) + t * (b * Real.log b) - a * Real.log a =
        t * (b * Real.log b - a * Real.log a) := by
    ring
  simpa [hrewrite] using hsub

/-- A sufficiently small exponential step makes the boundary entropy term beat any fixed linear
error term. -/
lemma exists_entropy_boundary_step (c C : ℝ) (hc : 0 < c) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ t * (c * Real.log (t * c) + C) < 0 := by
  let K : ℝ := max 1 (C / c + |Real.log c| + 1)
  let t : ℝ := Real.exp (-K)
  refine ⟨t, ?_, ?_, ?_⟩
  · -- The explicit step size is positive because exponentials are always positive.
    exact Real.exp_pos _
  · -- The cutoff `K ≥ 1` forces the step size below one.
    apply Real.exp_lt_one_iff.mpr
    have hK : (0 : ℝ) < K := by
      have : (1 : ℝ) ≤ K := by
        dsimp [K]
        exact le_max_left _ _
      linarith
    linarith
  · -- The `|log c|` term guarantees the logarithm of `t * c` is at most `-C / c - 1`.
    dsimp [t, K]
    have hK_ge : C / c + |Real.log c| + 1 ≤ max 1 (C / c + |Real.log c| + 1) := by
      exact le_max_right _ _
    have hneg : -max 1 (C / c + |Real.log c| + 1) ≤ -(C / c + |Real.log c| + 1) := by
      exact neg_le_neg hK_ge
    have habs : Real.log c - |Real.log c| ≤ 0 := sub_nonpos.mpr (le_abs_self _)
    have hlin1 :
        -max 1 (C / c + |Real.log c| + 1) + Real.log c ≤
          -(C / c + |Real.log c| + 1) + Real.log c := by
      linarith
    have hlin2 : -(C / c + |Real.log c| + 1) + Real.log c ≤ -C / c - 1 := by
      ring_nf
      linarith
    have hlogtc :
        Real.log (Real.exp (-max 1 (C / c + |Real.log c| + 1)) * c) ≤ -C / c - 1 := by
      rw [Real.log_mul (Real.exp_ne_zero _) hc.ne', Real.log_exp]
      exact le_trans hlin1 hlin2
    have hmul :
        c * Real.log (Real.exp (-max 1 (C / c + |Real.log c| + 1)) * c) ≤ c * (-C / c - 1) := by
      gcongr
    have hc_ne : c ≠ 0 := hc.ne'
    have hdiv : c * (-C / c - 1) = -C - c := by
      field_simp [hc_ne]
    rw [hdiv] at hmul
    have hinner : c * Real.log (Real.exp (-max 1 (C / c + |Real.log c| + 1)) * c) + C < 0 := by
      linarith
    have ht_pos : 0 < Real.exp (-max 1 (C / c + |Real.log c| + 1)) := Real.exp_pos _
    exact mul_neg_of_pos_of_neg ht_pos hinner

/-
For the entropy minimization problem above, show that there exists a unique optimal solution x*.
-/
theorem entropy_minimization_problem_has_unique_optimal_solution
    (P : EntropyMinimizationProblem) :
    ∃! x : Fin P.n → ℝ,
      P.isFeasible x ∧
        ∀ y : Fin P.n → ℝ, P.isFeasible y → P.objective x ≤ P.objective y := by
  rcases exists_relaxed_entropy_minimizer P with ⟨xStar, hxStar_nonneg, hxStar_eq, hxStar_min⟩
  have hxStar_pos : ∀ i : Fin P.n, 0 < xStar i := by
    rcases P.strictFeasiblePointExists with ⟨x0, hx0_pos, hx0_eq⟩
    intro i
    by_contra hnot_pos
    -- Route correction: instead of a full derivative-at-zero argument, isolate one zero coordinate,
    -- bound every other coordinate linearly by convexity, and let the explicit `t log t` term win.
    have hxStar_i_eq : xStar i = 0 := by
      exact le_antisymm (le_of_not_gt hnot_pos) (hxStar_nonneg i)
    let C : ℝ :=
      Finset.sum (Finset.univ.erase i)
        (fun j : Fin P.n => x0 j * Real.log (x0 j) - xStar j * Real.log (xStar j))
    obtain ⟨t, ht_pos, ht_lt_one, ht_boundary⟩ :=
      exists_entropy_boundary_step (x0 i) C (hx0_pos i)
    let z : Fin P.n → ℝ := (1 - t) • xStar + t • x0
    have ht_le : t ≤ 1 := le_of_lt ht_lt_one
    have hz_nonneg : ∀ j : Fin P.n, 0 ≤ z j := by
      intro j
      -- The affine segment stays inside the nonnegative orthant.
      have h_left : 0 ≤ (1 - t) * xStar j := by
        apply mul_nonneg
        linarith
        exact hxStar_nonneg j
      have h_right : 0 ≤ t * x0 j := by
        exact mul_nonneg ht_pos.le (hx0_pos j).le
      dsimp [z]
      simpa [Pi.smul_apply, Pi.add_apply] using add_nonneg h_left h_right
    have hz_eq : P.A.mulVec z = P.b := by
      -- The affine constraint is preserved along the feasible segment.
      dsimp [z]
      change P.A.mulVecLin ((1 - t) • xStar + t • x0) = P.b
      have hxStar_eq' : P.A.mulVecLin xStar = P.b := by
        simpa [Matrix.mulVecLin_apply] using hxStar_eq
      have hx0_eq' : P.A.mulVecLin x0 = P.b := by
        simpa [Matrix.mulVecLin_apply] using hx0_eq
      rw [map_add, map_smul, map_smul, hxStar_eq', hx0_eq']
      ext j
      simp [Pi.smul_apply]
      ring_nf
    have hz_i : z i = t * x0 i := by
      -- At the contradictory coordinate, the segment leaves the boundary with slope `x0 i`.
      dsimp [z]
      simp [hxStar_i_eq]
    have hrest_bound :
        Finset.sum (Finset.univ.erase i)
            (fun j : Fin P.n => z j * Real.log (z j) - xStar j * Real.log (xStar j)) ≤
          Finset.sum (Finset.univ.erase i)
            (fun j : Fin P.n => t * (x0 j * Real.log (x0 j) - xStar j * Real.log (xStar j))) := by
      -- Every non-target coordinate is controlled linearly by convexity of `x log x`.
      refine Finset.sum_le_sum ?_
      intro j hj
      dsimp [z]
      simpa [Pi.smul_apply, Pi.add_apply] using
        entropy_coordinate_segment_le (xStar j) (x0 j) t
          (hxStar_nonneg j) (hx0_pos j).le ht_pos.le ht_le
    have hobj_lt : P.objective z < P.objective xStar := by
      -- Splitting off the zero coordinate exposes the negative boundary term.
      have hsplit :
          Finset.sum Finset.univ
              (fun j : Fin P.n => z j * Real.log (z j) - xStar j * Real.log (xStar j)) =
            (z i * Real.log (z i) - xStar i * Real.log (xStar i)) +
              Finset.sum (Finset.univ.erase i)
                (fun j : Fin P.n => z j * Real.log (z j) - xStar j * Real.log (xStar j)) := by
        simpa [add_comm] using
          (Finset.sum_erase_add (s := Finset.univ)
            (a := i)
            (f := fun j : Fin P.n => z j * Real.log (z j) - xStar j * Real.log (xStar j))
            (by simp)).symm
      have hi_term :
          z i * Real.log (z i) - xStar i * Real.log (xStar i) =
            t * (x0 i * Real.log (t * x0 i)) := by
        rw [hz_i, hxStar_i_eq]
        ring
      have hrest_rewrite :
          Finset.sum (Finset.univ.erase i)
              (fun j : Fin P.n => t * (x0 j * Real.log (x0 j) - xStar j * Real.log (xStar j))) =
            t * C := by
        dsimp [C]
        rw [Finset.mul_sum]
      have hobj_upper :
          P.objective z - P.objective xStar ≤ t * (x0 i * Real.log (t * x0 i) + C) := by
        calc
          P.objective z - P.objective xStar =
              Finset.sum Finset.univ
                (fun j : Fin P.n => z j * Real.log (z j) - xStar j * Real.log (xStar j)) := by
              simp [EntropyMinimizationProblem.objective, Finset.sum_sub_distrib]
          _ = (z i * Real.log (z i) - xStar i * Real.log (xStar i)) +
                Finset.sum (Finset.univ.erase i)
                  (fun j : Fin P.n => z j * Real.log (z j) - xStar j * Real.log (xStar j)) :=
              hsplit
          _ ≤ t * (x0 i * Real.log (t * x0 i)) +
                Finset.sum (Finset.univ.erase i)
                  (fun j : Fin P.n => t * (x0 j * Real.log (x0 j) - xStar j * Real.log (xStar j))) := by
              rw [hi_term]
              exact add_le_add le_rfl hrest_bound
          _ = t * (x0 i * Real.log (t * x0 i)) + t * C := by
              rw [hrest_rewrite]
          _ = t * (x0 i * Real.log (t * x0 i) + C) := by
              ring
      linarith
    have hz_relaxed : (∀ j : Fin P.n, 0 ≤ z j) ∧ P.A.mulVec z = P.b := by
      constructor
      · exact hz_nonneg
      · exact hz_eq
    have hmin := hxStar_min z hz_relaxed
    exact not_lt_of_ge hmin hobj_lt
  have hxStar_feasible : P.isFeasible xStar := ⟨hxStar_pos, hxStar_eq⟩
  have hxStar_optimal :
      ∀ y : Fin P.n → ℝ, P.isFeasible y → P.objective xStar ≤ P.objective y := by
    intro y hy
    -- Feasible points are relaxed-feasible, so the relaxed minimizer is already optimal for them.
    exact hxStar_min y ⟨fun i => (hy.1 i).le, hy.2⟩
  refine ⟨xStar, ⟨hxStar_feasible, hxStar_optimal⟩, ?_⟩
  intro y hy
  rcases hy with ⟨hy_feasible, hy_optimal⟩
  by_contra hxy
  let z : Fin P.n → ℝ := (1 / 2 : ℝ) • xStar + (1 / 2 : ℝ) • y
  have hz_feasible : P.isFeasible z := by
    constructor
    · -- Strict positivity is preserved by midpoint averaging.
      intro i
      dsimp [z]
      nlinarith [hxStar_pos i, hy_feasible.1 i]
    · -- The affine constraint is preserved by midpoint averaging.
      dsimp [z]
      change P.A.mulVecLin ((1 / 2 : ℝ) • xStar + (1 / 2 : ℝ) • y) = P.b
      have hxStar_eq' : P.A.mulVecLin xStar = P.b := by
        simpa [Matrix.mulVecLin_apply] using hxStar_eq
      have hy_eq' : P.A.mulVecLin y = P.b := by
        simpa [Matrix.mulVecLin_apply] using hy_feasible.2
      rw [map_add, map_smul, map_smul, hxStar_eq', hy_eq']
      ext j
      simp [Pi.smul_apply]
      ring_nf
  have hobj_eq : P.objective y = P.objective xStar := by
    -- Two optimal feasible points must have the same objective value.
    exact le_antisymm (hy_optimal xStar hxStar_feasible) (hxStar_optimal y hy_feasible)
  have hz_ge : P.objective xStar ≤ P.objective z := hxStar_optimal z hz_feasible
  have hz_lt : P.objective z < P.objective xStar := by
    -- The midpoint is strictly better than either endpoint unless the endpoints coincide.
    have hxy' : xStar ≠ y := by
      intro hEq
      exact hxy hEq.symm
    have hmid : P.objective z < (P.objective xStar + P.objective y) / 2 := by
      simpa [z] using
        objective_midpoint_lt P xStar y (fun i => (hxStar_pos i).le)
          (fun i => (hy_feasible.1 i).le) hxy'
    linarith
  exact not_lt_of_ge hz_ge hz_lt
end «problem-83»
