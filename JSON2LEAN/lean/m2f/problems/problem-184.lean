import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-184»

/- [BLOCK Exercise 17.9 | 10 | defn]
For a nonempty closed convex set C ⊆ ℝ^n, the projection of y ∈ ℝ^n onto C is the unique point
P_C(y) ∈ C such that ‖y-P_C(y)‖ ≤ ‖y-z‖ for all z ∈ C.
-/
open scoped BigOperators

def IsProjection {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (y x : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  x ∈ C ∧
    (∀ z ∈ C, ‖y - x‖ ≤ ‖y - z‖) ∧
    (∀ x' : EuclideanSpace ℝ (Fin n),
      x' ∈ C → (∀ z ∈ C, ‖y - x'‖ ≤ ‖y - z‖) → x' = x)

/- [BLOCK Exercise 17.9 | 11 | defn]
For the problem min f(x) subject to gᵢ(x) ≤ 0 and hⱼ(x)=0, the Karush--Kuhn--Tucker conditions are
that there exist multipliers λ_i ≥ 0 and nu_j such that
∇ f(x)+sum_i λ_i ∇ gᵢ(x)+sum_j nu_j ∇ hⱼ(x)=0,
gᵢ(x)≤ 0, hⱼ(x)=0, λ_i gᵢ(x)=0 for all i.
-/
open scoped RealInnerProductSpace

def kktConditions {n m p : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (h : Fin p → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ lam : Fin m → ℝ, ∃ nu : Fin p → ℝ,
    gradient f x + ∑ i, lam i • gradient (g i) x + ∑ j, nu j • gradient (h j) x = 0 ∧
      (∀ i, g i x ≤ 0) ∧
      (∀ j, h j x = 0) ∧
      (∀ i, 0 ≤ lam i) ∧
      (∀ i, lam i * g i x = 0)

/- [BLOCK Exercise 17.9 | 12 | defn]
A bound-constrained problem is an optimization problem of the form min f(x) subject to l ≤ x ≤ u
componentwise, where l,u ∈ ℝ^n are given vectors with lᵢ ≤ uᵢ.
-/
structure BoundConstrainedProblem (n : ℕ) where
  f : EuclideanSpace ℝ (Fin n) → ℝ
  l : EuclideanSpace ℝ (Fin n)
  u : EuclideanSpace ℝ (Fin n)
  bounds_ordered : ∀ i : Fin n, l i ≤ u i

def BoundConstrainedProblem.isFeasible {n : ℕ} (P : BoundConstrainedProblem n)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ i : Fin n, P.l i ≤ x i ∧ x i ≤ P.u i

/-
Exercise 17.9 | 13 | opt_prob

Let n ∈ ℕ, let l, u ∈ ℝⁿ satisfy lᵢ ≤ uᵢ for each i = 1, …, n, and let φ : ℝⁿ → ℝ be continuously
differentiable. Consider the optimization problem

minimize φ(x) subject to x ∈ ℝⁿ and l ≤ x ≤ u,

where the inequalities are componentwise, and define the feasible set by

[l, u] := {x ∈ ℝⁿ : l ≤ x ≤ u}.
-/
structure BoxConstrainedOptimizationProblem (n : ℕ) where
  φ : EuclideanSpace ℝ (Fin n) → ℝ
  φ_contDiff : ContDiff ℝ 1 φ
  l : EuclideanSpace ℝ (Fin n)
  u : EuclideanSpace ℝ (Fin n)
  bounds_ordered : ∀ i : Fin n, l i ≤ u i

def BoxConstrainedOptimizationProblem.feasibleSet {n : ℕ} (P : BoxConstrainedOptimizationProblem n) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i : Fin n, P.l i ≤ x i ∧ x i ≤ P.u i}

/-
Exercise 17.9 | 14 | thm

Let n ∈ ℕ, let l, u ∈ ℝ^n satisfy lᵢ ≤ uᵢ for each i = 1, …, n, and let φ : ℝ^n → ℝ be continuously
differentiable. Consider the bound-constrained optimization problem

min_{x ∈ ℝ^n} φ(x) subject to l ≤ x ≤ u,

where the inequalities are componentwise, and define the feasible set by

[l, u] := {x ∈ ℝ^n : l ≤ x ≤ u}.

Define the projection P(·, l, u) : ℝ^n → [l, u] componentwise by

P(g, l, u)ᵢ =
{
lᵢ, if gᵢ ≤ lᵢ,
gᵢ, if lᵢ < gᵢ < uᵢ,
uᵢ, if gᵢ ≥ uᵢ,
}

for i = 1, …, n. Verify that the Karush–Kuhn–Tucker conditions for this bound-constrained problem
are equivalent to

x - P(x - ∇φ(x), l, u) = 0.
-/
/-- The lower-half index of `Fin (n + n)` always lands back in `Fin n`. -/
lemma lowerBoxIndex_lt {n : ℕ} (i : Fin (n + n)) (h : ¬ i.1 < n) : i.1 - n < n := by
  -- The lower branch starts at `n`, so subtracting `n` returns a valid coordinate.
  have hi : i.1 < n + n := i.2
  have hge : n ≤ i.1 := Nat.le_of_not_lt h
  omega

/-- Convert a lower-half constraint index into its corresponding box coordinate. -/
def lowerBoxIndex {n : ℕ} (i : Fin (n + n)) (h : ¬ i.1 < n) : Fin n :=
  ⟨i.1 - n, lowerBoxIndex_lt i h⟩

/-- The shifted lower index recovers the original box coordinate. -/
lemma lowerBoxIndex_addNat {n : ℕ} (i : Fin n) :
    lowerBoxIndex (i.addNat n) (by simpa using Nat.not_lt.mpr (Nat.le_add_left n i.1)) = i := by
  -- Both sides have the same underlying natural-number coordinate.
  ext
  simp [lowerBoxIndex]

/-- The gradient of the upper-bound affine constraint is the matching basis vector. -/
lemma gradient_upper_box_constraint {n : ℕ}
    (P : BoxConstrainedOptimizationProblem n)
    (x : EuclideanSpace ℝ (Fin n))
    (i : Fin n) :
    gradient (fun y : EuclideanSpace ℝ (Fin n) => y i - P.u i) x =
      (EuclideanSpace.basisFun (Fin n) ℝ) i := by
  -- Identify the Frechet derivative with the `i`-th coordinate projection.
  have hproj :
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) ((EuclideanSpace.basisFun (Fin n) ℝ) i) =
        PiLp.proj 2 (fun _ : Fin n => ℝ) i := by
    ext y
    rw [EuclideanSpace.basisFun_apply, InnerProductSpace.toDual_apply_apply, PiLp.proj_apply,
      EuclideanSpace.inner_single_left]
    norm_num
  -- Then the gradient is exactly the Riesz representative of that projection.
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt, hproj]
  exact (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin n => ℝ) x i).sub_const (P.u i)

/-- The gradient of the lower-bound affine constraint is the negative basis vector. -/
lemma gradient_lower_box_constraint {n : ℕ}
    (P : BoxConstrainedOptimizationProblem n)
    (x : EuclideanSpace ℝ (Fin n))
    (i : Fin n) :
    gradient (fun y : EuclideanSpace ℝ (Fin n) => P.l i - y i) x =
      -(EuclideanSpace.basisFun (Fin n) ℝ) i := by
  -- The derivative is the negative coordinate projection.
  have hproj :
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) (-(EuclideanSpace.basisFun (Fin n) ℝ) i) =
        -(PiLp.proj 2 (fun _ : Fin n => ℝ) i) := by
    ext y
    rw [InnerProductSpace.toDual_apply_apply]
    simp [PiLp.proj_apply, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  -- Convert that derivative description into the corresponding gradient formula.
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt, hproj]
  exact (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin n => ℝ) x i).const_sub (P.l i)

/-- Scalar KKT data for one box-constrained coordinate is equivalent to the clamp fixed point. -/
lemma scalar_box_kkt_iff_clamp {l u x g : ℝ} (hlu : l ≤ u) :
    (∃ lamu laml : ℝ,
        g + lamu - laml = 0 ∧
        l ≤ x ∧ x ≤ u ∧
        0 ≤ lamu ∧
        0 ≤ laml ∧
        lamu * (x - u) = 0 ∧
        laml * (l - x) = 0) ↔
      x = max l (min (x - g) u) := by
  constructor
  · rintro ⟨lamu, laml, hstat, hlx, hxu, hlamu, hlaml, hcompl_u, hcompl_l⟩
    -- Split by which bound is active and read the sign of `g` from complementarity.
    by_cases hx_eq_l : x = l
    · by_cases hx_eq_u : x = u
      · have hlu_eq : l = u := by simpa [hx_eq_l] using hx_eq_u
        rw [hx_eq_l, hlu_eq]
        simp
      · have hlu_lt : l < u := by
          have hlu_ne : l ≠ u := by
            intro hlu_eq
            apply hx_eq_u
            simp [hx_eq_l, hlu_eq]
          exact lt_of_le_of_ne hlu hlu_ne
        have hlamu_zero : lamu = 0 := by
          rw [hx_eq_l] at hcompl_u
          exact (mul_eq_zero.mp hcompl_u).resolve_right (sub_ne_zero.mpr (ne_of_lt hlu_lt))
        have hg_nonneg : 0 ≤ g := by linarith
        rw [hx_eq_l]
        have hsub : min (l - g) u ≤ l := le_trans (min_le_left _ _) (by linarith)
        exact (max_eq_left hsub).symm
    · have hlx_lt : l < x := lt_of_le_of_ne hlx (Ne.symm hx_eq_l)
      by_cases hx_eq_u : x = u
      · have hlu_lt : l < u := by simp [hx_eq_u] at hlx_lt; exact hlx_lt
        have hlaml_zero : laml = 0 := by
          rw [hx_eq_u] at hcompl_l
          exact (mul_eq_zero.mp hcompl_l).resolve_right (sub_ne_zero.mpr (ne_of_lt hlu_lt))
        have hg_nonpos : g ≤ 0 := by linarith
        rw [hx_eq_u]
        have hu_le : u ≤ u - g := by linarith
        rw [min_eq_right hu_le]
        exact (max_eq_right hlu).symm
      · have hxu_lt : x < u := lt_of_le_of_ne hxu hx_eq_u
        have hlamu_zero : lamu = 0 := by
          exact (mul_eq_zero.mp hcompl_u).resolve_right (sub_ne_zero.mpr (ne_of_lt hxu_lt))
        have hlaml_zero : laml = 0 := by
          exact (mul_eq_zero.mp hcompl_l).resolve_right (sub_ne_zero.mpr (ne_of_lt hlx_lt))
        have hg_zero : g = 0 := by linarith
        simp [hg_zero, min_eq_left hxu_lt.le, max_eq_right hlx_lt.le]
  · intro hx
    -- The clamp identity immediately places `x` inside the interval `[l, u]`.
    have hlx : l ≤ x := by
      rw [hx]
      exact le_max_left _ _
    have hxu : x ≤ u := by
      rw [hx]
      exact max_le hlu (min_le_right _ _)
    -- Choose multipliers according to the active-set case.
    by_cases hx_eq_l : x = l
    · by_cases hx_eq_u : x = u
      · refine ⟨max (-g) 0, max g 0, ?_⟩
        refine ⟨?_, ?_, ?_, le_max_right _ _, le_max_right _ _, ?_, ?_⟩
        · rcases le_total g 0 with hg | hg
          · rw [max_eq_right hg, max_eq_left (by linarith)]
            ring
          · rw [max_eq_left hg, max_eq_right (by linarith)]
            ring
        · simpa [hx_eq_l] using hlx
        · simpa [hx_eq_u] using hxu
        · simp [hx_eq_u]
        · simp [hx_eq_l]
      · have hlu_lt : l < u := by
          have hlu_ne : l ≠ u := by
            intro hlu_eq
            apply hx_eq_u
            simpa [hx_eq_l, hlu_eq] using hx_eq_l
          exact lt_of_le_of_ne hlu hlu_ne
        rw [hx_eq_l] at hx
        have hmax : max l (min (l - g) u) = l := hx.symm
        have hmin_le : min (l - g) u ≤ l := (max_eq_left_iff).mp hmax
        have hg_nonneg : 0 ≤ g := by
          by_contra hg_neg
          have hlt1 : l < l - g := by linarith
          have : l < min (l - g) u := lt_min hlt1 hlu_lt
          linarith
        refine ⟨0, g, ?_⟩
        refine ⟨by ring, ?_, ?_, le_rfl, hg_nonneg, by ring, ?_⟩
        · simpa [hx_eq_l] using hlx
        · simpa [hx_eq_l] using hxu
        · simp [hx_eq_l]
    · have hlx_lt : l < x := lt_of_le_of_ne hlx (Ne.symm hx_eq_l)
      by_cases hx_eq_u : x = u
      · rw [hx_eq_u] at hx
        have hmax : max l (min (u - g) u) = u := hx.symm
        have hmax_right : l ≤ min (u - g) u := by
          by_contra hcontra
          rw [max_eq_left (le_of_not_ge hcontra)] at hmax
          linarith
        have hmin_eq : min (u - g) u = u := by
          simpa [max_eq_right hmax_right] using hmax
        have hg_nonpos : g ≤ 0 := by
          have hu_le : u ≤ u - g := (min_eq_right_iff).mp hmin_eq
          linarith
        refine ⟨-g, 0, ?_⟩
        refine ⟨by ring, ?_, ?_, ?_, le_rfl, ?_, by ring⟩
        · simpa [hx_eq_u] using hlx
        · simpa [hx_eq_u] using hxu
        · linarith
        · simp [hx_eq_u]
      · have hxu_lt : x < u := lt_of_le_of_ne hxu hx_eq_u
        have hmax_right : l ≤ min (x - g) u := by
          by_contra hcontra
          rw [max_eq_left (le_of_not_ge hcontra)] at hx
          linarith
        have hmin_eq : min (x - g) u = x := by
          simpa [max_eq_right hmax_right] using hx.symm
        have hg_zero : g = 0 := by
          by_cases hsub : x - g ≤ u
          · rw [min_eq_left hsub] at hmin_eq
            linarith
          · rw [min_eq_right (le_of_not_ge hsub)] at hmin_eq
            linarith
        refine ⟨0, 0, ?_⟩
        refine ⟨by linarith, hlx, hxu, le_rfl, le_rfl, by ring, by ring⟩

theorem kktConditions_iff_eq_projection_fixed_point
    {n : ℕ}
    (P : BoxConstrainedOptimizationProblem n)
    (x : EuclideanSpace ℝ (Fin n)) :
    (kktConditions P.φ
      (fun i y =>
        if h : i.1 < n then
          y ⟨i.1, h⟩ - P.u ⟨i.1, h⟩
        else
          let j : Fin n :=
            ⟨i.1 - n, by
              have hi : i.1 < n + n := i.2
              have hge : n ≤ i.1 := Nat.le_of_not_lt h
              omega⟩
          P.l j - y j)
      (fun j _ => False.elim (Fin.elim0 j))
      x) ↔
      x -
          (fun i =>
            max (P.l i) (min (x i - gradient P.φ x i) (P.u i))) =
        0 := by
  constructor
  · intro hkkt
    -- Normalize the split constraint family into scalar KKT data on each coordinate.
    rcases hkkt with ⟨lam, nu, hstationary, hineq, hEq, hlam_nonneg, hcompl⟩
    have hkktCoord :
        ∃ lamu laml : Fin n → ℝ,
          (∀ i, gradient P.φ x i + lamu i - laml i = 0) ∧
          (∀ i, P.l i ≤ x i ∧ x i ≤ P.u i) ∧
          (∀ i, 0 ≤ lamu i) ∧
          (∀ i, 0 ≤ laml i) ∧
          (∀ i, lamu i * (x i - P.u i) = 0) ∧
          (∀ i, laml i * (P.l i - x i) = 0) := by
      refine ⟨fun i => lam (Fin.castAdd n i), fun i => lam (Fin.natAdd n i), ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i
        -- Read the stationarity vector equation in the `i`-th coordinate.
        have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) hstationary
        simp [Fin.sum_univ_add, gradient_upper_box_constraint, gradient_lower_box_constraint,
          EuclideanSpace.basisFun_apply, Pi.single_apply] at hcoord
        simpa [sub_eq_add_neg, add_assoc] using hcoord
      · intro i
        -- The two inequality families are exactly the upper and lower box bounds.
        have hu := hineq (Fin.castAdd n i)
        have hl := hineq (Fin.natAdd n i)
        simp at hu hl
        exact ⟨hl, hu⟩
      · intro i
        simpa using hlam_nonneg (Fin.castAdd n i)
      · intro i
        simpa using hlam_nonneg (Fin.natAdd n i)
      · intro i
        simpa using hcompl (Fin.castAdd n i)
      · intro i
        simpa using hcompl (Fin.natAdd n i)
    rcases hkktCoord with ⟨lamu, laml, hstat, hfeas, hlamu_nonneg, hlaml_nonneg, hcompl_u, hcompl_l⟩
    -- Apply the scalar equivalence coordinatewise and reassemble the vector equality.
    apply sub_eq_zero.mpr
    ext i
    exact (scalar_box_kkt_iff_clamp (P.bounds_ordered i)).mp
      ⟨lamu i, laml i, hstat i, (hfeas i).1, (hfeas i).2, hlamu_nonneg i, hlaml_nonneg i,
        hcompl_u i, hcompl_l i⟩
  · intro hfixed
    -- Rewrite the fixed-point equation as scalar clamp equations at each coordinate.
    have hfixed' : x = fun i => max (P.l i) (min (x i - gradient P.φ x i) (P.u i)) :=
      sub_eq_zero.mp hfixed
    have hscalar :
        ∀ i : Fin n,
          ∃ lamu laml : ℝ,
            gradient P.φ x i + lamu - laml = 0 ∧
            P.l i ≤ x i ∧ x i ≤ P.u i ∧
            0 ≤ lamu ∧
            0 ≤ laml ∧
            lamu * (x i - P.u i) = 0 ∧
            laml * (P.l i - x i) = 0 := by
      intro i
      have hcoord : x i = max (P.l i) (min (x i - gradient P.φ x i) (P.u i)) := by
        simpa using congrFun hfixed' i
      exact (scalar_box_kkt_iff_clamp (P.bounds_ordered i)).mpr hcoord
    choose lamu laml hdata using hscalar
    -- Package the scalar multipliers back into the original split indexing.
    let lam : Fin (n + n) → ℝ := fun i =>
      if h : i.1 < n then
        lamu ⟨i.1, h⟩
      else
        laml (lowerBoxIndex i h)
    refine ⟨lam, Fin.elim0, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- Reassemble the stationary vector equation from the coordinatewise data.
      ext i
      have hcoord : gradient P.φ x i + lamu i - laml i = 0 := (hdata i).1
      simp [lam, lowerBoxIndex_addNat, Fin.sum_univ_add, gradient_upper_box_constraint,
        gradient_lower_box_constraint, EuclideanSpace.basisFun_apply, Pi.single_apply]
      simpa [sub_eq_add_neg, add_assoc] using hcoord
    · intro i
      -- Each original inequality branch is one of the scalar box bounds.
      by_cases h : i.1 < n
      · simpa [h, lam] using sub_nonpos.mpr (hdata ⟨i.1, h⟩).2.2.1
      · simpa [h, lam] using sub_nonpos.mpr (hdata (lowerBoxIndex i h)).2.1
    · intro j
      exact Fin.elim0 j
    · intro i
      -- Nonnegativity is inherited from the scalar multipliers.
      by_cases h : i.1 < n
      · simpa [h, lam] using (hdata ⟨i.1, h⟩).2.2.2.1
      · simpa [h, lam] using (hdata (lowerBoxIndex i h)).2.2.2.2.1
    · intro i
      -- Complementarity follows from the same split into upper and lower branches.
      by_cases h : i.1 < n
      · simpa [h, lam] using (hdata ⟨i.1, h⟩).2.2.2.2.2.1
      · simpa [h, lam] using (hdata (lowerBoxIndex i h)).2.2.2.2.2.2

end «problem-184»
