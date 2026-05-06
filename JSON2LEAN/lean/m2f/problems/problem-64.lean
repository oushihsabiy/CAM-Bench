import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-64»
/-
For a set E subseteq ℝ^n, its support function is the map S_E: ℝ^n → ℝ - bar defined by S_E(y) = sup
{yᵀ x | x in E} for all y ∈ ℝ^n.
-/
open scoped RealInnerProductSpace

def supportFunction {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) → EReal :=
  fun y => sSup (((fun x : EuclideanSpace ℝ (Fin n) => ((⟪y, x⟫ : ℝ) : EReal)) '' E))

/-- A point of a set gives a lower bound on the support function. -/
lemma inner_le_supportFunction_of_mem
    {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))}
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ E) :
    (((⟪y, x⟫ : ℝ) : EReal)) ≤ supportFunction E y := by
  -- Unfold the support function and insert the chosen point into the image set.
  unfold supportFunction
  exact le_sSup (Set.mem_image_of_mem
    (fun z : EuclideanSpace ℝ (Fin n) => ((⟪y, z⟫ : ℝ) : EReal)) hx)

/-- A supporting-hyperplane inequality gives an upper bound on the support function. -/
lemma supportFunction_le_inner_of_forall_sub_nonpos
    {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))}
    {y p : EuclideanSpace ℝ (Fin n)}
    (h : ∀ z ∈ E, ⟪y, z - p⟫ ≤ 0) :
    supportFunction E y ≤ (((⟪y, p⟫ : ℝ) : EReal)) := by
  -- Unfold the support function and bound every pointwise inner product by `⟪y, p⟫`.
  unfold supportFunction
  refine sSup_le ?_
  rintro _ ⟨z, hz, rfl⟩
  have hz' : ⟪y, z⟫ ≤ ⟪y, p⟫ := by
    -- Rewrite the projection inequality into a direct bound on `⟪y, z⟫`.
    have hz0 := h z hz
    rw [inner_sub_right] at hz0
    linarith
  exact show (((⟪y, z⟫ : ℝ) : EReal)) ≤ (((⟪y, p⟫ : ℝ) : EReal)) from by
    exact_mod_cast hz'

/-- At a projection point, the support function is exactly the corresponding inner product. -/
lemma supportFunction_eq_inner_of_projection
    {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))}
    {y p : EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ E) (h : ∀ z ∈ E, ⟪y, z - p⟫ ≤ 0) :
    supportFunction E y = (((⟪y, p⟫ : ℝ) : EReal)) := by
  -- Combine the lower bound from membership with the upper bound from the projection inequality.
  apply le_antisymm
  · exact supportFunction_le_inner_of_forall_sub_nonpos h
  · exact inner_le_supportFunction_of_mem hp

/-- Equality of support functions and one point of `C` force `D` to be nonempty. -/
lemma nonempty_of_support_eq_of_mem
    {n : ℕ} {C D : Set (EuclideanSpace ℝ (Fin n))}
    (h : supportFunction C = supportFunction D)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ C) :
    D.Nonempty := by
  by_contra hD_empty
  -- Evaluate the common support function at `0` to contradict the empty-set value `⊥`.
  have h0 : ((0 : ℝ) : EReal) ≤ supportFunction D 0 := by
    simpa [h] using
      (inner_le_supportFunction_of_mem (E := C) (x := x)
        (y := (0 : EuclideanSpace ℝ (Fin n))) hx)
  have hD_eq_empty : D = ∅ := Set.not_nonempty_iff_eq_empty.mp hD_empty
  have h0' : ((0 : ℝ) : EReal) ≤ supportFunction (∅ : Set (EuclideanSpace ℝ (Fin n))) 0 := by
    simpa [hD_eq_empty] using h0
  simp [supportFunction] at h0'

/-- Equality of support functions implies the corresponding inclusion for closed convex sets. -/
lemma subset_of_supportFunction_eq
    {n : ℕ} {C D : Set (EuclideanSpace ℝ (Fin n))}
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (hEq : supportFunction C = supportFunction D) :
    C ⊆ D := by
  intro x hxC
  by_contra hxD
  -- Route correction: use nearest-point projection, not supremum attainment, to build a
  -- separating direction from `x ∉ D`.
  have hD_nonempty : D.Nonempty := nonempty_of_support_eq_of_mem hEq hxC
  obtain ⟨p, hpD, hp_min⟩ :=
    exists_norm_eq_iInf_of_complete_convex hD_nonempty hD_closed.isComplete hD_convex x
  let y : EuclideanSpace ℝ (Fin n) := x - p
  have hproj : ∀ z ∈ D, ⟪y, z - p⟫ ≤ 0 := by
    -- Translate the minimizer characterization into the chosen direction `y = x - p`.
    simpa [y] using
      (norm_eq_iInf_iff_real_inner_le_zero hD_convex hpD).1 hp_min
  have hsuppD : supportFunction D y = (((⟪y, p⟫ : ℝ) : EReal)) :=
    supportFunction_eq_inner_of_projection hpD hproj
  have hinnerEReal : (((⟪y, x⟫ : ℝ) : EReal)) ≤ (((⟪y, p⟫ : ℝ) : EReal)) := by
    -- Compare the common support-function value using `x ∈ C` and the exact formula on `D`.
    calc
      (((⟪y, x⟫ : ℝ) : EReal)) ≤ supportFunction C y := inner_le_supportFunction_of_mem hxC
      _ = supportFunction D y := by rw [hEq]
      _ = (((⟪y, p⟫ : ℝ) : EReal)) := hsuppD
  have hinner : ⟪y, x⟫ ≤ ⟪y, p⟫ := by
    exact_mod_cast hinnerEReal
  have hy_ne_zero : y ≠ 0 := by
    -- If `y = 0`, then `x = p ∈ D`, contradicting the assumption `x ∉ D`.
    intro hy0
    have hxp : x = p := by
      dsimp [y] at hy0
      exact sub_eq_zero.mp hy0
    exact hxD (hxp ▸ hpD)
  have hstrict : ⟪y, p⟫ < ⟪y, x⟫ := by
    -- Rewrite `x = p + y` so the difference is the positive quantity `⟪y, y⟫ = ‖y‖^2`.
    have hx_eq : x = p + y := by
      dsimp [y]
      abel
    have hyx : ⟪y, x⟫ = ⟪y, p⟫ + ‖y‖ ^ 2 := by
      calc
        ⟪y, x⟫ = ⟪y, p + y⟫ := by rw [hx_eq]
        _ = ⟪y, p⟫ + ⟪y, y⟫ := by rw [inner_add_right]
        _ = ⟪y, p⟫ + ‖y‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
    have hy_sq_pos : 0 < ‖y‖ ^ 2 := by
      exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hy_ne_zero)
    linarith [hyx, hy_sq_pos]
  linarith

/-
Let C and D be closed convex subsets of ℝ^n. For each E subseteq ℝ^n, define the support function
S_E: ℝ^n → ℝ - bar by S_E(y) = sup {yᵀ x | x in E}, for y ∈ ℝ^n. The supremum is in the extended -
real
sense, and the supremum of the empty set is - infinity. Show that C = D if and only if S_C = S_D,
meaning S_C(y) = S_D(y) for every y ∈ ℝ^n.
-/
theorem closed_convex_eq_iff_supportFunction_eq
    {n : ℕ} {C D : Set (EuclideanSpace ℝ (Fin n))}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) :
    C = D ↔ supportFunction C = supportFunction D := by
  constructor
  · intro hCD
    -- The forward implication is immediate by rewriting the set argument.
    subst hCD
    rfl
  · intro hEq
    -- Prove both inclusions using the projection argument, then conclude by antisymmetry.
    refine Set.Subset.antisymm
      (subset_of_supportFunction_eq hD_closed hD_convex hEq)
      ?_
    exact subset_of_supportFunction_eq hC_closed hC_convex hEq.symm
end «problem-64»
