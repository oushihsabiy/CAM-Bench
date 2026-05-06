import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-56»
def rec (C : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  { y | ∀ ⦃x⦄, x ∈ C → ∀ ⦃t : ℝ⦄, 0 ≤ t → x - t • y ∈ C }

def IsCone (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ ⦃y : EuclideanSpace ℝ (Fin n)⦄, y ∈ K → ∀ ⦃a : ℝ⦄, 0 ≤ a → a • y ∈ K

def IsConvexCone (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsCone (n := n) K ∧ Convex ℝ K

open scoped RealInnerProductSpace
def dualCone (B : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  { y | ∀ z, z ∈ B → 0 ≤ ⟪z, y⟫ }

def bar (C : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  { z | BddAbove (Set.image (fun x => ⟪z, x⟫) C) }

variable {n : ℕ}

/-- Normalizes the convex combination of two recession-shifted points into one shift. -/
lemma recession_combo_normalize
    (x y₁ y₂ : EuclideanSpace ℝ (Fin n)) (a b t : ℝ) (hab : a + b = 1) :
    a • (x - t • y₁) + b • (x - t • y₂) = x - t • (a • y₁ + b • y₂) := by
  -- Record the common-factor identity for the shifted recession directions.
  have hshift : a • (t • y₁) + b • (t • y₂) = t • (a • y₁ + b • y₂) := by
    -- Rewrite both sides into scalar multiples of `y₁` and `y₂` with the same outer scalar `t`.
    calc
      a • (t • y₁) + b • (t • y₂)
          = (a * t) • y₁ + (b * t) • y₂ := by simp [smul_smul]
      _ = (t * a) • y₁ + (t * b) • y₂ := by rw [mul_comm a t, mul_comm b t]
      _ = t • (a • y₁) + t • (b • y₂) := by simp [smul_smul]
      _ = t • (a • y₁ + b • y₂) := by rw [smul_add]
  -- First expand the convex combination into separate `x` and `y` contributions.
  calc
    a • (x - t • y₁) + b • (x - t • y₂)
        = (a • x - a • (t • y₁)) + (b • x - b • (t • y₂)) := by
            rw [smul_sub, smul_sub]
    _ = (a • x + b • x) - (a • (t • y₁) + b • (t • y₂)) := by
          -- Reassociate the additive terms so both positive and negative parts combine.
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = x - (a • (t • y₁) + b • (t • y₂)) := by
          -- The coefficients of `x` collapse because they form a convex combination.
          rw [← add_smul, hab, one_smul]
    _ = x - t • (a • y₁ + b • y₂) := by
          -- Pull the common shift `t` back outside the linear combination.
          rw [hshift]

/- - The recession directions of a convex set form a convex cone. -/
theorem rec_isConvexCone_of_convex {C: Set (EuclideanSpace ℝ (Fin n))} (hC: Convex ℝ C):
    IsConvexCone (n:= n) (rec (n:= n) C) := by
  rw [IsConvexCone, IsCone]
  constructor
  · -- Recession directions stay in the recession cone after nonnegative scaling.
    intro y hy a ha
    intro x hx t ht
    -- Evaluate the recession condition for `y` at the larger time `t * a`.
    have hta : 0 ≤ t * a := mul_nonneg ht ha
    simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using
      (hy hx (t := t * a) hta)
  · -- Convexity follows by applying convexity of `C` to two shifted points in `C`.
    rw [convex_iff_add_mem] at hC ⊢
    intro y₁ hy₁ y₂ hy₂ a b ha hb hab
    intro x hx t ht
    -- Each recession direction keeps `x` inside `C` after shifting by `t`.
    have hy₁t : x - t • y₁ ∈ C := hy₁ hx ht
    have hy₂t : x - t • y₂ ∈ C := hy₂ hx ht
    -- Combine the two shifted points using the convex-combination characterization.
    have hxy : a • (x - t • y₁) + b • (x - t • y₂) ∈ C :=
      hC hy₁t hy₂t ha hb hab
    -- Normalize the affine combination to the recession form for `a • y₁ + b • y₂`.
    rw [recession_combo_normalize x y₁ y₂ a b t hab] at hxy
    exact hxy

/-
For a nonempty closed convex set, the recession cone is the dual of the barrier cone. -/
/-- A recession direction pairs nonnegatively with every vector in the barrier cone. -/
lemma rec_subset_dualCone_bar_of_nonempty {C : Set (EuclideanSpace ℝ (Fin n))}
    (hCne : C.Nonempty) :
    rec (n := n) C ⊆ dualCone (n := n) (bar (n := n) C) := by
  intro y hy
  -- Unpack the recession condition once so it can be reused at the chosen base point.
  have hyrec : ∀ ⦃x : EuclideanSpace ℝ (Fin n)⦄, x ∈ C → ∀ ⦃t : ℝ⦄, 0 ≤ t → x - t • y ∈ C := by
    simpa [rec] using hy
  intro z hz
  rcases hCne with ⟨x₀, hx₀⟩
  rcases hz with ⟨M, hM⟩
  -- Evaluate the barrier bound at the chosen base point.
  have hx₀bound : ⟪z, x₀⟫ ≤ M := by
    apply hM
    exact ⟨x₀, hx₀, rfl⟩
  -- If the pairing were negative, the recession ray would force unbounded growth.
  by_contra hnonneg
  have hneg : ⟪z, y⟫ < 0 := lt_of_not_ge hnonneg
  have hden : 0 < -⟪z, y⟫ := by
    linarith
  have hnum : 0 < M - ⟪z, x₀⟫ + 1 := by
    linarith
  set t : ℝ := (M - ⟪z, x₀⟫ + 1) / (-⟪z, y⟫) with ht_def
  have ht : 0 ≤ t := by
    rw [ht_def]
    exact le_of_lt (div_pos hnum hden)
  -- Move along the recession ray and apply the barrier upper bound at that new point.
  have hxt : x₀ - t • y ∈ C := hyrec hx₀ ht
  have hbound : ⟪z, x₀ - t • y⟫ ≤ M := by
    apply hM
    exact ⟨x₀ - t • y, hxt, rfl⟩
  -- Rewrite the inner product along the ray into a positive increment.
  have hrewrite : ⟪z, x₀ - t • y⟫ = ⟪z, x₀⟫ + t * (-⟪z, y⟫) := by
    calc
      ⟪z, x₀ - t • y⟫ = ⟪z, x₀⟫ - ⟪z, t • y⟫ := by
        rw [inner_sub_right]
      _ = ⟪z, x₀⟫ - t * ⟪z, y⟫ := by
        rw [inner_smul_right]
      _ = ⟪z, x₀⟫ + t * (-⟪z, y⟫) := by
        ring
  have hden_ne : -⟪z, y⟫ ≠ 0 := by
    linarith
  have hscale : t * (-⟪z, y⟫) = M - ⟪z, x₀⟫ + 1 := by
    calc
      t * (-⟪z, y⟫) = ((M - ⟪z, x₀⟫ + 1) / (-⟪z, y⟫)) * (-⟪z, y⟫) := by
        rw [ht_def]
      _ = M - ⟪z, x₀⟫ + 1 := by
        exact div_mul_cancel₀ _ hden_ne
  rw [hrewrite, hscale] at hbound
  linarith

/-- A strict separating functional gives a vector in the barrier cone via the Riesz map. -/
lemma separator_vector_mem_bar_of_strict_upper_bound
    {C : Set (EuclideanSpace ℝ (Fin n))}
    {l : StrongDual ℝ (EuclideanSpace ℝ (Fin n))} {s : ℝ}
    (hs : ∀ a ∈ C, l a < s) :
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm l ∈ bar (n := n) C := by
  -- Use the separator threshold itself as a global upper bound on the image set.
  refine ⟨s, ?_⟩
  intro r hr
  rcases hr with ⟨a, haC, rfl⟩
  -- Convert the separating functional back into an inner product coordinate.
  simpa using le_of_lt (hs a haC)

/-- If a vector is not in the recession cone, a barrier-cone witness sees it negatively. -/
lemma exists_mem_bar_inner_lt_zero_of_not_mem_rec
    {C : Set (EuclideanSpace ℝ (Fin n))}
    (hCcl : IsClosed C) (hC : Convex ℝ C)
    {y : EuclideanSpace ℝ (Fin n)} (hnot : y ∉ rec (n := n) C) :
    ∃ z, z ∈ bar (n := n) C ∧ ⟪z, y⟫ < 0 := by
  -- Route correction: separate the offending point `x - t • y` from `C` directly.
  have hnot' : ∃ x, x ∈ C ∧ ∃ t : ℝ, 0 ≤ t ∧ x - t • y ∉ C := by
    simpa [rec] using hnot
  rcases hnot' with ⟨x, hx, t, ht, hnotin⟩
  have htpos : 0 < t := by
    by_contra hnotpos
    have ht_zero : t = 0 := by
      linarith
    apply hnotin
    simpa [ht_zero] using hx
  set u : EuclideanSpace ℝ (Fin n) := x - t • y with hu_def
  have hu_notin : u ∉ C := by
    simpa [hu_def] using hnotin
  -- Separate the outside point from the closed convex set.
  obtain ⟨l, s, hsC, hsu⟩ :=
    geometric_hahn_banach_closed_point (s := C) (x := u) hC hCcl hu_notin
  set z : EuclideanSpace ℝ (Fin n) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm l with hz_def
  have hz_apply : ∀ w : EuclideanSpace ℝ (Fin n), ⟪z, w⟫ = l w := by
    intro w
    simpa [hz_def] using (InnerProductSpace.toDual_symm_apply (x := w) (y := l))
  -- The separator is automatically bounded above on `C`, so its Riesz vector lies in `bar C`.
  have hzbar_raw :
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm l ∈ bar (n := n) C :=
    separator_vector_mem_bar_of_strict_upper_bound (n := n) hsC
  have hzbar : z ∈ bar (n := n) C := by
    simpa [hz_def] using hzbar_raw
  have hlx : l x < s := hsC x hx
  -- Rewrite the separating inequality at `u = x - t • y` into a sign condition on `⟪z, y⟫`.
  have hu_eval : l u = l x + t * (-⟪z, y⟫) := by
    calc
      l u = l (x - t • y) := by
        rw [hu_def]
      _ = l x - l (t • y) := by
        rw [map_sub]
      _ = l x - t * l y := by
        simp
      _ = l x - t * ⟪z, y⟫ := by
        rw [← hz_apply y]
      _ = l x + t * (-⟪z, y⟫) := by
        ring
  have hsep : s < l x + t * (-⟪z, y⟫) := by
    rw [← hu_eval]
    exact hsu
  have hprod : 0 < t * (-⟪z, y⟫) := by
    linarith
  have hpos : 0 < -⟪z, y⟫ := by
    have hprod' : 0 < (-⟪z, y⟫) * t := by
      simpa [mul_comm] using hprod
    exact pos_of_mul_pos_left hprod' htpos.le
  have hneg : ⟪z, y⟫ < 0 := by
    linarith
  exact ⟨z, hzbar, hneg⟩

theorem rec_eq_dualCone_bar_of_nonempty_closed_convex {C: Set (EuclideanSpace ℝ (Fin n))}
    (hCne : C.Nonempty) (hCcl: IsClosed C) (hC: Convex ℝ C):
    rec (n:= n) C = dualCone (n:= n) (bar (n:= n) C) := by
  apply Set.Subset.antisymm
  · -- The easy direction is the bounded-ray argument proved above.
    exact rec_subset_dualCone_bar_of_nonempty (n := n) hCne
  · intro y hy
    -- Unpack dual-cone membership into the nonnegative inner-product condition.
    have hydual : ∀ z, z ∈ bar (n := n) C → 0 ≤ ⟪z, y⟫ := by
      simpa [dualCone] using hy
    by_contra hnot
    -- A failure of recession produces a barrier witness with negative pairing.
    obtain ⟨z, hzbar, hneg⟩ :=
      exists_mem_bar_inner_lt_zero_of_not_mem_rec (n := n) hCcl hC hnot
    exact not_lt_of_ge (hydual z hzbar) hneg
end «problem-56»
