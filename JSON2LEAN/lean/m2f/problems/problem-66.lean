import Mathlib

noncomputable section
open scoped Topology
open scoped Pointwise
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-66»
def IsConvexCone {n: ℕ} (C: Set (Fin n → ℝ)): Prop :=
  Convex ℝ C ∧
    (∀ ⦃x: Fin n → ℝ⦄, x ∈ C → ∀ ⦃α: ℝ⦄, 0 ≤ α → α • x ∈ C)

def DualCone {n: ℕ} (C: Set (Fin n → ℝ)): Set (Fin n → ℝ) :=
  {y | ∀ ⦃x: Fin n → ℝ⦄, x ∈ C → 0 ≤ (∑ i, y i * x i)}

open scoped BigOperators

/-- Positive scaling preserves interior points of a convex cone. -/
lemma smul_mem_interior_of_IsConvexCone {n : ℕ} {C : Set (Fin n → ℝ)}
    (hC : IsConvexCone (n := n) C) {x : Fin n → ℝ} (hx : x ∈ interior C) {α : ℝ}
    (hα : 0 < α) : α • x ∈ interior C := by
  rcases hC with ⟨_hconv, hsmul⟩
  -- Route correction: use `interior_smul₀` plus monotonicity of interior, rather than rebuilding
  -- the topology of the cone interior from scratch.
  have hsmul_subset : α • C ⊆ C := by
    rintro z ⟨y, hy, rfl⟩
    exact hsmul hy hα.le
  have hmem : α • x ∈ interior (α • C) := by
    rw [interior_smul₀ hα.ne' C]
    exact ⟨x, hx, rfl⟩
  exact interior_mono hsmul_subset hmem

/-- A strict upper separator on the interior of a convex cone is nonpositive on the whole cone. -/
lemma nonpos_on_cone_of_strict_upper_sep {n : ℕ} {C : Set (Fin n → ℝ)}
    (hC : IsConvexCone (n := n) C) (hCint_nonempty : (interior C).Nonempty)
    {f : StrongDual ℝ (Fin n → ℝ)} {u : ℝ} (hf : ∀ x ∈ interior C, f x < u) :
    ∀ x ∈ C, f x ≤ 0 := by
  rcases hC with ⟨hconv, hsmul⟩
  have hnonpos_int : ∀ x ∈ interior C, f x ≤ 0 := by
    intro x hx
    by_contra hfx_nonpos
    have hfx_pos : 0 < f x := lt_of_not_ge hfx_nonpos
    -- Scale an interior point far enough so the strict bound `f (α • x) < u` becomes impossible.
    obtain ⟨m, hm⟩ := exists_nat_gt (u / f x)
    let α : ℝ := m + 1
    have hα_pos : 0 < α := by
      dsimp [α]
      positivity
    have hα_gt : u / f x < α := by
      dsimp [α]
      exact lt_trans hm (by exact_mod_cast Nat.lt_succ_self m)
    have hu_lt : u < α * f x := by
      rw [div_lt_iff₀ hfx_pos] at hα_gt
      exact hα_gt
    have hsep := hf (α • x) (smul_mem_interior_of_IsConvexCone ⟨hconv, hsmul⟩ hx hα_pos)
    have hmap : f (α • x) = α * f x := by
      simp [α]
    linarith
  have hclosed : IsClosed {z : Fin n → ℝ | f z ≤ 0} :=
    isClosed_Iic.preimage f.continuous
  have hint_subset : interior C ⊆ {z : Fin n → ℝ | f z ≤ 0} := by
    intro z hz
    exact hnonpos_int z hz
  have hclosure_subset : closure (interior C) ⊆ {z : Fin n → ℝ | f z ≤ 0} :=
    closure_minimal hint_subset hclosed
  intro x hx
  -- Pass from the interior to the whole cone through the closure identity for convex sets.
  have hx_closure : x ∈ closure (interior C) := by
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior hCint_nonempty]
    exact subset_closure hx
  exact hclosure_subset hx_closure

/-- A continuous linear functional on `Fin n → ℝ` is the dot product with its values on the
standard basis. -/
lemma functional_coordinates_fin {n : ℕ} (g : StrongDual ℝ (Fin n → ℝ)) :
    ∀ x : Fin n → ℝ, g x = ∑ i, x i * g ((Pi.basisFun ℝ (Fin n)) i) := by
  intro x
  let b := Pi.basisFun ℝ (Fin n)
  -- Expand `x` in the standard basis and use linearity to evaluate `g` termwise.
  have hx_basis : g x = g (∑ i, b.repr x i • b i) := by
    simpa [b] using congrArg g (b.sum_repr x).symm
  have hsum : g (∑ i, b.repr x i • b i) = ∑ i, b.repr x i * g (b i) := by
    rw [map_sum]
    simp [smul_eq_mul]
  rw [hx_basis]
  simp [b] at hsum ⊢

/-- Strict separation of two nonempty sets forces the separating functional to be nonzero. -/
lemma strict_separator_ne_zero {n : ℕ} {s t : Set (Fin n → ℝ)} (hs : s.Nonempty) (ht : t.Nonempty)
    {f : StrongDual ℝ (Fin n → ℝ)} {u : ℝ} (hf : ∀ a ∈ s, f a < u)
    (hg : ∀ b ∈ t, u < f b) : f ≠ 0 := by
  intro hzero
  rcases hs with ⟨a, ha⟩
  rcases ht with ⟨b, hb⟩
  -- If `f = 0`, the two strict inequalities force the impossible chain `0 < u < 0`.
  have ha' := hf a ha
  have hb' := hg b hb
  simp [hzero] at ha' hb'
  linarith

/-
- Disjoint interiors yield a nonzero vector lying in one dual cone and whose negation lies in the
other.
-/
theorem exists_nonzero_mem_dualCone_and_neg_mem_dualCone_of_disjoint_interiors
    {n : ℕ} {K Ktilde : Set (Fin n → ℝ)}
    (hK : IsConvexCone (n := n) K)
    (hKtilde : IsConvexCone (n := n) Ktilde)
    (hKint_nonempty : (interior K).Nonempty)
    (hKtildeint_nonempty : (interior Ktilde).Nonempty)
    (hdisj : Disjoint (interior K) (interior Ktilde)) :
    ∃ y : Fin n → ℝ, y ≠ 0 ∧ y ∈ DualCone (n := n) K ∧ (-y) ∈ DualCone (n := n) Ktilde := by
  rcases hK with ⟨hKconv, hKsmul⟩
  rcases hKtilde with ⟨hKtildeconv, hKtildesmul⟩
  -- First separate the two open interiors by a continuous linear functional.
  obtain ⟨f, u, hfK, hfKtilde⟩ :=
    geometric_hahn_banach_open_open (s := interior K) (t := interior Ktilde)
      (hKconv.interior) isOpen_interior (hKtildeconv.interior) isOpen_interior hdisj
  let g : StrongDual ℝ (Fin n → ℝ) := -f
  let y : Fin n → ℝ := fun i ↦ g ((Pi.basisFun ℝ (Fin n)) i)
  have hf_nonpos_K : ∀ x ∈ K, f x ≤ 0 := by
    exact nonpos_on_cone_of_strict_upper_sep ⟨hKconv, hKsmul⟩ hKint_nonempty (f := f) (u := u) hfK
  have hg_ne_zero : g ≠ 0 := by
    -- Negating the strict separator keeps it nonzero.
    have hf_ne_zero : f ≠ 0 := strict_separator_ne_zero hKint_nonempty hKtildeint_nonempty hfK hfKtilde
    simpa [g] using neg_ne_zero.mpr hf_ne_zero
  have hgK : ∀ x ∈ K, 0 ≤ g x := by
    -- On `K`, the original separator is nonpositive, so its negation is nonnegative.
    intro x hx
    simpa [g] using neg_nonneg.mpr (hf_nonpos_K x hx)
  have hgKtilde : ∀ x ∈ Ktilde, g x ≤ 0 := by
    -- On `Ktilde`, the negated separator has the strict upper bound needed by the cone lemma.
    refine nonpos_on_cone_of_strict_upper_sep ⟨hKtildeconv, hKtildesmul⟩ hKtildeint_nonempty
      (f := g) (u := -u) ?_
    intro x hx
    simpa [g] using neg_lt_neg (hfKtilde x hx)
  have hcoords : ∀ x : Fin n → ℝ, g x = ∑ i, x i * y i := by
    intro x
    simpa [y] using functional_coordinates_fin g x
  have hcoords_symm : ∀ x : Fin n → ℝ, ∑ i, y i * x i = g x := by
    intro x
    rw [hcoords x]
    simp_rw [mul_comm]
  have hcoords_neg : ∀ x : Fin n → ℝ, ∑ i, (-y) i * x i = -g x := by
    intro x
    calc
      ∑ i, (-y) i * x i = ∑ i, -(y i * x i) := by
        simp
      _ = -∑ i, y i * x i := by
        rw [Finset.sum_neg_distrib]
      _ = -g x := by
        rw [hcoords_symm x]
  have hy_ne_zero : y ≠ 0 := by
    intro hy_zero
    apply hg_ne_zero
    ext x
    -- If all coordinates of `y` vanish, then the coordinate formula forces `g = 0`.
    rw [hcoords x, hy_zero]
    simp
  refine ⟨y, hy_ne_zero, ?_, ?_⟩
  · intro x hx
    -- Rewrite the separator inequality in coordinates to obtain dual-cone membership.
    rw [hcoords_symm x]
    exact hgK x hx
  · intro x hx
    -- The same coordinate rewrite proves membership in the dual cone of `Ktilde`.
    rw [hcoords_neg x]
    exact neg_nonneg.mpr (hgKtilde x hx)
end «problem-66»
