import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-19»
/-
Given a proper cone K ⊆ ℝ^n, the generalized inequality ⪯_K is the relation on ℝ^n defined by x ⪯_K
y if and only if y - x ∈ K.
-/
def generalizedInequality {n : ℕ} (K : Set (Fin n → ℝ)) (x y : Fin n → ℝ) : Prop :=
  y - x ∈ K

/-
Let K ⊆ ℝ² be a closed convex cone. A cone is proper if it is pointed and has nonempty interior. For
a proper cone K, define the generalized inequality ⪯_K by x ⪯_K y if and only if y - x ∈ K. Prove
that K is proper if and only if K is a sector {(r cos φ, r sin φ) | r ≥ 0 and α ≤ φ ≤ β} for some α,
β satisfying 0 < β - α < π.
-/
theorem proper_cone_iff_eq_sector
    (K : Set (Fin 2 → ℝ))
    (h_closed : IsClosed K)
    (h_convex : Convex ℝ K)
    (h_cone : ∀ ⦃x : Fin 2 → ℝ⦄ ⦃a : ℝ⦄, x ∈ K → 0 ≤ a → a • x ∈ K) :
    (K ∩ (-K) = ({0} : Set (Fin 2 → ℝ)) ∧ Set.Nonempty (interior K)) ↔
      ∃ α β : ℝ,
        0 < β - α ∧
        β - α < Real.pi ∧
        K =
          {x : Fin 2 → ℝ |
            ∃ r : ℝ, ∃ φ : Set.Icc α β,
              x 0 = r * Real.cos φ ∧
              x 1 = r * Real.sin φ ∧
              0 ≤ r} := by
  sorry

/-
Let K ⊆ ℝ² be a closed convex cone, and define x ⪯_K y to mean y - x ∈ K. Prove that x ⪯_K y if and
only if y ∈ x + K.
-/
theorem generalizedInequality_iff_mem_translate
    (K : Set (Fin 2 → ℝ))
    (x y : Fin 2 → ℝ) :
    generalizedInequality K x y ↔ y ∈ ((fun z : Fin 2 → ℝ => x + z) '' K) := by
  sorry
end «problem-19»
