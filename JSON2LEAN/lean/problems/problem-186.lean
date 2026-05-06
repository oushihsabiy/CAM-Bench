import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-186»

def SeparatingHyperplane (n : ℕ) (a : Fin n → ℝ) (b : ℝ)
    (C D : Set (Fin n → ℝ)) : Prop :=
  a ≠ 0 ∧
    (∀ x, x ∈ C → (∑ i, a i * x i) ≤ b) ∧
    (∀ y, y ∈ D → b ≤ (∑ i, a i * y i))

/-- Two disjoint convex sets admit a separating hyperplane. -/
theorem exists_separating_hyperplane_of_disjoint_convex
    (n : ℕ) (C D : Set (Fin n → ℝ))
    (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hdisj : Disjoint C D) :
    ∃ a : Fin n → ℝ, ∃ b : ℝ,
      SeparatingHyperplane n a b C D := by
  sorry

end «problem-186»
