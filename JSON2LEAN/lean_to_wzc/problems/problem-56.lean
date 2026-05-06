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

/- - The recession directions of a convex set form a convex cone. -/
theorem rec_isConvexCone_of_convex {C: Set (EuclideanSpace ℝ (Fin n))} (hC: Convex ℝ C):
    IsConvexCone (n:= n) (rec (n:= n) C) := by
  sorry

/-
For a nonempty closed convex set, the recession cone is the dual of the barrier cone. -/
theorem rec_eq_dualCone_bar_of_nonempty_closed_convex {C: Set (EuclideanSpace ℝ (Fin n))}
    (hCne : C.Nonempty) (hCcl: IsClosed C) (hC: Convex ℝ C):
    rec (n:= n) C = dualCone (n:= n) (bar (n:= n) C) := by
  sorry
end «problem-56»