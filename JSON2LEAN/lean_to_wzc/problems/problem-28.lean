import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-28»
/-
A cone K ⊆ ℝ^n is called proper if it is convex, closed, pointed, and has nonempty interior, where
pointed means K cap (- K) = {0}.
-/
def IsProperCone {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  (0 ∈ K ∧ ∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x : Fin n → ℝ⦄, x ∈ K → a • x ∈ K) ∧
  Convex ℝ K ∧
  IsClosed K ∧
  K ∩ {x | -x ∈ K} = {0} ∧
  Set.Nonempty (interior K)

/-
Given a cone K ⊆ ℝ^n, the cone order induced by K is defined by x preceq_K y if and only if y - x ∈
K;
the strict cone order is defined by x prec_K y if and only if y - x ∈ int K.
-/
def StrictConeOrder {n : ℕ} (K : Set (Fin n → ℝ)) (x y : Fin n → ℝ) : Prop :=
  y - x ∈ interior K

/-
Let K ⊆ ℝ^n be a proper cone, with dual cone K* = {z∈ ℝ^n | zᵀ x ≥ 0 for all x∈ K}. Define the cone
orders by x preceq_K y Longleftrightarrow y - x ∈ K, x prec_K y Longleftrightarrow y - x ∈ int K,
where
int K is the interior of K. Let psi: - int K → ℝ be differentiable and concave, and assume that for
all x ∈ - int K and all s > 0, psi(sx) = psi(x) + log s. Suppose y prec_K 0. Show that -∇ psi(y) ∈
K*.
-/
open scoped Topology

theorem neg_gradient_mem_dualCone_of_concave_log_homogeneous
    {n : ℕ} (K : Set (Fin n → ℝ)) (hK : IsProperCone K) :
    ∀ (psi : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ),
      y ∈ -interior K →
      StrictConeOrder K y 0 →
      ConcaveOn ℝ (-interior K) psi →
      (∀ x : Fin n → ℝ, x ∈ -interior K → DifferentiableAt ℝ psi x) →
      (∀ x : Fin n → ℝ, x ∈ -interior K → ∀ s : ℝ, 0 < s → psi (s • x) = psi x + Real.log s) →
      ∀ x : Fin n → ℝ, x ∈ K → ∑ i, (fderiv ℝ psi y) (Pi.single i (1 : ℝ)) * x i ≤ 0 := by
  sorry

end «problem-28»
