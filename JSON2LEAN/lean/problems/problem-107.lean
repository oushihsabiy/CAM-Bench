import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-107»
/-
Let x_[1] ≥ x_[2] ≥ ··· ≥ x_[n] be the nonincreasing rearrangement of the components of x ∈ ℝ^n, and
let α₁ ≥ α₂ ≥ ··· ≥ α_n ≥ 0. Define f(x) = ∑_{i = 1}^n α_i x_[i]. Prove that f is convex on ℝ^n.
-/
theorem weighted_sorted_sum_convexOn
    (n : ℕ) (α : Fin n → ℝ)
    (hα_mono : Antitone α)
    (hα_nonneg : ∀ i : Fin n, 0 ≤ α i) :
    ConvexOn ℝ Set.univ
      (fun x : EuclideanSpace ℝ (Fin n) =>
        sSup {r : ℝ | ∃ σ : Equiv.Perm (Fin n), r = ∑ i : Fin n, α i * x (σ i)}) := by
  sorry

end «problem-107»