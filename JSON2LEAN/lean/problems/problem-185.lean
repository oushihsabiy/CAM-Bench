import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-185»

/- [BLOCK Exercise 2.10 | 11 | defn]
Given weights α_1,dots,α_n ≥ 0, the weighted geometric mean on ℝ_{++}^n is the function
f(x)=prod_{k=1}^n xₖ^{α_k}.
-/
def weightedGeometricMean (n : ℕ) (α x : Fin n → ℝ) : ℝ :=
  ∏ k, Real.rpow (x k) (α k)

/- [BLOCK Exercise 2.10 | 12 | thm]
Let n ∈ ℕ, and let α_1,dots,α_n ∈ ℝ satisfy α_k ≥ 0 for k=1,dots,n and sum_{k=1}^n α_k ≤ 1. Define f
: ℝ_{++}^n o ℝ by f(x₁,dots,xₙ)=prod_{k=1}^n xₖ^{α_k}, where ℝ_{++}^n={x=(x₁,dots,xₙ)∈ ℝ^n | xₖ>0
ext{ for } k=1,dots,n}. Show that the weighted geometric mean f is concave on ℝ_{++}^n.
-/
theorem weightedGeometricMean_concaveOn_pos
    (n : ℕ) (α : Fin n → ℝ)
    (hα_nonneg : ∀ k, 0 ≤ α k)
    (hα_sum : ∑ k, α k ≤ 1) :
    ConcaveOn ℝ {x : Fin n → ℝ | ∀ k, 0 < x k} (weightedGeometricMean n α) := by
  sorry

end «problem-185»
