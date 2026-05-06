import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-49»
/-
Let 0 < p < 1. Define the function f: ℝ_{++}^n o ℝ by f(x) = (sum_{i = 1}^n xᵢ^p ight)^{1/p}, where
ℝ_{++}^n = {x = (x₁,..., xₙ)∈ ℝ^n: xᵢ > 0, i = 1,..., n}. Using the second-order criterion for
concavity of differentiable functions, prove that f is concave on ℝ_{++}^n.
-/
open scoped BigOperators

theorem lp_quasinorm_concave_on_positive_orthant
    {n : ℕ} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    ConcaveOn ℝ {x : Fin n → ℝ | ∀ i, 0 < x i}
      (fun x => Real.rpow (∑ i, Real.rpow (x i) p) (1 / p)) := by
  sorry


theorem convexOn_spd_pos_log_det_perspective
    (n : ℕ) :
    ConvexOn ℝ
      { p : Matrix (Fin n) (Fin n) ℝ × ℝ |
          p.1.PosDef ∧ 0 < p.2 }
      (fun p =>
        (n : ℝ) * p.2 * Real.log p.2 - p.2 * Real.log (Matrix.det p.1)) := by
  sorry

/- [BLOCK Exercise 2.6 | 8 | thm]
Let S_{++}^n denote the set of n × n real symmetric positive definite matrices, and let ℝ_{++} = { t
∈ ℝ | t > 0 }. For X ∈ S_{++}^n, let det X denote the determinant of X, tr X denote the trace of X,
and log denote the natural logarithm. Also show that the function
g(X)=n(trX)log(trX)-(trX)(logdet X)
is convex on S_{++}^n.
-/

theorem convexOn_spd_trace_log_det
    (n : ℕ) :
    ConvexOn ℝ
      { X : Matrix (Fin n) (Fin n) ℝ | X.PosDef }
      (fun X =>
        (n : ℝ) * Matrix.trace X * Real.log (Matrix.trace X) -
          Matrix.trace X * Real.log (Matrix.det X)) := by
  sorry
end «problem-49»
