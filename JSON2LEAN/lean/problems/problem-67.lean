import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-67»

-- Exercise_3_49__d_

/- [BLOCK Exercise 3.49-(d) | 40 | defn]
A function f : C → ℝ_{++} on a convex set C is log-concave if log f is concave on C; equivalently,
for all x,y ∈ C and θ ∈ [0,1],
f(θ x+(1-θ)y) ≥ f(x)^θ f(y)^{1-θ}.
-/
def LogConcaveOn (C : Set ℝ) (f : ℝ → ℝ) : Prop :=
  Convex ℝ C ∧
    Set.MapsTo f C (Set.Ioi 0) ∧
      ∀ ⦃x y : ℝ⦄, x ∈ C → y ∈ C →
        ∀ ⦃θ : ℝ⦄, θ ∈ Set.Icc (0 : ℝ) 1 →
          f (θ * x + (1 - θ) * y) ≥ Real.rpow (f x) θ * Real.rpow (f y) (1 - θ)

/- [BLOCK Exercise 3.49-(d) | 41 | thm]
Let S_{++}^n denote the set of all n× n real symmetric positive definite matrices. For X∈ S_{++}^n,
define f(X)=det X{tr X}. Prove that f is log-concave on S_{++}^n; equivalently, prove that the
function X mapsto log det X-log(tr X) is concave on S_{++}^n.
-/
theorem det_div_trace_logConcaveOn_posDef
    (n : Type*) [Fintype n] [DecidableEq n] :
    ConcaveOn ℝ
      {X : Matrix n n ℝ | X.PosDef}
      (fun X : Matrix n n ℝ => Real.log (Matrix.det X) - Real.log (Matrix.trace X)) := by
  sorry

end «problem-67»