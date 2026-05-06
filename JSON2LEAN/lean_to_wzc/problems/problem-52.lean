import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-52»
/-
Let f: ℝ^n times ℝ^m o ℝ be differentiable, and suppose that for any fixed z ∈ ℝ^m, the mapping x
mapsto f(x, z) is convex on ℝ^n, and for any fixed x ∈ ℝ^n, the mapping z mapsto f(x, z) is concave
on ℝ^m. That is, f is a convex--concave function with respect to (x, z). It is known that there
exists (ar x, ar z) ∈ ℝ^n times ℝ^m such that abla f(ar x, ar z) = 0, where abla f(ar x, ar z)
denotes the ∇of f with respect to all variables (x, z). Prove that (ar x, ar z) is a saddle point
of f, that is, for any x ∈ ℝ^n and any z ∈ ℝ^m, we have f(ar x, z) ≤ f(ar x, ar z) ≤ f(x, ar z).
-/
open scoped BigOperators

theorem convex_concave_gradient_zero_is_saddle_point
    {n m : ℕ}
    {f : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → ℝ}
    {xBar : EuclideanSpace ℝ (Fin n)}
    {zBar : EuclideanSpace ℝ (Fin m)}
    (hconv :
      ∀ z : EuclideanSpace ℝ (Fin m),
        ConvexOn ℝ Set.univ (fun x : EuclideanSpace ℝ (Fin n) => f (x, z)))
    (hconc :
      ∀ x : EuclideanSpace ℝ (Fin n),
        ConcaveOn ℝ Set.univ (fun z : EuclideanSpace ℝ (Fin m) => f (x, z)))
    (hdiff : DifferentiableAt ℝ f (xBar, zBar))
    (hgrad : fderiv ℝ f (xBar, zBar) = 0) :
    ∀ x : EuclideanSpace ℝ (Fin n), ∀ z : EuclideanSpace ℝ (Fin m),
      f (xBar, z) ≤ f (xBar, zBar) ∧ f (xBar, zBar) ≤ f (x, zBar) := by
  sorry

/-
Let f: ℝ^n times ℝ^m o ℝ be differentiable, and suppose that for any fixed z ∈ ℝ^m, the mapping x
mapsto f(x, z) is convex on ℝ^n, and for any fixed x ∈ ℝ^n, the mapping z mapsto f(x, z) is concave
on ℝ^m. That is, f is a convex--concave function with respect to (x, z). It is known that there
exists (ar x, ar z) ∈ ℝ^n times ℝ^m such that abla f(ar x, ar z) = 0, where abla f(ar x, ar z)
denotes the ∇of f with respect to all variables (x, z). Assume additionally that for every
fixed x the set of values {f(x, z) | z ∈ ℝ^m} is bounded above, and for every fixed z the
set of values {f(x, z) | x ∈ ℝ^n} is bounded below, so that the real-valued `sSup` and
`sInf` below are meaningful. Prove that f satisfies the minimax relation
min_{x ∈ ℝ^n} sup_{z ∈ ℝ^m} f(x, z) = sup_{z ∈ ℝ^m} inf_{x ∈ ℝ^n} f(x, z).
-/
theorem convex_concave_gradient_zero_implies_minimax
    {n m : ℕ}
    {f : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → ℝ}
    (hdiff : Differentiable ℝ f)
    (hconv :
      ∀ z : EuclideanSpace ℝ (Fin m),
        ConvexOn ℝ Set.univ (fun x : EuclideanSpace ℝ (Fin n) => f (x, z)))
    (hconc :
      ∀ x : EuclideanSpace ℝ (Fin n),
        ConcaveOn ℝ Set.univ (fun z : EuclideanSpace ℝ (Fin m) => f (x, z)))
    (hex :
      ∃ xBar : EuclideanSpace ℝ (Fin n), ∃ zBar : EuclideanSpace ℝ (Fin m),
        fderiv ℝ f (xBar, zBar) = 0)
    (hbounded_sup :
      ∀ x : EuclideanSpace ℝ (Fin n),
        BddAbove (Set.range fun z : EuclideanSpace ℝ (Fin m) => f (x, z)))
    (hbounded_inf :
      ∀ z : EuclideanSpace ℝ (Fin m),
        BddBelow (Set.range fun x : EuclideanSpace ℝ (Fin n) => f (x, z))) :
    sInf (Set.range fun x : EuclideanSpace ℝ (Fin n) =>
      sSup (Set.range fun z : EuclideanSpace ℝ (Fin m) => f (x, z))) =
    sSup (Set.range fun z : EuclideanSpace ℝ (Fin m) =>
      sInf (Set.range fun x : EuclideanSpace ℝ (Fin n) => f (x, z))) := by
  sorry

end «problem-52»
