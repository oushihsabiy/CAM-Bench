import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-116»
/- [BLOCK Exercise 2.31-(b) | 49 | defn]
For a function g:ℝ^n	oℝ+∞, its convex conjugate is defined by
g*(y)=sup_{x∈ℝ^n}{yᵀ x-g(x)}, y∈ℝ^n.
For a function h:ℝ	oℝ+∞,
h*(s)=sup_{t∈ℝ}{st-h(t)}, s∈ℝ.
-/
open scoped BigOperators

def convexConjugate {n : ℕ} (g : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun y => sSup {r | ∃ x : Fin n → ℝ, r = (∑ i, y i * x i) - g x}

def scalarConvexConjugate (h : ℝ → EReal) : ℝ → EReal :=
  fun s => sSup {r | ∃ t : ℝ, r = (s * t : ℝ) - h t}

/- [BLOCK Exercise 2.31-(b) | 50 | thm]
Let n ∈ ℕ. Let h:ℝ oℝ be convex and nondecreasing with dom h=ℝ, and assume h(t)=h(0) quad ext{for
all } t ≤ 0. Define f:ℝ^n oℝ by f(x)=h(‖x‖_2), where ‖x‖_2 is the Euclidean norm on ℝ^n. For g:ℝ^n
oℝ+∞, define its convex conjugate by g*(y)=sup_{x∈ℝ^n}igl(yᵀ x-g(x)igr), y∈ℝ^n. For h:ℝ oℝ, define
its convex conjugate by h*(s)=sup_{t∈ℝ}igl(st-h(t)igr), s∈ℝ. Show that the conjugate of f is
f*(y)=h*(‖y‖_2).
-/
theorem convexConjugate_radial_eq_scalarConvexConjugate_norm
    {n : ℕ} (h : ℝ → ℝ)
    (h_convex : ConvexOn ℝ Set.univ h)
    (h_monotone : Monotone h)
    (h_nonpos_const : ∀ t : ℝ, t ≤ 0 → h t = h 0) :
    convexConjugate
        (fun x : Fin n → ℝ => (h (Real.sqrt (dotProduct x x)) : EReal)) =
      fun y : Fin n → ℝ =>
        scalarConvexConjugate (fun t => (h t : EReal)) (Real.sqrt (dotProduct y y)) := by
  sorry

end «problem-116»
