import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-190»

/- [BLOCK Exercise 3.28-(b) | 26 | defn]
The epigraph of a function f : ℝ^n → ℝ cup {∞} is
epi f = {(x,t) ∈ ℝ^n × ℝ | f(x) ≤ t}.
-/
def epigraph {n : ℕ} (f : (Fin n → ℝ) → WithTop ℝ) : Set ((Fin n → ℝ) × ℝ) :=
  { p | f p.1 ≤ p.2 }

/- [BLOCK Exercise 3.28-(b) | 27 | thm]
Let f:ℝ^n → ℝ∞ be a convex function, and define bar f:ℝ^n → ℝ∞ by bar f(x)=sup{g(x)| g:ℝ^n→ℝ is
affine and g(z)≤ f(z) for all z∈ℝ^n}, where an affine function has the form g(x)=aᵀ x+b for some
a∈ℝ^n and b∈ℝ. The epigraph of f is epi f={(x,t)∈ℝ^n×ℝ| f(x)≤ t}. The function f is called closed if
epi f is a closed subset of ℝ^n×ℝ. Show that f=bar f if f is closed.
-/
theorem closed_convex_eq_sup_affine_minorants
    {n : ℕ} (f : (Fin n → ℝ) → WithTop ℝ)
    (hconv : Convex ℝ (epigraph f))
    (hclosed : IsClosed (epigraph f)) :
    f =
      fun x =>
        sSup {r : WithTop ℝ |
          ∃ a : Fin n → ℝ, ∃ b : ℝ,
            (∀ z : Fin n → ℝ, (((∑ i, a i * z i) + b : ℝ) : WithTop ℝ) ≤ f z) ∧
            r = (((∑ i, a i * x i) + b : ℝ) : WithTop ℝ)} := by
  sorry

end «problem-190»
