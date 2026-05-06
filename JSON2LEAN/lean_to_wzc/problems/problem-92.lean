import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-92»

/- [BLOCK Exercise 3.39-(d) | 24 | defn]
A function f : ℝ^n → ℝ ∪ {+∞} is a closed convex function if its epigraph is closed and convex.
-/
def IsClosedConvexFunction {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  IsClosed {p : (Fin n → ℝ) × ℝ | f p.1 ≤ (p.2 : EReal)} ∧
  Convex ℝ {p : (Fin n → ℝ) × ℝ | f p.1 ≤ (p.2 : EReal)}

/- [BLOCK Exercise 3.39-(d) | 26 | defn]
The convex conjugate of f : ℝ^n → ℝ cup {+∞} is the function f* : ℝ^n → ℝ cup {+∞} defined by
f*(y)=sup_x∈ ℝ^n(yᵀ x-f(x)).
-/
def convexConjugate {n : ℕ} (f : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun y => sSup {z : EReal | ∃ x : Fin n → ℝ, z = (∑ i, y i * x i : ℝ) - f x}

/- [BLOCK Exercise 3.39-(d) | 27 | defn]
The biconjugate of f is the convex conjugate of f*; equivalently, f** : ℝ^n → ℝ cup {+∞} is
defined by
f* * (x)=sup_y∈ ℝ^n(yᵀ x-f*(y)).
-/
def biconjugate {n : ℕ} (f : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  convexConjugate (convexConjugate f)

/- [BLOCK Exercise 3.39-(d) | 28 | thm]
Let f:ℝ^n → ℝ+∞ be a closed convex function, where closed means that epi(f)={(x,t)∈ ℝ^n× ℝ| f(x)≤ t}
is a closed subset of ℝ^n× ℝ. Define the convex conjugate f*:ℝ^n→ ℝ+∞ by f*(y)=sup_{x∈ ℝ^n}(yᵀ
x-f(x)), and define the biconjugate f^{ ** }:ℝ^n→ ℝ+∞ by f^{** }(x)=sup_{y∈ ℝ^n}(yᵀ x-f*(y)). Show
that
f=f^{**}.
-/
theorem closed_convex_function_eq_biconjugate {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hclosedConv : IsClosedConvexFunction f)
    (hnoBot : ∀ x, f x ≠ ⊥)
    (hproper : ∃ x, f x < ⊤) :
    f = biconjugate f := by
  sorry

end «problem-92»
