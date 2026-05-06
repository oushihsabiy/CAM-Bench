import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped MatrixOrder
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-100»

/- [BLOCK Exercise 3.37 | 18 | defn]
For a function f : ℝ^m → ℝ cup {+∞}, the convex conjugate f* : ℝ^m → ℝ cup {+∞} is defined by
f*(y) = sup_{x ∈ ℝ^m} (langle y, x rangle - f(x)).
-/
open scoped Real

def convexConjugate {m : ℕ} (f : (Fin m → ℝ) → EReal) : (Fin m → ℝ) → EReal :=
  fun y => sSup (Set.range fun x : Fin m → ℝ => ((∑ i, y i * x i : ℝ) : EReal) - f x)

/- [BLOCK Exercise 3.37 | 19 | thm]
Let S_{++}^n be the set of n × n real symmetric positive definite matrices, and let S_+^n be the set
of n × n real symmetric positive semidefinite matrices. Define f:ℝ^{n×n} → ℝ+∞ by f(X)=tr(X^{-1})
quad for X ∈ S_{++}^n, and f(X)=+∞ for X notin S_{++}^n. The convex conjugate of f is f*(Y)=sup_{X∈
ℝ^{n×n}} ≤ft(tr(YX)-f(X)). For A ∈ S_+^n, let A^{1/2} denote the unique symmetric positive
semidefinite square root of A. Show that f*(Y)=-2tr((-Y)^{1/2}) for Y ∈ -S_+^n, and that dom
f*=-S_+^n.
-/
theorem convexConjugate_trace_inv_eq_negTwo_trace_sqrt
    {n : Type} [Fintype n] [DecidableEq n] :
    (∀ Y : Matrix n n ℝ, ∀ hY : (-Y).IsSymm ∧ (-Y).PosSemidef,
      sSup (Set.range fun X : {X : Matrix n n ℝ // X.IsSymm ∧ X.PosDef} =>
        (((Matrix.trace (Y * X.1)) : ℝ) : EReal) -
          (((Matrix.trace (X.1⁻¹)) : ℝ) : EReal)) =
        (((-2 : ℝ) * Matrix.trace (CFC.sqrt (-Y))) : EReal)) ∧
    ({Y : Matrix n n ℝ |
      sSup (Set.range fun X : {X : Matrix n n ℝ // X.IsSymm ∧ X.PosDef} =>
        (((Matrix.trace (Y * X.1)) : ℝ) : EReal) -
          (((Matrix.trace (X.1⁻¹)) : ℝ) : EReal)) < ⊤} =
      {Y : Matrix n n ℝ | (-Y).IsSymm ∧ (-Y).PosSemidef}) := by
  sorry

end «problem-100»
