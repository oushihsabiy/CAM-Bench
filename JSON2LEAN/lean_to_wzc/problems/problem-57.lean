import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-57»

-- Exercise_3_20__c_

/- [BLOCK Exercise 3.20-(c) | 10 | thm]
Let m,n ∈ ℕ, and let Aᵢ ∈ S^m for i=0,1,dots,n, where S^m is the set of real symmetric m imes m
matrices. Define X(x)=A₀+x₁A_1+·s+x_nA_n, x=(x₁,dots,xₙ)∈ ℝ^n, and define f(x)=trigl(X(x)^{-1}igr)
on the domain dom f={x∈ ℝ^n | X(x)succ 0}, where X(x)succ 0 means that X(x) is positive definite. A
function g on a convex set C⊆ ℝ^n is convex if for all x,y∈ C and all heta∈[0,1], one has g( heta
x+(1- heta)y)≤ heta g(x)+(1- heta)g(y). Prove that f is convex on dom f.
-/
open Matrix

theorem trace_inv_matrix_affine_convexOn
    {m n : ℕ}
    (A : Fin (n + 1) → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ i, IsSymm (A i)) :
    let domf : Set (Fin n → ℝ) := {x : Fin n → ℝ | PosDef (A 0 + ∑ i : Fin n, (x i) • A i.succ)}
    let f : (Fin n → ℝ) → ℝ :=
      fun x => Matrix.trace ((A 0 + ∑ i : Fin n, (x i) • A i.succ)⁻¹)
    ConvexOn ℝ domf f := by
  sorry

end «problem-57»