import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-39»
/- [BLOCK Exercise 3.33-(b) | 34 | thm]
Let S^n be the vector space of real symmetric n × n matrices, and write X succeq 0 when X is
positive semidefinite. Consider the feasible set F={X∈ S^n : tr(A_iX)=bᵢ for i=1,ldots,m, Xsucceq
0}, where A₁,ldots,Aₘ∈ S^n and b₁,ldots,bₘ∈ ℝ. A matrix hat X∈ F is an extreme point of F if the
only matrix V∈ S^n such that tr(A_iV)=0 quad for i=1,ldots,m, hat X+Vsucceq 0, hat X-Vsucceq 0 is
V=0. Let hat X∈ F and let r=rank(hat X). Show that if (r(r+1))/(2)>m, then hat X is not an extreme
point of F.
-/
open Matrix

theorem not_extremePoint_of_rank_condition
    {n m : ℕ}
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (Xhat : Matrix (Fin n) (Fin n) ℝ)
    (hA_symm : ∀ i : Fin m, (A i).IsSymm)
    (hXhat_symm : Xhat.IsSymm)
    (hXhat_psd : Xhat.PosSemidef)
    (hfeas : ∀ i : Fin m, Matrix.trace (A i * Xhat) = b i)
    (hineq : Matrix.rank Xhat * (Matrix.rank Xhat + 1) / 2 > m) :
    ∃ V : Matrix (Fin n) (Fin n) ℝ,
      V.IsSymm ∧
      (∀ i : Fin m, Matrix.trace (A i * V) = 0) ∧
      (Xhat + V).PosSemidef ∧
      (Xhat - V).PosSemidef ∧
      V ≠ 0 := by
  sorry

end «problem-39»
