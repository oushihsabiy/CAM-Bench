import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-117»
/-
Let S^n be the set of real symmetric n×n matrices. For X∈S^n let λ₁(X) ≥ ··· ≥ λ_n(X) be its
eigenvalues. Fix 1 ≤ k ≤ n and assume ∑_{i = 1}^k λ_i(X) = sup{tr(VᵀXV): V∈ℝ^{n×k}, VᵀV = Iₖ}. Prove
that X↦∑_{i = 1}^k λ_i(X) is convex on S^n.
-/
open scoped Matrix
theorem sum_top_k_eigenvalues_convex_on_symmetric
    (n k : ℕ)
    (hk1 : 1 ≤ k)
    (hkn : k ≤ n)
    (topKEigenvalueSum : Matrix (Fin n) (Fin n) ℝ → ℝ)
    (hvariational :
      ∀ X : Matrix (Fin n) (Fin n) ℝ,
        Matrix.IsSymm X →
          topKEigenvalueSum X =
            sSup {r : ℝ |
              ∃ V : Matrix (Fin n) (Fin k) ℝ,
                V.transpose * V = 1 ∧ r = Matrix.trace (V.transpose * X * V)}) :
    ConvexOn ℝ
      {X : Matrix (Fin n) (Fin n) ℝ | Matrix.IsSymm X}
      topKEigenvalueSum := by
  sorry

end «problem-117»