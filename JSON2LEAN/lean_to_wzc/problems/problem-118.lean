import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-118»
/-
Let 1 ≤ k ≤ n and let S_{+ +}^n be the positive - definite cone in S^n. Prove that X ↦ (∏_{i = n - k
+ 1}^n
λ_i(X))^(1/k), the geometric mean of the k smallest eigenvalues, is concave on S_{+ +}^n.
-/
theorem geometricMeanSmallestEigenvalues_concave
    (n k : ℕ)
    (hk1 : 1 ≤ k)
    (hkn : k ≤ n) :
    ConcaveOn ℝ
      {X : Matrix (Fin n) (Fin n) ℝ | X.PosDef ∧ X.IsSymm}
      (fun X =>
        by
          classical
          exact
            if hX : X.PosDef ∧ X.IsSymm then
              let hH : X.IsHermitian := by
                ext i j
                simpa using hX.2.apply i j
              Real.rpow
                (∏ j : Fin k, hH.eigenvalues₀
                  (Fin.cast (show n = Fintype.card (Fin n) by simp) ⟨n - k + j.1, by
                    have hj : j.1 < k := j.2
                    calc
                      n - k + j.1 < n - k + k := Nat.add_lt_add_left hj (n - k)
                      _ = n := Nat.sub_add_cancel hkn⟩))
                (1 / (k : ℝ))
            else
              0) := by
  sorry

end «problem-118»
