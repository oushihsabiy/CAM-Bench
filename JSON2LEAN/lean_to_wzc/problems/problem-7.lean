import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-7»

/- [BLOCK Exercise 3.26-(c) | 35 | thm]
Let n ∈ ℕ and let k satisfy 1 ≤ k ≤ n. Let S_{++}^n denote the set of all real symmetric positive
definite n × n matrices. For X ∈ S_{++}^n, let λ_1(X) ≥ λ_2(X) ≥ ·s ≥ λ_n(X) > 0 denote the
eigenvalues of X. Prove that for every X ∈ S_{++}^n,
prod_{i=n-k+1}^{n} λ_i(X)
=
∈f ≤ft{ prod_{i=1}^{k} vᵢ^{T} X vᵢ |dle| V=[v₁\ ·s\ vₖ] ∈ ℝ^{n × k}, V^{T}V=Iₖ },
where Iₖ is the k × k identity matrix.
-/
theorem inf_prod_quadratic_forms_eq_prod_smallest_eigenvalues
    (n k : ℕ)
    (hk1 : 1 ≤ k)
    (hkn : k ≤ n) :
    ∀ X : Matrix (Fin n) (Fin n) ℝ,
      (hXsymm : X.IsSymm) →
      X.PosDef →
      let hXHerm : X.IsHermitian := by
        simpa using hXsymm
      (∏ i : Fin k,
        hXHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i))) =
        sInf
          {r : ℝ |
            ∃ V : Matrix (Fin n) (Fin k) ℝ,
              V.transpose * V = 1 ∧
              r = ∏ i : Fin k, dotProduct (V · i) (X.mulVec (V · i))} := by
  sorry

/- [BLOCK Exercise 3.26-(c) | 36 | thm]
Let n ∈ ℕ and let k satisfy 1 ≤ k ≤ n. Let S_{++}^n denote the set of all real symmetric positive
definite n × n matrices. For X ∈ S_{++}^n, let λ_1(X) ≥ λ_2(X) ≥ ·s ≥ λ_n(X) > 0 denote the
eigenvalues of X. Prove that the function
X mapsto sum_{i=n-k+1}^{n} log λ_i(X)
is concave on S_{++}^n, i.e., for all X,Y ∈ S_{++}^n and all θ ∈ [0,1],
sum_{i=n-k+1}^{n} log λ_i(θ X + (1-θ)Y)
≥
θ sum_{i=n-k+1}^{n} log λ_i(X)
+ (1-θ) sum_{i=n-k+1}^{n} log λ_i(Y).
-/
theorem sum_log_smallest_eigenvalues_concave
    (n k : ℕ)
    (hk1 : 1 ≤ k)
    (hkn : k ≤ n) :
    ∀ X Y : Matrix (Fin n) (Fin n) ℝ,
      (hXsymm : X.IsSymm) →
      X.PosDef →
      (hYsymm : Y.IsSymm) →
      Y.PosDef →
      ∀ θ : ℝ,
        0 ≤ θ →
        θ ≤ 1 →
        let hXHerm : X.IsHermitian := by
          simpa using hXsymm
        let hYHerm : Y.IsHermitian := by
          simpa using hYsymm
        let hZSymm : (θ • X + (1 - θ) • Y).IsSymm := by
          simpa [Matrix.IsSymm] using
            (Matrix.IsSymm.add (Matrix.IsSymm.smul hXsymm θ)
              (Matrix.IsSymm.smul hYsymm (1 - θ)))
        let hZHerm : (θ • X + (1 - θ) • Y).IsHermitian := by
          simpa using hZSymm
        (∑ i : Fin k,
          Real.log (hZHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)))) ≥
          θ *
            (∑ i : Fin k,
              Real.log
                (hXHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)))) +
            (1 - θ) *
              (∑ i : Fin k,
                Real.log
                  (hYHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)))) := by
  sorry

end «problem-7»
