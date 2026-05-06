import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-82»

-- Exercise_13_22__a_

/- [BLOCK Exercise 13.22-(a) | 15 | opt_prob]
Let n,M ∈ ℕ with M ≥ 1, let μ ∈ ℝ^n, let γ > 0, and for each k=1,ldots,M, let σ^{(k)} ∈ S_{++}^n,
where S_{++}^n denotes the set of real symmetric positive definite n × n matrices. Let 1 ∈ ℝ^n
denote the all-ones vector. Consider the problem
aligned
maximize quad & μᵀ w - γ max_{k=1,ldots,M} wᵀ σ^{(k)} w ;
subject to quad & 1ᵀ w = 1,
aligned
over w ∈ ℝ^n, and suppose that w^{star} ∈ ℝ^n is an optimal solution.
-/
open Matrix

structure RobustMeanVariancePortfolioProblem where
  n : ℕ
  M : ℕ
  hM : 1 ≤ M
  μ : Fin n → ℝ
  γ : ℝ
  hγ : 0 < γ
  Sigma : Fin M → Matrix (Fin n) (Fin n) ℝ
  Sigma_symm : ∀ k : Fin M, (Sigma k).IsSymm
  Sigma_pos : ∀ k : Fin M, PosDef (Sigma k)
  wStar : Fin n → ℝ

def RobustMeanVariancePortfolioProblem.objective
    (P : RobustMeanVariancePortfolioProblem) (w : Fin P.n → ℝ) : ℝ :=
  (∑ i : Fin P.n, P.μ i * w i) -
    P.γ * sSup (Set.range fun k : Fin P.M => dotProduct w (P.Sigma k *ᵥ w))

def RobustMeanVariancePortfolioProblem.isFeasible
    (P : RobustMeanVariancePortfolioProblem) (w : Fin P.n → ℝ) : Prop :=
  (∑ i : Fin P.n, w i) = 1

def RobustMeanVariancePortfolioProblem.isOptimalSolution
    (P : RobustMeanVariancePortfolioProblem) (w : Fin P.n → ℝ) : Prop :=
  P.isFeasible w ∧ ∀ z : Fin P.n → ℝ, P.isFeasible z → P.objective z ≤ P.objective w

/- [BLOCK Exercise 13.22-(a) | 16 | opt_prob]
Consider the problem
aligned
maximize quad & μᵀ w - sum_{k=1}^M γ_k wᵀ σ^{(k)} w ;
subject to quad & 1ᵀ w = 1,
aligned
over w ∈ ℝ^n.
-/
structure WeightedMeanVariancePortfolioProblem where
  n : ℕ
  M : ℕ
  hM : 1 ≤ M
  μ : Fin n → ℝ
  γ : Fin M → ℝ
  hγ : ∀ k : Fin M, 0 ≤ γ k
  Sigma : Fin M → Matrix (Fin n) (Fin n) ℝ
  Sigma_symm : ∀ k : Fin M, (Sigma k).IsSymm
  Sigma_pos : ∀ k : Fin M, PosDef (Sigma k)

def WeightedMeanVariancePortfolioProblem.objective
    (P : WeightedMeanVariancePortfolioProblem) (w : Fin P.n → ℝ) : ℝ :=
  (∑ i : Fin P.n, P.μ i * w i) -
    ∑ k : Fin P.M, P.γ k * dotProduct w (P.Sigma k *ᵥ w)

def WeightedMeanVariancePortfolioProblem.isFeasible
    (P : WeightedMeanVariancePortfolioProblem) (w : Fin P.n → ℝ) : Prop :=
  (∑ i : Fin P.n, w i) = 1

def WeightedMeanVariancePortfolioProblem.isOptimalSolution
    (P : WeightedMeanVariancePortfolioProblem) (w : Fin P.n → ℝ) : Prop :=
  P.isFeasible w ∧ ∀ z : Fin P.n → ℝ, P.isFeasible z → P.objective z ≤ P.objective w

/- [BLOCK Exercise 13.22-(a) | 17 | thm]
Let n,M ∈ ℕ with M ≥ 1, let μ ∈ ℝ^n, let γ > 0, and for each k=1,ldots,M, let σ^{(k)} ∈ S_{++}^n,
where S_{++}^n is the set of real symmetric positive definite n × n matrices. Let 1 ∈ ℝ^n be the
vector of all ones. Consider the robust mean-variance portfolio problem, and assume that w^{star} ∈
ℝ^n is a solution. Show that there exist scalars γ_1,ldots,γ_M ∈ ℝ such that γ_k ≥ 0 quad
(k=1,ldots,M), sum_{k=1}^M γ_k = γ, and w^{star} is also a solution of the weighted mean-variance
portfolio problem.
-/
theorem robust_optimal_implies_weighted_optimal
    (P : RobustMeanVariancePortfolioProblem)
    (hwStar_optimal : P.isOptimalSolution P.wStar) :
    ∃ γw : Fin P.M → ℝ,
      ∃ hγw : ∀ k : Fin P.M, 0 ≤ γw k,
        (∑ k : Fin P.M, γw k) = P.γ ∧
        ((∑ i : Fin P.n, P.wStar i) = 1 ∧
          ∀ z : Fin P.n → ℝ, (∑ i : Fin P.n, z i) = 1 →
            ((∑ i : Fin P.n, P.μ i * z i) -
                ∑ k : Fin P.M, γw k * dotProduct z (P.Sigma k *ᵥ z)) ≤
              ((∑ i : Fin P.n, P.μ i * P.wStar i) -
                ∑ k : Fin P.M, γw k * dotProduct P.wStar (P.Sigma k *ᵥ P.wStar))) := by
  sorry

end «problem-82»
