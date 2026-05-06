import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-200»

/- [BLOCK Exercise 7.4-(a) | 1 | defn]
Given a parametric family of densities or likelihoods {p_θ} and observed data, a parameter value
hatθ is a maximum-likelihood estimate if hatθ ∈ argmax_θ L(θ), equivalently if hatθ ∈ argmax_θ
ell(θ), where L is the likelihood and ell = log L is the log-likelihood.
-/
def IsMaximumLikelihoodEstimate {Θ : Type*} (L ℓ : Θ → ℝ) (θhat : Θ) : Prop :=
  (∀ θ : Θ, 0 < L θ) ∧
    (∀ θ : Θ, ℓ θ = Real.log (L θ)) ∧
    (∀ θ : Θ, L θ ≤ L θhat) ∧
    (∀ θ : Θ, ℓ θ ≤ ℓ θhat)

/- [BLOCK Exercise 7.4-(a) | 2 | defn]
For observed data y₁,dots,y_N under a parametric density p_θ, the log-likelihood function is
ell(θ)=sum_{k=1}^N log p_θ(yₖ), defined for parameter values θ such that each p_θ(yₖ)>0.
-/
def logLikelihood {Θ Y : Type*} (p : Θ → Y → ℝ) (y : Fin N → Y) :
    {θ : Θ // ∀ k : Fin N, p θ (y k) > 0} → ℝ :=
  fun θ => ∑ k : Fin N, Real.log (p θ.1 (y k))


/- [BLOCK Exercise 7.4-(a) | 4 | thm]
Let R ∈ ℝ^{n imes n} be symmetric positive definite, R succ 0, and let a ∈ ℝ^n. For y ∈ ℝ^n, define
p_{R,a}(y)=(2π)^{-n/2}det(R)^{-1/2}exp≤ft(-
rac{1}{2}(y-a)ᵀ R^{-1}(y-a)
ight). Let y₁,ldots,y_N ∈ ℝ^n be independent samples from this density, and define μ=
rac{1}{N}sum_{k=1}^N yₖ, Y=
rac{1}{N}sum_{k=1}^N (yₖ-μ)(yₖ-μ)ᵀ. The log-likelihood function is l(R,a)= -
rac{Nn}{2}log(2π)-
rac{N}{2}logdet R-
rac{1}{2}sum_{k=1}^N (y_{k-a})ᵀ R^{-1}(y_{k-a}), and l(R,a)=
rac{N}{2}≤ft(-nlog(2π)-logdet R-tr(R^{-1}Y)-(a-μ)ᵀ R^{-1}(a-μ)
ight). Using this expression, show that if Y succ 0, then the maximum-likelihood estimates of R and
a are unique and satisfy a_{ml}=μ, R_{ml}=Y.
-/
theorem gaussian_mle_unique_at_sample_mean_and_covariance
    {n N : ℕ} (hN : 0 < N)
    (y : Fin N → Fin n → ℝ)
    (hYpd :
      ((N : ℝ)⁻¹ •
        ∑ k : Fin N,
          Matrix.vecMulVec
            (fun i => y k i - ((N : ℝ)⁻¹ * ∑ t : Fin N, y t i))
            (fun i => y k i - ((N : ℝ)⁻¹ * ∑ t : Fin N, y t i))).PosDef) :
    let μ : Fin n → ℝ :=
      fun i => (N : ℝ)⁻¹ * ∑ t : Fin N, y t i
    let Y : Matrix (Fin n) (Fin n) ℝ :=
      (N : ℝ)⁻¹ •
        ∑ k : Fin N,
          Matrix.vecMulVec
            (fun i => y k i - μ i)
            (fun i => y k i - μ i)
    let p :
        ({R : Matrix (Fin n) (Fin n) ℝ // R.PosDef} × (Fin n → ℝ)) →
          (Fin n → ℝ) → ℝ :=
      fun θ z =>
        (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) *
          Real.rpow (Matrix.det θ.1.1) (-(1 : ℝ) / 2)) *
          Real.exp
            (-(1 / 2 : ℝ) *
              dotProduct (fun i => z i - θ.2 i)
                (fun i => ∑ j : Fin n, (θ.1.1⁻¹) i j * (z j - θ.2 j)))
    let L :
        ({R : Matrix (Fin n) (Fin n) ℝ // R.PosDef} × (Fin n → ℝ)) → ℝ :=
      fun θ => ∏ k : Fin N, p θ (y k)
    let ell :
        ({R : Matrix (Fin n) (Fin n) ℝ // R.PosDef} × (Fin n → ℝ)) → ℝ :=
      fun θ => Real.log (L θ)
    let θstar : ({R : Matrix (Fin n) (Fin n) ℝ // R.PosDef} × (Fin n → ℝ)) :=
      (⟨Y, hYpd⟩, μ)
    IsMaximumLikelihoodEstimate
        L
        ell
        θstar ∧
      ∀ θ : ({R : Matrix (Fin n) (Fin n) ℝ // R.PosDef} × (Fin n → ℝ)),
        IsMaximumLikelihoodEstimate
            L
            ell
            θ →
          θ = θstar := by
  sorry


end «problem-200»
