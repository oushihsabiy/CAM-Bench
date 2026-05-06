import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-198»


/- [BLOCK Exercise 7.4-(b) | 29 | defn]
Given a parametric density or mass function p_θ and observations y₁,dots,y_N, the log-likelihood is
the function ell(θ)=sum_{i=1}^N log p_θ(yᵢ).
-/
def logLikelihood {Θ Y : Type} (p : Θ → Y → ℝ) (y : Fin N → Y) : Θ → ℝ :=
  fun θ => ∑ i : Fin N, Real.log (p θ (y i))

/- [BLOCK Exercise 7.4-(b) | 30 | defn]
A function f : X × Y → ℝ is jointly concave if for all (x₁,y₁),(x₂,y₂) ∈ X× Y and all λ∈[0,1],
f(λ x₁+(1-λ)x₂,λ y₁+(1-λ)y₂) ≥ λ f(x₁,y₁)+(1-λ)f(x₂,y₂).
-/
def JointlyConcave {X Y : Type*} [AddCommMonoid X] [Module ℝ X] [AddCommMonoid Y] [Module ℝ Y]
    (f : X × Y → ℝ) : Prop :=
  ∀ (x₁ x₂ : X) (y₁ y₂ : Y) (lam : ℝ),
    0 ≤ lam →
    lam ≤ 1 →
    f (lam • x₁ + (1 - lam) • x₂, lam • y₁ + (1 - lam) • y₂) ≥
      lam * f (x₁, y₁) + (1 - lam) * f (x₂, y₂)

/- [BLOCK Exercise 7.4-(b) | 31 | thm]
Let p_{R,a}(y)=(2π)^{-n/2}det(R)^{-1/2}exp≤ft(-(1)/(2)(y-a)ᵀ R^{-1}(y-a)), where y,a∈ ℝ^n and R∈
ℝ^{n×n} is symmetric positive definite. Let y₁,ldots,y_N∈ ℝ^n be independent samples from this
distribution, and define the log-likelihood l(R,a)=sum_{i=1}^N log p_{R,a}(yᵢ). Let bar
y=(1)/(N)sum_{i=1}^N yᵢ and Y=(1)/(N)sum_{i=1}^N (y_{i-bar} y)(y_{i-bar} y)ᵀ. For symmetric matrices
A,B, write Apreceq B if B-A is positive semidefinite. Show that l is jointly concave ∈ ℝ and a over
the region Rpreceq 2Y.
-/
theorem gaussian_logLikelihood_jointly_concave_on_covariance_region
    {n N : ℕ}
    (hN : 0 < N)
    (y : Fin N → (Fin n → ℝ)) :
    let p : (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) → (Fin n → ℝ) → ℝ :=
      fun θ z =>
        Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) *
          Real.sqrt (Matrix.det θ.1)⁻¹ *
          Real.exp
            (-((∑ i : Fin n, ∑ j : Fin n, (z i - θ.2 i) * ((θ.1)⁻¹ i j) * (z j - θ.2 j)) / 2))
    let l : (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) → ℝ :=
      logLikelihood p y
    let Ybar : Fin n → ℝ :=
      fun j => (1 / (N : ℝ)) * ∑ i : Fin N, y i j
    let sampleCov : Matrix (Fin n) (Fin n) ℝ :=
      fun j k =>
        (1 / (N : ℝ)) * ∑ i : Fin N, (y i j - Ybar j) * (y i k - Ybar k)
    ∀ (R₁ R₂ : Matrix (Fin n) (Fin n) ℝ) (a₁ a₂ : Fin n → ℝ) (lam : ℝ),
      R₁.IsSymm →
      R₂.IsSymm →
      (∀ x : Fin n → ℝ, x ≠ 0 → 0 < ∑ i : Fin n, ∑ j : Fin n, x i * R₁ i j * x j) →
      (∀ x : Fin n → ℝ, x ≠ 0 → 0 < ∑ i : Fin n, ∑ j : Fin n, x i * R₂ i j * x j) →
      (∀ x : Fin n → ℝ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, x i * ((2 : ℝ) • sampleCov - R₁) i j * x j) →
      (∀ x : Fin n → ℝ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, x i * ((2 : ℝ) • sampleCov - R₂) i j * x j) →
      0 ≤ lam →
      lam ≤ 1 →
      l (lam • R₁ + (1 - lam) • R₂, lam • a₁ + (1 - lam) • a₂) ≥
        lam * l (R₁, a₁) + (1 - lam) * l (R₂, a₂) := by
  sorry


end «problem-198»
