import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-79»
/-
For a statistical model with observed data z and parameter x, the log - likelihood is the function
ell(x) = log p(z| x), where p(z| x) is the likelihood of the observation under parameter x.
-/
def logLikelihood (p : α → β → ℝ) (z : β) : α → ℝ :=
  fun x => Real.log (p x z)

/-
Maximum - likelihood estimation is the problem of choosing a parameter x that maximizes the
log - likelihood, equivalently the likelihood, of the observed data: x* ∈ operatorname*{argmax}_x
ell(x).
-/
def maximumLikelihoodEstimators (p : α → β → ℝ) (z : β) : Set α :=
  {x | ∀ y, logLikelihood p z y ≤ logLikelihood p z x}

/-
Let m, n ∈ ℕ, let x ∈ ℝ^n be the optimization variable, and for each i = 1, ..., m, let aᵢ ∈ ℝ^n and
bᵢ ∈ ℝ be given. Let v₁, ..., vₘ be independent N(0, 1) random variables. For each i = 1, ..., m,
define yᵢ = sign(a_iᵀ x + vᵢ - bᵢ) = cases 1, & a_iᵀ x + vᵢ ≥ bᵢ,; - 1, & a_iᵀ x + vᵢ < bᵢ. cases
Assume an
observed vector bar y = (bar y₁, ..., bar yₘ) is given, where bar yᵢ ∈ {- 1, 1} for all i. For each
i,
define Pᵢ(x) = prob(yᵢ = 1) = 1{2π}int_{bᵢ - a_iᵀ x}^{∞} e^{- t^2/2}dt. Then prob(yᵢ = - 1) = 1 -
Pᵢ(x),
and the log - likelihood of the observation bar y is l(x) = \sum_{bar yᵢ = 1}log Pᵢ(x) + \sum_{bar
yᵢ =
- 1}log(1 - Pᵢ(x)). Show that the maximum - likelihood estimation problem maximize l(x) is a convex
optimization problem. The variable is x; the measured vector bar y and the parameters aᵢ and bᵢ are
given.
-/
theorem maximumLikelihoodEstimation_is_convex_optimization
    {m n : ℕ} (a : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (ybar : Fin m → ℤ)
    (hybar : ∀ i, ybar i = 1 ∨ ybar i = -1) :
    let p : (Fin n → ℝ) → Unit → ℝ :=
      fun x _ =>
        Real.exp
          (∑ i : Fin m,
            if ybar i = 1 then
              Real.log
                ((((1 / Real.sqrt (2 * Real.pi)) : ℝ) *
                  (∫ t in Set.Ici ((b i) - ∑ j : Fin n, a i j * x j),
                    Real.exp (-(t ^ 2) / 2))))
            else
              Real.log
                (1 -
                  (((1 / Real.sqrt (2 * Real.pi)) : ℝ) *
                    (∫ t in Set.Ici ((b i) - ∑ j : Fin n, a i j * x j),
                      Real.exp (-(t ^ 2) / 2)))))
    -- l(x) is concave, so maximizing it is a convex optimization problem
    ConcaveOn ℝ (Set.univ : Set (Fin n → ℝ)) (logLikelihood p ()) ∧
    -- the optimal solution set is convex (follows from concavity of l)
    Convex ℝ (maximumLikelihoodEstimators p ()) := by
  sorry


end «problem-79»