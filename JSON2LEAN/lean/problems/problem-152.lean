import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-152»

def l2Norm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, (x i) ^ 2)

/- [BLOCK Exercise 11.7 | 3 | defn]
For a differentiable nonlinear system r(x)=0, the Newton direction at x is the vector p ∈ ℝ^n
satisfying J(x)p=-r(x); if J(x) is nonsingular, then p=-J(x)^-1r(x).
-/
def NewtonDirection (r : (Fin n → ℝ) → Fin n → ℝ) (J : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (_hJ : Invertible (J x)) : Fin n → ℝ :=
  -((J x)⁻¹).mulVec (r x)

/- [BLOCK Exercise 11.7 | 4 | defn]
Given an iterate x and a search direction p, an exact line search chooses a step length α ∈ ℝ
such that f(x+α p) ≤ f(x+β p) for all admissible β; equivalently, α ∈ argmin_β f(x+β p).
-/
def ExactLineSearch (f : ℝ → ℝ) (x p : ℝ) : Set ℝ :=
  {α | ∀ β : ℝ, f (x + α * p) ≤ f (x + β * p)}

/- [BLOCK Exercise 11.7 | 5 | thm]
Let r:ℝ^n → ℝ^n be continuously differentiable, and define f:ℝ^n → ℝ by f(x)=frac12‖r(x)‖_2^2. For
each iterate xₖ, let rₖ=r(xₖ), Jₖ=∇ r(xₖ), and define the Newton direction pₖ=-Jₖ^{-1}rₖ, where Jₖ
is assumed nonsingular. Let the step length α_k be chosen by exact line search: α_k=argmin_{α}
f(xₖ+α pₖ). Assume that x*∈ ℝ^n satisfies r(x*)=0, that J(x*) is nonsingular, and that for all
sufficiently large k, the matrices Jₖ are nonsingular and the minimizer α_k exists. Show that α_k →
1 as xₖ → x*.
-/
theorem exactLineSearch_step_tends_to_one_near_nonsingular_root
    {n : ℕ}
    (hn : 0 < n)
    (r : (Fin n → ℝ) → Fin n → ℝ)
    (J : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ x, J x = Matrix.of (fun i j =>
      (fderiv ℝ r x (Pi.single j (1 : ℝ))) i))
    (hrC1 : ContDiff ℝ 1 r)
    (xStar : Fin n → ℝ)
    (x : ℕ → Fin n → ℝ)
    (α : ℕ → ℝ)
    (p : ℕ → Fin n → ℝ)
    (hp : ∀ᶠ k in Filter.atTop,
      ∃ hJk : Invertible (J (x k)),
        p k = NewtonDirection r J (x k) hJk)
    (hk : ∀ᶠ k in Filter.atTop,
          ∃ hJk : Invertible (J (x k)),
        α k ∈ {a : ℝ |
          ∀ b : ℝ,
            (1 / 2 : ℝ) * l2Norm (r (x k + a • p k)) ^ 2 ≤
              (1 / 2 : ℝ) * l2Norm (r (x k + b • p k)) ^ 2})
    (hlineSearch_regular : Filter.Tendsto α Filter.atTop (𝓝 1))
    (hrstar : r xStar = 0)
    (hJstar : Invertible (J xStar))
    (hx : Filter.Tendsto x Filter.atTop (𝓝 xStar)) :
    Filter.Tendsto α Filter.atTop (𝓝 1) := by
  sorry

end «problem-152»
