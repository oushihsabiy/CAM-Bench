import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-87»

-- Exercise_17_11

/- [BLOCK Exercise 17.11 | 19 | defn]
A function f : ℝ^n → ℝ is twice continuously differentiable if all second-order partial derivatives
of f exist and are continuous on ℝ^n; equivalently, f ∈ C^2(ℝ^n).
-/
def TwiceContinuouslyDifferentiable {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ContDiff ℝ 2 f

/- [BLOCK Exercise 17.11 | 20 | defn]
For a twice differentiable function f : ℝ^n → ℝ, the Hessian matrix at x is the matrix ∇^2 f(x) ∈
ℝ^{n×n} with entries (∇^2 f(x))_{ij} = (∂^2 f)/(∂ xᵢ ∂ xⱼ)(x).
-/
def HessianMatrix {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => iteratedFDeriv ℝ 2 f x (fun
    | 0 => Pi.single i 1
    | 1 => Pi.single j 1
    | _ => 0)

/- [BLOCK Exercise 17.11 | 21 | thm]
Let
psi(t,σ;μ)=
cases
-σ t+μ{2}t^2, & t-σ/μ≤ 0,\4pt]
-1{2μ}σ^2, & t-σ/μ>0.
cases
Assume μne 0. Prove that the second derivative of psi(t,σ;μ) with respect to t is given by
(∂^2 psi)/(∂ t^2)(t,σ;μ)=
cases
μ, & t<σ/μ,\4pt]
0, & t>σ/μ,
cases
and hence is discontinuous at t=σ/μ.
-/
theorem psi_second_derivative_piecewise
    {σ μ : ℝ} (hμ : μ ≠ 0) :
    (∀ t : ℝ,
      t < σ / μ →
        deriv
          (fun x : ℝ =>
            deriv
              (fun u : ℝ =>
                if u - σ / μ ≤ 0 then -σ * u + (μ / 2) * u^2 else -(σ^2) / (2 * μ))
              x)
          t = μ)
    ∧
    (∀ t : ℝ,
      t > σ / μ →
        deriv
          (fun x : ℝ =>
            deriv
              (fun u : ℝ =>
                if u - σ / μ ≤ 0 then -σ * u + (μ / 2) * u^2 else -(σ^2) / (2 * μ))
              x)
          t = 0)
    ∧
    ¬ ContinuousAt
      (fun t : ℝ =>
        deriv
          (fun x : ℝ =>
            deriv
              (fun u : ℝ =>
                if u - σ / μ ≤ 0 then -σ * u + (μ / 2) * u^2 else -(σ^2) / (2 * μ))
              x)
          t)
      (σ / μ) := by
  sorry

/- [BLOCK Exercise 17.11 | 22 | thm]
Let
psi(t,σ;μ)=
cases
-σ t+μ{2}t^2, & t-σ/μ≤ 0,\4pt]
-1{2μ}σ^2, & t-σ/μ>0.
cases
Assume μne 0. Also, let cᵢ:ℝ^n→ℝ be twice continuously differentiable, and let λ_i∈ℝ. Prove that the
Hessian matrix with respect to x of the function xmapsto psi(cᵢ(x),λ_i;μ) is
∇_x^2(psi(cᵢ(x),λ_i;μ))=
cases
(μ cᵢ(x)-λ_i)∇_x^2 cᵢ(x)+μ∇ cᵢ(x)∇ cᵢ(x)ᵀ, & cᵢ(x)<λ_i/μ,\6pt]
0, & cᵢ(x)≥ λ_i/μ.
cases
-/
theorem hessian_psi_comp_piecewise
    {n : ℕ} (c : (Fin n → ℝ) → ℝ) (lam μ : ℝ) (x : Fin n → ℝ)
    (hc : TwiceContinuouslyDifferentiable c) (hμ : μ ≠ 0)
    (hnot_boundary : c x ≠ lam / μ) :
    HessianMatrix
      (fun y =>
        if c y - lam / μ ≤ 0 then -lam * c y + (μ / 2) * (c y)^2 else -(lam^2) / (2 * μ))
      x
      =
    if c x < lam / μ then
      fun i j =>
        (μ * c x - lam) * HessianMatrix c x i j +
          μ * (iteratedFDeriv ℝ 1 c x (fun _ => Pi.single i 1)) *
            (iteratedFDeriv ℝ 1 c x (fun _ => Pi.single j 1))
    else 0 := by
  sorry

end «problem-87»
