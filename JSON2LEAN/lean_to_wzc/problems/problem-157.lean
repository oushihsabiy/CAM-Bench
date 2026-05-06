import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-157»

def l2Norm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, (x i) ^ 2)

/-
For a twice differentiable function f: ℝ^n → ℝ, the Hessian of f at x is the matrix ∇^2 f(x) = [(∂^2
f)/(∂ xᵢ ∂ xⱼ)(x)]_{i, j = 1}^n.
-/
def Hessian (n : ℕ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (_ : ContDiffAt ℝ 2 f x) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) x) (Pi.single i (1 : ℝ))

/-
Let f: dom f → ℝ be twice continuously differentiable on dom f ⊆ ℝ^p × ℝ^q. Assume there exists a
constant m > 0 such that for all (u, v)∈ dom f, ∇_{uu}^2 f(u, v) succeq m I, ∇_{vv}^2 f(u, v) preceq
- m I. Define r(u, v) = [∇_u f(u, v); - ∇_v f(u, v)], and let D^2 f(u, v) be the Hessian of f with
respect to (u, v). Also define S = diag(I_p, - I_q). Then Dr(u, v) = SD^2 f(u, v). Show that ‖Dr(u,
v)^{- 1}‖_2 = ‖D^2 f(u, v)^{- 1} S‖_2 = ‖D^2 f(u, v)^{- 1}‖_2 ≤ (1)/(m).
-/
theorem saddle_residual_deriv_inverse_norm_le
    (p q : ℕ)
    (f : (Fin (p + q) → ℝ) → ℝ)
    (m : ℝ)
    (hdom :
      ∀ x : Fin (p + q) → ℝ, ContDiffAt ℝ 2 f x)
    (hm : 0 < m)
    (huu :
      ∀ x : Fin (p + q) → ℝ,
        ∀ u : Fin p → ℝ,
          m * l2Norm u ^ 2 ≤
            ∑ i : Fin p, ∑ j : Fin p,
              u i * (Hessian (p + q) f x (hdom x) (Fin.castAdd q i) (Fin.castAdd q j)) * u j)
    (hvv :
      ∀ x : Fin (p + q) → ℝ,
        ∀ v : Fin q → ℝ,
          ∑ i : Fin q, ∑ j : Fin q,
            v i * (Hessian (p + q) f x (hdom x) (Fin.natAdd p i) (Fin.natAdd p j)) * v j
            ≤ -m * l2Norm v ^ 2)
    (hinv_bound :
      ∀ x : Fin (p + q) → ℝ,
        let H : Matrix (Fin (p + q)) (Fin (p + q)) ℝ := Hessian (p + q) f x (hdom x)
        ‖H⁻¹‖ ≤ 1 / m) :
    ∀ x : Fin (p + q) → ℝ,
    let H : Matrix (Fin (p + q)) (Fin (p + q)) ℝ := Hessian (p + q) f x (hdom x)
    let S : Matrix (Fin (p + q)) (Fin (p + q)) ℝ :=
      fun i j =>
        if i = j then
          if (i : ℕ) < p then 1 else -1
        else 0
    let r : (Fin (p + q) → ℝ) → (Fin (p + q) → ℝ) :=
      fun y i =>
        if (i : ℕ) < p then
          (fderiv ℝ f y) (Pi.single i (1 : ℝ))
        else
          -((fderiv ℝ f y) (Pi.single i (1 : ℝ)))
    let Dr : Matrix (Fin (p + q)) (Fin (p + q)) ℝ :=
      fun i j => (fderiv ℝ r x (Pi.single j (1 : ℝ))) i
    Dr = S * H ∧ ‖Dr⁻¹‖ = ‖H⁻¹ * S‖ ∧ ‖H⁻¹ * S‖ = ‖H⁻¹‖ ∧ ‖H⁻¹‖ ≤ 1 / m := by
  sorry

end «problem-157»
