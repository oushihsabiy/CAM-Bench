import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-174»

/- [BLOCK Exercise 14.13 | 18 | defn]
A function g defined on a neighborhood of 0 has a third-order Taylor expansion at 0 if there
exist g(0), g'(0), g''(0), and g^(3)(0) such that, as τ → 0,
g(τ)=g(0)+τ g'(0)+(τ^2)/(2)g''(0)+(τ^3)/(6)g^(3)(0)+o(τ^3).
-/
def HasThirdOrderTaylorExpansionAtZero (g : ℝ → ℝ) : Prop :=
  ∃ g0 g1 g2 g3 : ℝ,
    Tendsto (fun τ : ℝ =>
      (g τ - (g0 + τ * g1 + (τ ^ 2 / 2) * g2 + (τ ^ 3 / 6) * g3)) / τ ^ 3) (𝓝[≠] 0) (𝓝 0)

/-
Exercise 14.13 | 19 | thm

Let A ∈ ℝ^{m×n}, b ∈ ℝ^m, c ∈ ℝ^n, x, s ∈ ℝ^n, and λ ∈ ℝ^m, with xᵢ > 0 and sᵢ > 0 for all i = 1, …,
n. Let e ∈ ℝ^n be the vector of all ones, and define X = diag(x) and S = diag(s). Define F : ℝ^n ×
ℝ^m × ℝ^n → ℝ^{m+2n} by

F(u, μ, v) =
\[
\begin{bmatrix}
Aᵀμ + v - c \\
Au - b \\
diag(u)v
\end{bmatrix}.
\]

Let (x̂, λ̂, ŝ) be a trajectory that is three times differentiable on a neighborhood of 0, satisfies

\[
F(x̂(τ), λ̂(τ), ŝ(τ)) =
\begin{bmatrix}
(1 - τ)(Aᵀλ + s - c) \\
(1 - τ)(Ax - b) \\
(1 - τ)XSe
\end{bmatrix}
\]

for all τ near 0, and has initial condition

\[
(x̂(0), λ̂(0), ŝ(0)) = (x, λ, s).
\]

Write

ẋ = x̂′(0), λ̇ = λ̂′(0), ṡ = ŝ′(0),

ẍ = x̂″(0), λ̈ = λ̂″(0), s̈ = ŝ″(0), and

x^(3) = x̂^(3)(0), λ^(3) = λ̂^(3)(0), s^(3) = ŝ^(3)(0).

Prove that these derivatives satisfy

Aᵀλ̇ + ṡ = -(Aᵀλ + s - c), A ẋ = -(Ax - b), Sẋ + Xṡ = -XSe,

Aᵀλ̈ + s̈ = 0, A ẍ = 0, Sẍ + Xs̈ = -2(ẋ ∘ ṡ),

Aᵀλ^(3) + s^(3) = 0, A x^(3) = 0, Sx^(3) + Xs^(3) = -3(ẋ ∘ s̈ + ẍ ∘ ṡ),

where ∘ denotes componentwise multiplication.
-/
theorem trajectory_derivatives_satisfy_first_second_third_order_system
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (x s : Fin n → ℝ)
    (lam : Fin m → ℝ)
    (hxpos : ∀ i : Fin n, 0 < x i)
    (hspos : ∀ i : Fin n, 0 < s i)
    (xhat : ℝ → Fin n → ℝ)
    (lamhat : ℝ → Fin m → ℝ)
    (shat : ℝ → Fin n → ℝ)
    (xdot xddot xthird : Fin n → ℝ)
    (lamdot lamddot lamthird : Fin m → ℝ)
    (sdot sddot sthird : Fin n → ℝ)
    (hF : ∀ᶠ τ in 𝓝 0,
      Matrix.mulVec A.transpose (lamhat τ) + shat τ - c =
        (1 - τ) • (Matrix.mulVec A.transpose lam + s - c) ∧
      Matrix.mulVec A (xhat τ) - b = (1 - τ) • (Matrix.mulVec A x - b) ∧
      (fun i : Fin n => xhat τ i * shat τ i) = (1 - τ) • (fun i : Fin n => x i * s i))
    (h0 : xhat 0 = x ∧ lamhat 0 = lam ∧ shat 0 = s)
    (hx_contdiff : ∀ i : Fin n, ContDiffAt ℝ 3 (fun τ : ℝ => xhat τ i) 0)
    (hlam_contdiff : ∀ i : Fin m, ContDiffAt ℝ 3 (fun τ : ℝ => lamhat τ i) 0)
    (hs_contdiff : ∀ i : Fin n, ContDiffAt ℝ 3 (fun τ : ℝ => shat τ i) 0)
    (hxderiv1 : ∀ i : Fin n, HasDerivAt (fun τ : ℝ => xhat τ i) (xdot i) 0)
    (hlamderiv1 : ∀ i : Fin m, HasDerivAt (fun τ : ℝ => lamhat τ i) (lamdot i) 0)
    (hsderiv1 : ∀ i : Fin n, HasDerivAt (fun τ : ℝ => shat τ i) (sdot i) 0)
    (hxderiv2 : ∀ i : Fin n, HasDerivAt (fun τ : ℝ => deriv (fun t : ℝ => xhat t i) τ) (xddot i) 0)
    (hlamderiv2 : ∀ i : Fin m, HasDerivAt (fun τ : ℝ => deriv (fun t : ℝ => lamhat t i) τ) (lamddot i) 0)
    (hsderiv2 : ∀ i : Fin n, HasDerivAt (fun τ : ℝ => deriv (fun t : ℝ => shat t i) τ) (sddot i) 0)
    (hxderiv3 :
      ∀ i : Fin n,
        HasDerivAt (fun τ : ℝ => deriv (fun u : ℝ => deriv (fun t : ℝ => xhat t i) u) τ) (xthird i) 0)
    (hlamderiv3 :
      ∀ i : Fin m,
        HasDerivAt (fun τ : ℝ => deriv (fun u : ℝ => deriv (fun t : ℝ => lamhat t i) u) τ) (lamthird i) 0)
    (hsderiv3 :
      ∀ i : Fin n,
        HasDerivAt (fun τ : ℝ => deriv (fun u : ℝ => deriv (fun t : ℝ => shat t i) u) τ) (sthird i) 0) :
    Matrix.mulVec A.transpose lamdot + sdot = -(Matrix.mulVec A.transpose lam + s - c) ∧
    Matrix.mulVec A xdot = -(Matrix.mulVec A x - b) ∧
    (fun i : Fin n => s i * xdot i + x i * sdot i) = -(fun i : Fin n => x i * s i) ∧
    Matrix.mulVec A.transpose lamddot + sddot = 0 ∧
    Matrix.mulVec A xddot = 0 ∧
    (fun i : Fin n => s i * xddot i + x i * sddot i) =
      (fun i : Fin n => -2 * (xdot i * sdot i)) ∧
    Matrix.mulVec A.transpose lamthird + sthird = 0 ∧
    Matrix.mulVec A xthird = 0 ∧
    (fun i : Fin n => s i * xthird i + x i * sthird i) =
      (fun i : Fin n => -3 * (xdot i * sddot i + xddot i * sdot i)) := by
  sorry

/-
Exercise 14.13 | 20 | thm

Let A ∈ ℝ^{m×n}, b ∈ ℝ^m, c ∈ ℝ^n, x, s ∈ ℝ^n, and λ ∈ ℝ^m, with xᵢ > 0 and sᵢ > 0 for all i = 1, …,
n. Let e ∈ ℝ^n be the vector of all ones, and define X = diag(x) and S = diag(s). Define F : ℝ^n ×
ℝ^m × ℝ^n → ℝ^{m+2n} by
F(u, μ, v) = \[
Aᵀμ + v - c;
Au - b;
diag(u)v
\].
Let (x̂, λ̂, ŝ) be a trajectory that is three times differentiable on a neighborhood of 0, satisfies
F(x(τ), λ(τ), s(τ)) =
\[
(1 - τ)(Aᵀλ + s - c);
(1 - τ)(Ax - b);
(1 - τ)XSe
\]
for all τ near 0, and has initial condition
(x(0), λ(0), s(0)) = (x, λ, s).
Write
ẋ = x̂′(0), λ̇ = λ̂′(0), ṡ = ŝ′(0),
ẍ = x̂″(0), λ̈ = λ̂″(0), s̈ = ŝ″(0), and
x⁽³⁾ = x̂⁽³⁾(0), λ⁽³⁾ = λ̂⁽³⁾(0), s⁽³⁾ = ŝ⁽³⁾(0).
Prove also that the third-order Taylor expansion of the trajectory at τ = 0 is
x̂(τ) = x + τẋ + (τ²/2)ẍ + (τ³/6)x⁽³⁾ + o(τ³),
λ̂(τ) = λ + τλ̇ + (τ²/2)λ̈ + (τ³/6)λ⁽³⁾ + o(τ³),
ŝ(τ) = s + τṡ + (τ²/2)s̈ + (τ³/6)s⁽³⁾ + o(τ³).
-/
theorem trajectory_has_third_order_taylor_expansion
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (x s : Fin n → ℝ)
    (lam : Fin m → ℝ)
    (hxpos : ∀ i : Fin n, 0 < x i)
    (hspos : ∀ i : Fin n, 0 < s i)
    (xhat : ℝ → Fin n → ℝ)
    (lamhat : ℝ → Fin m → ℝ)
    (shat : ℝ → Fin n → ℝ)
    (xdot xddot xthird : Fin n → ℝ)
    (lamdot lamddot lamthird : Fin m → ℝ)
    (sdot sddot sthird : Fin n → ℝ)
    (hF : ∀ᶠ τ in 𝓝 0,
      Matrix.mulVec A.transpose (lamhat τ) + shat τ - c =
        (1 - τ) • (Matrix.mulVec A.transpose lam + s - c) ∧
      Matrix.mulVec A (xhat τ) - b = (1 - τ) • (Matrix.mulVec A x - b) ∧
      (fun i : Fin n => xhat τ i * shat τ i) = (1 - τ) • (fun i : Fin n => x i * s i))
    (h0 : xhat 0 = x ∧ lamhat 0 = lam ∧ shat 0 = s)
    (hx_contdiff : ∀ i : Fin n, ContDiffAt ℝ 3 (fun τ : ℝ => xhat τ i) 0)
    (hlam_contdiff : ∀ i : Fin m, ContDiffAt ℝ 3 (fun τ : ℝ => lamhat τ i) 0)
    (hs_contdiff : ∀ i : Fin n, ContDiffAt ℝ 3 (fun τ : ℝ => shat τ i) 0)
    (hxderiv1 : ∀ i : Fin n, HasDerivAt (fun τ : ℝ => xhat τ i) (xdot i) 0)
    (hlamderiv1 : ∀ i : Fin m, HasDerivAt (fun τ : ℝ => lamhat τ i) (lamdot i) 0)
    (hsderiv1 : ∀ i : Fin n, HasDerivAt (fun τ : ℝ => shat τ i) (sdot i) 0)
    (hxderiv2 : ∀ i : Fin n, HasDerivAt (fun τ : ℝ => deriv (fun t : ℝ => xhat t i) τ) (xddot i) 0)
    (hlamderiv2 : ∀ i : Fin m, HasDerivAt (fun τ : ℝ => deriv (fun t : ℝ => lamhat t i) τ) (lamddot i) 0)
    (hsderiv2 : ∀ i : Fin n, HasDerivAt (fun τ : ℝ => deriv (fun t : ℝ => shat t i) τ) (sddot i) 0)
    (hxderiv3 :
      ∀ i : Fin n,
        HasDerivAt (fun τ : ℝ => deriv (fun u : ℝ => deriv (fun t : ℝ => xhat t i) u) τ) (xthird i) 0)
    (hlamderiv3 :
      ∀ i : Fin m,
        HasDerivAt (fun τ : ℝ => deriv (fun u : ℝ => deriv (fun t : ℝ => lamhat t i) u) τ) (lamthird i) 0)
    (hsderiv3 :
      ∀ i : Fin n,
        HasDerivAt (fun τ : ℝ => deriv (fun u : ℝ => deriv (fun t : ℝ => shat t i) u) τ) (sthird i) 0) :
    (∀ i : Fin n,
      Tendsto
        (fun τ : ℝ =>
          ((xhat τ i) -
              (x i + τ * xdot i + (τ ^ 2 / 2) * xddot i + (τ ^ 3 / 6) * xthird i)) / τ ^ 3)
        (𝓝[≠] 0) (𝓝 0)) ∧
    (∀ i : Fin m,
      Tendsto
        (fun τ : ℝ =>
          ((lamhat τ i) -
              (lam i + τ * lamdot i + (τ ^ 2 / 2) * lamddot i + (τ ^ 3 / 6) * lamthird i)) / τ ^ 3)
        (𝓝[≠] 0) (𝓝 0)) ∧
    (∀ i : Fin n,
      Tendsto
        (fun τ : ℝ =>
          ((shat τ i) -
              (s i + τ * sdot i + (τ ^ 2 / 2) * sddot i + (τ ^ 3 / 6) * sthird i)) / τ ^ 3)
        (𝓝[≠] 0) (𝓝 0)) := by
  sorry

end «problem-174»
