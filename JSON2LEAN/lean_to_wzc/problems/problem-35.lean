import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-35»
/-
A nonlinear least - squares problem is an optimization problem of the form min_{x ∈ ℝ^n}
tfrac12‖r(x)‖_2^2, where r: ℝ^n → ℝ^m is a generally nonlinear residual map.
-/
structure NonlinearLeastSquaresProblem where
  n : ℕ
  m : ℕ
  residual : (Fin n → ℝ) → (Fin m → ℝ)
  objective : (Fin n → ℝ) → ℝ := fun x => (1 / 2 : ℝ) * dotProduct (residual x) (residual x)

/-
For the least - squares objective f(x) = tfrac12‖r(x)‖_2^2, a Gauss - - Newton direction at x is any
vector d ∈ ℝ^n satisfying J(x)^→p J(x)d = - J(x)^→p r(x).
-/
def NonlinearLeastSquaresProblem.gaussNewtonDirection
    (p : NonlinearLeastSquaresProblem) (J : (Fin p.n → ℝ) → Matrix (Fin p.m) (Fin p.n) ℝ)
    (x d : Fin p.n → ℝ) : Prop :=
  ((J x)ᵀ.mulVec ((J x).mulVec d)) = -((J x)ᵀ.mulVec (p.residual x))

/-
Given a set S ⊆ ℝ^n, a vector hat d ∈ S is a minimum - ell_2 - norm solution if ‖hat d‖_2 ≤ ‖d‖_2
for
every d ∈ S.
-/
def IsMinimumL2NormSolution {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (dhat : EuclideanSpace ℝ (Fin n)) : Prop :=
  dhat ∈ S ∧ ∀ d, d ∈ S → ‖dhat‖ ≤ ‖d‖

/-
Consider the nonlinear least - squares problem min_{x ∈ ℝ^n} frac12 ‖r(x)‖_2^2, where the residual
function r: ℝ^n → ℝ^m is differentiable at x, and its Jacobian matrix is denoted by J(x) ∈ ℝ^{m ×
n}.
-/
structure DifferentiableNonlinearLeastSquaresProblem extends NonlinearLeastSquaresProblem where
  jacobian : (Fin n → ℝ) → Matrix (Fin m) (Fin n) ℝ
  differentiableAt : ∀ x : Fin n → ℝ, DifferentiableAt ℝ residual x
  jacobian_spec : ∀ x : Fin n → ℝ,
    ∀ v : Fin n → ℝ,
      fderiv ℝ residual x v = (jacobian x).mulVec v

def DifferentiableNonlinearLeastSquaresProblem.gaussNewtonSystem
    (p : DifferentiableNonlinearLeastSquaresProblem) (x d : Fin p.n → ℝ) : Prop :=
  NonlinearLeastSquaresProblem.gaussNewtonDirection p.toNonlinearLeastSquaresProblem p.jacobian x d

/-
Consider the nonlinear least - squares problem min_{x ∈ ℝ^n} frac12 ‖r(x)‖_2^2, where the residual
function r: ℝ^n → ℝ^m is differentiable at the point x, and its Jacobian matrix is denoted by J(x) ∈
ℝ^{m × n}. At the point x, the Gauss - - Newton direction d ∈ ℝ^n satisfies the equation
J(x)^{mathrm
T} J(x) d = - J(x)^{mathrm T} r(x). Assume that J(x) J(x)^{mathrm T} is invertible, that is, J(x)
has full row rank. Prove that hat d = - J(x)^{mathrm T} (J(x) J(x)^{mathrm T})^{- 1} r(x) is a
minimum - ell_2 - norm solution of the above Gauss - - Newton equation; that is, among all vectors d
satisfying J(x)^{mathrm T} J(x) d = - J(x)^{mathrm T} r(x), hat d minimizes ‖d‖_2.
-/
open scoped Matrix

theorem gaussNewton_minimumL2NormSolution_of_fullRowRank
    (p : DifferentiableNonlinearLeastSquaresProblem) (x : EuclideanSpace ℝ (Fin p.n))
    (hmn : p.m ≤ p.n)
    (hInvertible : Invertible (p.jacobian x * (p.jacobian x)ᵀ)) :
    IsMinimumL2NormSolution
      {d : EuclideanSpace ℝ (Fin p.n) | p.gaussNewtonSystem x d}
      ((EuclideanSpace.equiv (Fin p.n) ℝ).symm
        (-((p.jacobian x)ᵀ).mulVec
          (((⅟ (p.jacobian x * (p.jacobian x)ᵀ)).mulVec (p.residual x))))) := by
  sorry

end «problem-35»
