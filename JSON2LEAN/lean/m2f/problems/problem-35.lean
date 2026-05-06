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
  let J : Matrix (Fin p.m) (Fin p.n) ℝ := p.jacobian x
  let r : Fin p.m → ℝ := p.residual x
  have hInvertibleJ : Invertible (J * Jᵀ) := by
    simpa [J] using hInvertible
  letI := hInvertibleJ
  let z : Fin p.m → ℝ := (⅟ (J * Jᵀ)) *ᵥ r
  let dhatFun : Fin p.n → ℝ := -(Jᵀ *ᵥ z)
  let dhat : EuclideanSpace ℝ (Fin p.n) := (EuclideanSpace.equiv (Fin p.n) ℝ).symm dhatFun
  constructor
  · -- First show that the explicit pseudoinverse candidate gives an exact residual solve.
    have hresidual : J *ᵥ dhatFun = -r := by
      -- Rewrite the candidate through `J * Jᵀ` and cancel the inverse on the left.
      calc
        J *ᵥ dhatFun = -(J *ᵥ (Jᵀ *ᵥ z)) := by
          simp [dhatFun, Matrix.mulVec_neg]
        _ = -((J * Jᵀ) *ᵥ z) := by
          rw [← Matrix.mulVec_mulVec z J Jᵀ]
        _ = -((J * Jᵀ) *ᵥ ((⅟ (J * Jᵀ)) *ᵥ r)) := by
          rfl
        _ = -(((J * Jᵀ) * ⅟ (J * Jᵀ)) *ᵥ r) := by
          rw [← Matrix.mulVec_mulVec r (J * Jᵀ) (⅟ (J * Jᵀ))]
        _ = -(1 *ᵥ r) := by rw [mul_invOf_self]
        _ = -r := by rw [Matrix.one_mulVec]
    have hdhat_system_fun : p.gaussNewtonSystem x dhatFun := by
      -- Applying `Jᵀ` to the exact residual identity gives the normal equations.
      dsimp [DifferentiableNonlinearLeastSquaresProblem.gaussNewtonSystem,
        NonlinearLeastSquaresProblem.gaussNewtonDirection]
      calc
        Jᵀ *ᵥ (J *ᵥ dhatFun) = Jᵀ *ᵥ (-r) := by rw [hresidual]
        _ = -(Jᵀ *ᵥ r) := by rw [Matrix.mulVec_neg]
    -- Transfer the solved function vector back to Euclidean space.
    simpa [dhatFun, z, J, r]
      using hdhat_system_fun
  · intro d hd
    let dFun : Fin p.n → ℝ := d.ofLp
    let eVec : EuclideanSpace ℝ (Fin p.n) := d - dhat
    let e : Fin p.n → ℝ := eVec.ofLp
    have hd_system_fun : p.gaussNewtonSystem x dFun := by
      simpa [dFun]
        using hd
    have hresidual : J *ᵥ dhatFun = -r := by
      -- Reuse the exact residual calculation for the canonical candidate.
      calc
        J *ᵥ dhatFun = -(J *ᵥ (Jᵀ *ᵥ z)) := by
          simp [dhatFun, Matrix.mulVec_neg]
        _ = -((J * Jᵀ) *ᵥ z) := by
          rw [← Matrix.mulVec_mulVec z J Jᵀ]
        _ = -((J * Jᵀ) *ᵥ ((⅟ (J * Jᵀ)) *ᵥ r)) := by
          rfl
        _ = -(((J * Jᵀ) * ⅟ (J * Jᵀ)) *ᵥ r) := by
          rw [← Matrix.mulVec_mulVec r (J * Jᵀ) (⅟ (J * Jᵀ))]
        _ = -(1 *ᵥ r) := by rw [mul_invOf_self]
        _ = -r := by rw [Matrix.one_mulVec]
    have hdhat_system_fun : p.gaussNewtonSystem x dhatFun := by
      -- The exact residual identity implies the same normal equations as any solution.
      dsimp [DifferentiableNonlinearLeastSquaresProblem.gaussNewtonSystem,
        NonlinearLeastSquaresProblem.gaussNewtonDirection]
      calc
        Jᵀ *ᵥ (J *ᵥ dhatFun) = Jᵀ *ᵥ (-r) := by rw [hresidual]
        _ = -(Jᵀ *ᵥ r) := by rw [Matrix.mulVec_neg]
    have hnormal_difference : (Jᵀ * J) *ᵥ e = 0 := by
      -- Subtract the two normal equations to isolate the homogeneous direction.
      have hd_eq :
          Jᵀ *ᵥ (J *ᵥ dFun) = -(Jᵀ *ᵥ r) := by
        simpa [DifferentiableNonlinearLeastSquaresProblem.gaussNewtonSystem,
          NonlinearLeastSquaresProblem.gaussNewtonDirection]
          using hd_system_fun
      have hdhat_eq :
          Jᵀ *ᵥ (J *ᵥ dhatFun) = -(Jᵀ *ᵥ r) := by
        simpa [DifferentiableNonlinearLeastSquaresProblem.gaussNewtonSystem,
          NonlinearLeastSquaresProblem.gaussNewtonDirection]
          using hdhat_system_fun
      have he_eq : e = dFun - dhatFun := by
        simp [e, eVec, dFun, dhat]
      calc
        (Jᵀ * J) *ᵥ e = Jᵀ *ᵥ (J *ᵥ e) := by rw [Matrix.mulVec_mulVec]
        _ = Jᵀ *ᵥ (J *ᵥ dFun - J *ᵥ dhatFun) := by
          rw [he_eq, Matrix.mulVec_sub]
        _ = Jᵀ *ᵥ (J *ᵥ dFun) - Jᵀ *ᵥ (J *ᵥ dhatFun) := by
          rw [Matrix.mulVec_sub]
        _ = (-(Jᵀ *ᵥ r)) - (-(Jᵀ *ᵥ r)) := by rw [hd_eq, hdhat_eq]
        _ = 0 := by simp
    have hkernel : J *ᵥ e = 0 := by
      -- The kernel of `Jᵀ * J` equals the kernel of `J`.
      have hmem :
          e ∈ LinearMap.ker ((Jᵀ * J).mulVecLin) := by
        change (Jᵀ * J) *ᵥ e = 0
        exact hnormal_difference
      have hmemJ : e ∈ LinearMap.ker (Matrix.mulVecLin J) := by
        rw [← Matrix.ker_mulVecLin_transpose_mul_self J]
        exact hmem
      simpa [LinearMap.mem_ker] using hmemJ
    have horth_dot : dhatFun ⬝ᵥ e = 0 := by
      -- The candidate lies in the row space of `J`, hence is orthogonal to any kernel vector.
      calc
        dhatFun ⬝ᵥ e = (Jᵀ *ᵥ (-z)) ⬝ᵥ e := by
          simp [dhatFun, Matrix.mulVec_neg]
        _ = ((-z) ᵥ* J) ⬝ᵥ e := by rw [Matrix.mulVec_transpose]
        _ = (-z) ⬝ᵥ (J *ᵥ e) := by
          simpa using (Matrix.dotProduct_mulVec (-z) J e).symm
        _ = (-z) ⬝ᵥ 0 := by rw [hkernel]
        _ = 0 := by simp
    have horth_inner : inner ℝ dhat eVec = 0 := by
      -- Convert Euclidean inner products to dot products on coordinate functions.
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simpa [e, eVec, dFun, dhat, dotProduct_comm]
        using horth_dot
    have hdecomp : d = dhat + eVec := by
      -- Every solution splits as the canonical candidate plus a kernel direction.
      ext i
      simp [eVec, dhat, sub_eq_add_neg, add_left_comm]
    have hnormsq :
        ‖d‖ * ‖d‖ = ‖dhat‖ * ‖dhat‖ + ‖eVec‖ * ‖eVec‖ := by
      -- The orthogonal decomposition turns the norm comparison into Pythagoras.
      simpa [hdecomp]
        using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero dhat eVec horth_inner
    have hfun_norm : ‖dhat‖ ≤ ‖d‖ := by
      -- The extra squared term is nonnegative, so the canonical candidate has minimal norm.
      have hnormsq' : ‖d‖ ^ 2 = ‖dhat‖ ^ 2 + ‖eVec‖ ^ 2 := by
        simpa [pow_two] using hnormsq
      have hsq : ‖dhat‖ ^ 2 ≤ ‖d‖ ^ 2 := by
        nlinarith [sq_nonneg ‖eVec‖, hnormsq']
      exact le_of_sq_le_sq hsq (norm_nonneg d)
    simpa [dhat, dhatFun, z, J, r] using hfun_norm

end «problem-35»
