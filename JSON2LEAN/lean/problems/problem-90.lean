import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-90»

-- Exercise_2_11

/- [BLOCK Exercise 2.11 | 8 | defn]
A quasi-Newton method is an iterative method for unconstrained minimization that generates search
directions by solving Bₖ pₖ = -∇ f(xₖ), where Bₖ is an approximation to the Hessian ∇^2 f(xₖ)
updated from previous iterates and gradients.
-/
structure QuasiNewtonMethod where
  dim : ℕ
  fVec : EuclideanSpace ℝ (Fin dim) → ℝ
  xVec : ℕ → EuclideanSpace ℝ (Fin dim)
  BVec : ℕ → EuclideanSpace ℝ (Fin dim) →L[ℝ] EuclideanSpace ℝ (Fin dim)
  pVec : ℕ → EuclideanSpace ℝ (Fin dim)
  gradVec : ℕ → EuclideanSpace ℝ (Fin dim)
  gradVec_eq : ∀ k, HasGradientAt (f := fVec) (gradVec k) (xVec k)
  updateRule :
    ℕ →
      (EuclideanSpace ℝ (Fin dim) →L[ℝ] EuclideanSpace ℝ (Fin dim)) →
      EuclideanSpace ℝ (Fin dim) →
      EuclideanSpace ℝ (Fin dim) →
      EuclideanSpace ℝ (Fin dim) →
      EuclideanSpace ℝ (Fin dim) →
      (EuclideanSpace ℝ (Fin dim) →L[ℝ] EuclideanSpace ℝ (Fin dim))
  search_direction_eq_vec : ∀ k, BVec k (pVec k) = -gradVec k
  B_updated_from_previous :
    ∀ k,
      BVec (k + 1) =
        updateRule k (BVec k) (xVec k) (xVec (k + 1)) (gradVec k) (gradVec (k + 1))

def QuasiNewtonMethod.x (_q : QuasiNewtonMethod) : ℕ → ℝ :=
  fun _ => 0

def QuasiNewtonMethod.grad (_q : QuasiNewtonMethod) : ℕ → ℝ :=
  fun _ => 0

def QuasiNewtonMethod.B (_q : QuasiNewtonMethod) : ℕ → ℝ :=
  fun _ => 0

def quasiNewtonMethod : Set QuasiNewtonMethod :=
  { q | ∀ k, q.BVec k (q.pVec k) = -q.gradVec k }

/- [BLOCK Exercise 2.11 | 9 | defn]
A Hessian approximation is a matrix Bₖ ∈ ℝ^n×n intended to approximate the Hessian matrix ∇^2
f(xₖ) of a twice-differentiable objective function at the current iterate.
-/
structure HessianApproximation (n : ℕ) where
  f : EuclideanSpace ℝ (Fin n) → ℝ
  x : ℕ → EuclideanSpace ℝ (Fin n)
  B : ℕ → Matrix (Fin n) (Fin n) ℝ
  hessian : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
  hessian_spec :
    ∀ k : ℕ, HasFDerivAt (gradient f) (hessian k) (x k)
  approximationResidual :
    ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
  approximation_decomposition :
    ∀ k : ℕ,
      Matrix.toEuclideanLin (B k) = hessian k + approximationResidual k

/- [BLOCK Exercise 2.11 | 10 | defn]
Given sₖ = x_k+1-xₖ and yₖ = ∇ f(x_k+1)-∇ f(xₖ), with (yₖ-Bₖ sₖ)ᵀ sₖ neq 0, the symmetric
rank-one (SR1) update is
B_k+1=Bₖ+(yₖ-Bₖ sₖ)(yₖ-Bₖ sₖ)ᵀ{(yₖ-Bₖ sₖ)ᵀ sₖ}.
-/
def sr1Update (q : QuasiNewtonMethod) (k : ℕ)
    (hdenom :
      let s := q.xVec (k + 1) - q.xVec k
      let y := q.gradVec (k + 1) - q.gradVec k
      let u := y - q.BVec k s
      ⟪u, s⟫ ≠ 0) :
    EuclideanSpace ℝ (Fin q.dim) →L[ℝ] EuclideanSpace ℝ (Fin q.dim) :=
  let s := q.xVec (k + 1) - q.xVec k
  let y := q.gradVec (k + 1) - q.gradVec k
  let u := y - q.BVec k s
  q.BVec k + (1 / ⟪u, s⟫) • (((innerSL ℝ) u).smulRight u)

/- [BLOCK Exercise 2.11 | 11 | defn]
Given sₖ = x_k+1-xₖ and yₖ = ∇ f(x_k+1)-∇ f(xₖ), with s_kᵀ Bₖ sₖ neq 0 and y_kᵀ sₖ neq
0, the BFGS update is
B_k+1=Bₖ-Bₖ sₖ s_kᵀ Bₖ{s_kᵀ Bₖ sₖ}+yₖ y_kᵀ{y_kᵀ sₖ}.
-/
def bfgsUpdate (q : QuasiNewtonMethod) (k : ℕ)
    (hBs :
      let s := q.xVec (k + 1) - q.xVec k
      ⟪q.BVec k s, s⟫ ≠ 0)
    (hys :
      let s := q.xVec (k + 1) - q.xVec k
      let y := q.gradVec (k + 1) - q.gradVec k
      ⟪y, s⟫ ≠ 0) :
    EuclideanSpace ℝ (Fin q.dim) →L[ℝ] EuclideanSpace ℝ (Fin q.dim) :=
  let s := q.xVec (k + 1) - q.xVec k
  let y := q.gradVec (k + 1) - q.gradVec k
  q.BVec k
    - (1 / ⟪q.BVec k s, s⟫) • (((innerSL ℝ) (q.BVec k s)).smulRight (q.BVec k s))
    + (1 / ⟪y, s⟫) • (((innerSL ℝ) y).smulRight y)

/- [BLOCK Exercise 2.11 | 12 | defn]
A symmetric rank-one update is a matrix update of the form B_k+1=Bₖ+uuᵀ/α for some u ∈ ℝ^n and
nonzero scalar α, so that B_k+1-Bₖ is symmetric and has rank one.
-/
structure SymmetricRankOneUpdate (n : ℕ) where
  B : ℕ → Matrix (Fin n) (Fin n) ℝ
  u : ℕ → Fin n → ℝ
  α : ℕ → ℝ
  alpha_ne_zero : ∀ k, α k ≠ 0
  update_eq : ∀ k, B (k + 1) = B k + (1 / α k) • Matrix.vecMulVec (u k) (u k)

/- [BLOCK Exercise 2.11 | 13 | defn]
A method is scale-invariant under the affine change of variables x=Sz+s if, when initialized
consistently under this transformation, the iterates satisfy xₖ=Sz_k+s for all k.
-/
def scaleInvariantUnderAffineChange (x z : ℕ → ℝ) (S s : ℝ) : Prop :=
  ∀ k, x k = S * z k + s

/-
Exercise 2.11 | 14 | thm

Let f : ℝ^n → ℝ be differentiable, let S ∈ ℝ^{n×n} be nonsingular, and let s ∈ ℝ^n. Define f̃ : ℝ^n
→ ℝ by f̃(z) = f(Sz + s). A quasi-Newton method is applied to f with initial point x₀ = Sz₀ + s and
initial Hessian approximation B₀ ∈ ℝ^{n×n}, and the corresponding transformed method is applied to
f̃ with initial point z₀ and initial Hessian approximation B̃₀ = SᵀB₀S. Assume both methods use unit
step lengths and generate iterates by x_{k+1} = xₖ + pₖ, z_{k+1} = zₖ + p̃ₖ, where Bₖpₖ = -∇f(xₖ),
B̃ₖp̃ₖ = -∇f̃(zₖ). For each k, define sₖ = x_{k+1} - xₖ, yₖ = ∇f(x_{k+1}) - ∇f(xₖ), and s̃ₖ =
z_{k+1} - zₖ, ỹₖ = ∇f̃(z_{k+1}) - ∇f̃(zₖ). Assume all quantities in the update formulas are well
defined: for the SR1 update, (yₖ - Bₖsₖ)ᵀsₖ ≠ 0, and for the BFGS update, sₖᵀBₖsₖ ≠ 0, yₖᵀsₖ ≠ 0,
with the corresponding conditions for the transformed iterates. Show that the symmetric rank-one
update
B_{k+1} = Bₖ + ((yₖ - Bₖsₖ)(yₖ - Bₖsₖ)ᵀ) / ((yₖ - Bₖsₖ)ᵀsₖ)
and the BFGS update
B_{k+1} = Bₖ - (BₖsₖsₖᵀBₖ) / (sₖᵀBₖsₖ) + (yₖyₖᵀ) / (yₖᵀsₖ)
are scale-invariant when the initial Hessian approximations are chosen appropriately. Using the
notation above, show that if these methods are applied to f starting from x₀ = Sz₀ + s with initial
Hessian approximation B₀, and to f̃ starting from z₀ with initial Hessian approximation SᵀB₀S, then,
assuming unit step lengths, all iterates satisfy xₖ = Szₖ + s.
-/
theorem sr1_and_bfgs_scale_invariant
    {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (s : EuclideanSpace ℝ (Fin n))
    (ftilde : EuclideanSpace ℝ (Fin n) → ℝ)
    (x x_tilde : ℕ → EuclideanSpace ℝ (Fin n))
    (p p_tilde : ℕ → EuclideanSpace ℝ (Fin n))
    (grad grad_tilde : ℕ → EuclideanSpace ℝ (Fin n))
    (B B_tilde : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hf_diff : ∀ x, DifferentiableAt ℝ f x)
    (hS_nonsing : Function.Bijective S)
    (hftilde : ∀ z, ftilde z = f (S z + s))
    (hx0 : x 0 = S (x_tilde 0) + s)
    (hB0 :
      B_tilde 0 = (S.adjoint.comp (B 0)).comp S)
    (hcompat_grad : ∀ k, grad_tilde k = S.adjoint (grad k))
    (hcompat_B : ∀ k, B_tilde k = (S.adjoint.comp (B k)).comp S)
    (hB_injective : ∀ k, Function.Injective (B k))
    (hunit_x : ∀ k, x (k + 1) = x k + p k)
    (hunit_tilde : ∀ k, x_tilde (k + 1) = x_tilde k + p_tilde k)
    (hsearch_x : ∀ k, B k (p k) = -grad k)
    (hsearch_tilde : ∀ k, B_tilde k (p_tilde k) = -grad_tilde k)
    (hgrad_x : ∀ k, HasGradientAt f (grad k) (x k))
    (hgrad_ftilde : ∀ k, HasGradientAt ftilde (grad_tilde k) (x_tilde k))
    (hsr1_x :
      ∀ k,
        let sk := x (k + 1) - x k
        let yk := grad (k + 1) - grad k
        ⟪yk - B k sk, sk⟫ ≠ 0)
    (hsr1_tilde :
      ∀ k,
        let sk := x_tilde (k + 1) - x_tilde k
        let yk := grad_tilde (k + 1) - grad_tilde k
        ⟪yk - B_tilde k sk, sk⟫ ≠ 0)
    (hbfgs_x1 :
      ∀ k,
        let sk := x (k + 1) - x k
        ⟪B k sk, sk⟫ ≠ 0)
    (hbfgs_x2 :
      ∀ k,
        let sk := x (k + 1) - x k
        let yk := grad (k + 1) - grad k
        ⟪yk, sk⟫ ≠ 0)
    (hbfgs_tilde1 :
      ∀ k,
        let sk := x_tilde (k + 1) - x_tilde k
        ⟪B_tilde k sk, sk⟫ ≠ 0)
    (hbfgs_tilde2 :
      ∀ k,
        let sk := x_tilde (k + 1) - x_tilde k
        let yk := grad_tilde (k + 1) - grad_tilde k
        ⟪yk, sk⟫ ≠ 0)
    (hupdate :
      (((∀ k,
          let sk := x (k + 1) - x k
          let yk := grad (k + 1) - grad k
          let uk := yk - B k sk
          B (k + 1) = B k + (1 / ⟪uk, sk⟫) • (((innerSL ℝ) uk).smulRight uk)) ∧
        (∀ k,
          let sk := x_tilde (k + 1) - x_tilde k
          let yk := grad_tilde (k + 1) - grad_tilde k
          let uk := yk - B_tilde k sk
          B_tilde (k + 1) =
            B_tilde k + (1 / ⟪uk, sk⟫) • (((innerSL ℝ) uk).smulRight uk))) ∨
       ((∀ k,
          let sk := x (k + 1) - x k
          let yk := grad (k + 1) - grad k
          B (k + 1) =
            B k
              - (1 / ⟪B k sk, sk⟫) • (((innerSL ℝ) (B k sk)).smulRight (B k sk))
              + (1 / ⟪yk, sk⟫) • (((innerSL ℝ) yk).smulRight yk)) ∧
        (∀ k,
          let sk := x_tilde (k + 1) - x_tilde k
          let yk := grad_tilde (k + 1) - grad_tilde k
          B_tilde (k + 1) =
            B_tilde k
              - (1 / ⟪B_tilde k sk, sk⟫) • (((innerSL ℝ) (B_tilde k sk)).smulRight (B_tilde k sk))
              + (1 / ⟪yk, sk⟫) • (((innerSL ℝ) yk).smulRight yk))))
    )
    :
    ∀ k, x k = S (x_tilde k) + s := by
  sorry

end «problem-90»
