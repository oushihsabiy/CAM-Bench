import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-73»
/-
For the equality - constrained problem with feasible point x, the Newton step δ x is the primal
component of a pair (δ x, nu) satisfying the KKT system [∇^2 f(x) & Aᵀ; A & 0] [δ x; nu] = [ - ∇
f(x);
0].
-/
def newtonStep
    {n m : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (xhat : Fin n → ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) : Fin n → ℝ :=
  by
    classical
    by_cases hsol :
        Nonempty
          { p : (Fin n → ℝ) × (Fin m → ℝ) //
              (∀ i : Fin n,
                (∑ j : Fin n,
                    ((fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) xhat)
                      (Pi.single i (1 : ℝ))) * p.1 j)
                  + ∑ j : Fin m, (A.transpose i j) * p.2 j
                  = -((fderiv ℝ f xhat) (Pi.single i (1 : ℝ)))) ∧
              (∀ i : Fin m, ∑ j : Fin n, A i j * p.1 j = 0) }
    · exact (Classical.choice hsol).1.1
    · exact 0

/-
The Newton decrement at x is defined by λ(x) = (- ∇ f(x)ᵀ δ x)^{1/2} = (δ xᵀ ∇^2 f(x) δ x)^{1/2},
where δ x is the Newton step at x.
-/
def newtonDecrement
    {n m : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (xhat : Fin n → ℝ)
    (_ : Matrix (Fin m) (Fin n) ℝ)
    (dx : Fin n → ℝ) : ℝ :=
  Real.sqrt (-∑ i : Fin n, ((fderiv ℝ f xhat) (Pi.single i (1 : ℝ))) * dx i)

/-
[BLOCK Exercise 8.2 | 3 | opt_prob] Consider the optimization problem minimize ∇f(x)ᵀy subject to Ay
= 0, yᵀ∇²f(x)y ≤ 1, where y ∈ ℝⁿ.
-/
structure QuadraticallyConstrainedLinearProgram where
  n : ℕ
  m : ℕ
  grad : Fin n → ℝ
  hess : Matrix (Fin n) (Fin n) ℝ
  A : Matrix (Fin m) (Fin n) ℝ

def QuadraticallyConstrainedLinearProgram.objective (P : QuadraticallyConstrainedLinearProgram) :
    (Fin P.n → ℝ) → ℝ :=
  fun y => dotProduct P.grad y

def QuadraticallyConstrainedLinearProgram.isFeasible (P : QuadraticallyConstrainedLinearProgram) :
    (Fin P.n → ℝ) → Prop :=
  fun y => P.A.mulVec y = 0 ∧ dotProduct y (P.hess.mulVec y) ≤ 1

/-
Let f: ℝⁿ → ℝ be a convex twice - differentiable function, let A ∈ ℝ^{p×n} satisfy rank(A) = p, and
let b ∈ ℝᵖ. Let x ∈ ℝⁿ satisfy Ax = b. Define the Newton step δx ∈ ℝⁿ as the x - component of the
unique solution (δx, ν) ∈ ℝⁿ × ℝᵖ of [∇²f(x) Aᵀ; A 0] [δx; ν] = [ - ∇f(x); 0]. Define the Newton
decrement by λ(x) = (- ∇f(x)ᵀ δx)^{1/2} = (δxᵀ ∇²f(x) δx)^{1/2}. Assume that [∇²f(x) Aᵀ; A 0] is
nonsingular and that λ(x) > 0. Consider the quadratically constrained linear program minimize
∇f(x)ᵀy subject to Ay = 0, yᵀ ∇²f(x) y ≤ 1, where y ∈ ℝⁿ. Prove that its unique solution is y = δx /
λ(x).
-/
theorem qcqp_unique_solution_eq_normalized_newton_step
    {n m : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (xhat : Fin n → ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (Δx : Fin n → ℝ)
    (hC2 : ContDiffAt ℝ 2 f xhat)
    (hconvex : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f)
    (hrank : Module.finrank ℝ (LinearMap.range A.toLin') = m)
    (hfeas : A.mulVec xhat = b)
    (hkkt_nonsingular :
      Function.Bijective
        (fun p : (Fin n → ℝ) × (Fin m → ℝ) =>
          ( (fun i : Fin n =>
                (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single i (1 : ℝ))) xhat) p.1
                  + ∑ j : Fin m, (A.transpose i j) * p.2 j),
            (fun i : Fin m => ∑ j : Fin n, A i j * p.1 j) )))
    (hstep : Δx = newtonStep f xhat A)
    (hlam_pos : 0 < newtonDecrement f xhat A Δx) :
    let P : QuadraticallyConstrainedLinearProgram :=
      { n := n
        m := m
        grad := fun i => (fderiv ℝ f xhat) (Pi.single i (1 : ℝ))
        hess := fun i j =>
          (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) xhat)
            (Pi.single i (1 : ℝ))
        A := A }
    QuadraticallyConstrainedLinearProgram.isFeasible P
        (fun i => Δx i / newtonDecrement f xhat A Δx) ∧
      (∀ z : Fin n → ℝ,
          QuadraticallyConstrainedLinearProgram.isFeasible P z →
          QuadraticallyConstrainedLinearProgram.objective P
              (fun i => Δx i / newtonDecrement f xhat A Δx) ≤
            QuadraticallyConstrainedLinearProgram.objective P z) ∧
      (∀ y : Fin n → ℝ,
          QuadraticallyConstrainedLinearProgram.isFeasible P y →
          (∀ z : Fin n → ℝ,
              QuadraticallyConstrainedLinearProgram.isFeasible P z →
              QuadraticallyConstrainedLinearProgram.objective P y ≤
                QuadraticallyConstrainedLinearProgram.objective P z) →
          y = (fun i => Δx i / newtonDecrement f xhat A Δx)) := by
  sorry

end «problem-73»
