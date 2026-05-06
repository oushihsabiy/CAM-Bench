import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-195»

/- [BLOCK chapter5 Ex.11 | 13 | opt_prob]
Let A∈S^n, i.e. A is an n× n real symmetric matrix. Consider the optimization problem on the
unit sphere
S^n-1={x∈ℝ^n:‖x‖_2=1}
given by
min_x∈ℝ^n x^→p A x quadsubject toquad ‖x‖_2=1.
On the unit sphere, x^→p A x is the Rayleigh quotient of A. Denote the smallest and largest
eigenvalues of A by λ_min and λ_max, respectively.
-/
structure RayleighQuotientMinimization (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  symmetric : A.IsSymm

def RayleighQuotientMinimization.feasibleSet {n : ℕ} (P : RayleighQuotientMinimization n) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ‖x‖ = 1}

def RayleighQuotientMinimization.objective {n : ℕ} (P : RayleighQuotientMinimization n) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => dotProduct x (P.A.mulVec x)

def RayleighQuotientMinimization.isFeasible {n : ℕ} (P : RayleighQuotientMinimization n)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ P.feasibleSet

def RayleighQuotientMinimization.isMinimizer {n : ℕ} (P : RayleighQuotientMinimization n)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  P.isFeasible x ∧ ∀ y, P.isFeasible y → P.objective x ≤ P.objective y

def RayleighQuotientMinimization.isMaximizer {n : ℕ} (P : RayleighQuotientMinimization n)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  P.isFeasible x ∧ ∀ y, P.isFeasible y → P.objective y ≤ P.objective x

/- [BLOCK chapter5 Ex.11 | 14 | thm]
Let A ∈ S^n, that is, A is an n × n real symmetric matrix. Consider the constrained optimization
problem on the unit sphere S^{n-1} = {x ∈ ℝ^n : ‖x‖_2 = 1} given by min_{x ∈ ℝ^n} x^→p A x, s.t.
‖x‖_2 = 1. Here, x^→p A x is the value of the Rayleigh quotient of the matrix A on the unit sphere.
Denote the smallest and largest eigenvalues of A by λ_{min} and λ_{max}, respectively. Prove that
the set of global minimizers of Rayleigh quotient minimization is exactly the set of all unit
eigenvectors satisfying Ax = λ_{min} x, ‖x‖_2 = 1, and, under the same constraint, the set of global
maximizers of the function x^→p A x is exactly the set of all unit eigenvectors satisfying Ax =
λ_{max} x, ‖x‖_2 = 1.
-/
theorem rayleigh_quotient_minimizers_and_maximizers_are_unit_extreme_eigenvectors
    (n : ℕ) (hn : 0 < n) (P : RayleighQuotientMinimization n) :
    ∃ lmin lmax : ℝ,
      (Module.End.HasEigenvalue P.A.toLin' lmin ∧
        ∀ ν : ℝ, Module.End.HasEigenvalue P.A.toLin' ν → lmin ≤ ν) ∧
      (Module.End.HasEigenvalue P.A.toLin' lmax ∧
        ∀ ν : ℝ, Module.End.HasEigenvalue P.A.toLin' ν → ν ≤ lmax) ∧
      (∀ x : EuclideanSpace ℝ (Fin n),
        P.isMinimizer x ↔ ‖x‖ = 1 ∧ Module.End.HasEigenvector P.A.toLin' lmin x) ∧
      (∀ x : EuclideanSpace ℝ (Fin n),
        P.isMaximizer x ↔ ‖x‖ = 1 ∧ Module.End.HasEigenvector P.A.toLin' lmax x) := by
  sorry

/- [BLOCK chapter5 Ex.11 | 15 | thm]
Let A ∈ S^n, that is, A is an n × n real symmetric matrix. Consider the constrained optimization
problem on the unit sphere S^{n-1} = {x ∈ ℝ^n : ‖x‖_2 = 1} given by min_{x ∈ ℝ^n} x^→p A x, s.t.
‖x‖_2 = 1. Here, x^→p A x is the value of the Rayleigh quotient of the matrix A on the unit sphere.
Denote the smallest and largest eigenvalues of A by λ_{min} and λ_{max}, respectively. Let λ be an
eigenvalue of A. If λ is strictly minimal in the eigenvalue sequence, that is, it is an isolated
smallest eigenvalue (equivalently, there are no other eigenvalues smaller than it in some
neighborhood), prove that any unit eigenvector corresponding to λ is a strict local minimizer of
this constrained optimization problem; and explain that such points are in fact also global
minimizers.
-/
theorem isolated_smallest_eigenvalue_unit_eigenvector_is_strict_local_and_global_minimizer
    (n : ℕ) (hn : 0 < n) (P : RayleighQuotientMinimization n) (lam : ℝ)
    (hlam : Module.End.HasEigenvalue P.A.toLin' lam)
    (hiso : ∀ μ : ℝ, Module.End.HasEigenvalue P.A.toLin' μ → μ ≠ lam → lam < μ)
    (hsimple :
      ∀ x y : EuclideanSpace ℝ (Fin n),
        Module.End.HasEigenvector P.A.toLin' lam x →
        Module.End.HasEigenvector P.A.toLin' lam y →
        ∃ a : ℝ, y = a • x) :
    ∀ x : EuclideanSpace ℝ (Fin n),
      Module.End.HasEigenvector P.A.toLin' lam x ∧ ‖x‖ = 1 →
        (∃ r > 0, ∀ y : EuclideanSpace ℝ (Fin n),
          ‖y‖ = 1 → 0 < ‖y - x‖ → ‖y - x‖ < r → P.objective x < P.objective y) ∧
        P.isMinimizer x := by
  sorry

end «problem-195»
