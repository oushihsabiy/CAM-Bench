import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-32»

/- [BLOCK Exercise 8.20 | 12 | defn]
An ellipsoid in ℝ^n is a set of the form
{x∈ ℝ^n| (x-c)ᵀ P (x-c)≤ 1},
for some center $c∈ ℝ^n and some symmetric positive definite matrix P∈ S^n.
-/
def ellipsoid {n : ℕ} (c : Fin n → ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ)
    (_hP_symm : P.IsSymm)
    (_hP_pos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < dotProduct x (P.mulVec x)) :
    Set (Fin n → ℝ) :=
  {x | dotProduct (x - c) (P.mulVec (x - c)) ≤ 1}

/- [BLOCK Exercise 8.20 | 13 | opt_prob]
Let
C={x∈ ℝ^n| x₁A_1+x₂A_2+·s+x_nA_npreceq B},
where A₁,dots,Aₙ,B∈ S^m, S^m is the set of real symmetric m× m matrices, and for X,Y∈ S^m,
Xpreceq Y means that Y-X is positive semidefinite. Assume that C has nonempty interior. Let
x_ac be the minimizer of
φ(x)=-logdet(B-x₁A_1-x₂A_2-·s-x_nA_n)
over the domain
{x∈ ℝ^n| B-x₁A_1-x₂A_2-·s-x_nA_nsucc 0},
where Xsucc 0 means that X is positive definite.
-/
structure LogDetAnalyticCenterProblem (n m : ℕ) where
  A : Fin n → Matrix (Fin m) (Fin m) ℝ
  B : Matrix (Fin m) (Fin m) ℝ
  A_symm : ∀ i, (A i).IsSymm
  B_symm : B.IsSymm
  interior_nonempty :
    ∃ x : Fin n → ℝ,
      Matrix.PosDef (B - ∑ i, (x i) • A i)
  x_ac : Fin n → ℝ

def LogDetAnalyticCenterProblem.slack {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m) (x : Fin n → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  p.B - ∑ i, (x i) • p.A i

def LogDetAnalyticCenterProblem.feasible {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m) (x : Fin n → ℝ) : Prop :=
  Matrix.PosSemidef (p.slack x)

def LogDetAnalyticCenterProblem.strictlyFeasible {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m) (x : Fin n → ℝ) : Prop :=
  Matrix.PosDef (p.slack x)

def LogDetAnalyticCenterProblem.constraintSet {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m) : Set (Fin n → ℝ) :=
  {x | p.feasible x}

def LogDetAnalyticCenterProblem.domain {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m) : Set (Fin n → ℝ) :=
  {x | p.strictlyFeasible x}

def LogDetAnalyticCenterProblem.objective {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m) (x : Fin n → ℝ) : ℝ :=
  -Real.log (Matrix.det (p.slack x))

def LogDetAnalyticCenterProblem.IsAnalyticCenter {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m) (x_ac : Fin n → ℝ) : Prop :=
  x_ac ∈ p.domain ∧
    ∀ x ∈ p.domain, p.objective x_ac ≤ p.objective x

/-
Exercise 8.20 | 14 | thm

Let C = {x ∈ ℝⁿ | x₁A₁ + x₂A₂ + ··· + xₙAₙ ⪯ B}, where A₁, …, Aₙ, B ∈ Sᵐ, Sᵐ is the set of real
symmetric m × m matrices, and for X, Y ∈ Sᵐ, X ⪯ Y means that Y - X is positive semidefinite. Assume
that C has nonempty interior. Let x_ac be the minimizer of φ(x) = -log det(B - x₁A₁ - x₂A₂ - ··· -
xₙAₙ) over the domain {x ∈ ℝⁿ | B - x₁A₁ - x₂A₂ - ··· - xₙAₙ ≻ 0}, where X ≻ 0 means that X is
positive definite. Let H be the Hessian of φ at x_ac. Define E_inner = {x ∈ ℝⁿ | (x - x_ac)ᵀ H (x -
x_ac) ≤ q 1} and E_outer = {x ∈ ℝⁿ | (x - x_ac)ᵀ H (x - x_ac) ≤ q m(m - 1)}. Show that E_inner ⊆ C ⊆
E_outer.
-/
theorem analyticCenter_ellipsoid_bounds
    {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m)
    (hx_ac : p.IsAnalyticCenter p.x_ac)
    (H : Matrix (Fin n) (Fin n) ℝ)
    (hH_hessian :
      H = fun i j =>
        (fderiv ℝ
          (fun y : Fin n → ℝ =>
            (fderiv ℝ p.objective y (Pi.single j (1 : ℝ)))) p.x_ac)
          (Pi.single i (1 : ℝ)))
    (hH_symm : H.IsSymm)
    (hH_pos : ∀ u : Fin n → ℝ, u ≠ 0 → 0 < dotProduct u (H.mulVec u)) :
    {x | dotProduct (x - p.x_ac) (H.mulVec (x - p.x_ac)) ≤ 1} ⊆ p.constraintSet ∧
      p.constraintSet ⊆
        {x | dotProduct (x - p.x_ac) (H.mulVec (x - p.x_ac)) ≤ (m * (m - 1) : ℝ)} := by
  sorry

end «problem-32»
