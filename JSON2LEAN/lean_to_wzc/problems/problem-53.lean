import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-53»

def l2Norm3 (v : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (∑ k : Fin 3, (v k) ^ 2)
/-
For an optimization problem with objective $f_0(x)$ and equality constraints $h_i(x) = 0$, the
Lagrangian is the function $L(x, nu) = f_0(x)+sum_i nu_i h_i(x)$, where $ nu_i$ are the associated
dual variables.
-/
def Lagrangian {n m : ℕ} (f₀ : (Fin n → ℝ) → ℝ) (h : Fin m → (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → (Fin m → ℝ) → ℝ :=
  fun x ν => f₀ x + ∑ i : Fin m, ν i * h i x

/-
Dual variables are the multipliers associated with the constraints in a Lagrangian. For equality
constraints $h_i(x) = 0$, they are unrestricted scalars or vectors $ nu_i$ appearing in (L(x, nu) =
f_0(x)+sum_i nu_i h_i(x) ).
-/
def DualVariables (m : ℕ) := Fin m → ℝ

/-
Given a Lagrangian $L(x, nu)$, the Lagrange dual function is $g( nu) = inf_x L(x, nu)$. More
generally, if there are multiple blocks of primal variables, then $g( nu) = inf_{x, y} L(x, y, nu)$.
-/
structure PrimalNonsmoothOptimizationProblem (n m : ℕ) where
  h : ℝ → ℝ
  c : Fin n → ℝ
  A : Fin m → (Fin n → ℝ) → (Fin 3 → ℝ)
  b : Fin m → Fin 3 → ℝ

def PrimalNonsmoothOptimizationProblem.objective {n m : ℕ}
    (P : PrimalNonsmoothOptimizationProblem n m)
    (x : Fin n → ℝ)
    (y : Fin m → Fin 3 → ℝ) : ℝ :=
  (∑ i : Fin m, P.h (l2Norm3 (y i))) - ∑ j : Fin n, P.c j * x j

def PrimalNonsmoothOptimizationProblem.feasible {n m : ℕ}
    (P : PrimalNonsmoothOptimizationProblem n m)
    (x : Fin n → ℝ)
    (y : Fin m → Fin 3 → ℝ) : Prop :=
  ∀ i : Fin m, (fun k : Fin 3 => P.A i x k + P.b i k - y i k) = 0

def PrimalNonsmoothOptimizationProblem.isSolution {n m : ℕ}
    (P : PrimalNonsmoothOptimizationProblem n m)
    (x : Fin n → ℝ)
    (y : Fin m → Fin 3 → ℝ) : Prop :=
  P.feasible x y ∧
    ∀ x' : Fin n → ℝ, ∀ y' : Fin m → Fin 3 → ℝ,
      P.feasible x' y' → P.objective x y ≤ P.objective x' y'

/-
The corresponding Lagrange dual problem is [ begin{ } text{maximize} & sum_{i = 1}^m (b_i^T nu_i- |
nu_i |_2- frac{1}{2} | nu_i |_2^2) text{subject to} & sum_{i = 1}^m A_i^T nu_i = c, end{ } ] with
variables ( nu_i in mathbf{R}^3 ) for (i = 1,..., m ).
-/
structure DualNonsmoothOptimizationProblem (n m : ℕ) where
  c : Fin n → ℝ
  A : Fin m → Matrix (Fin 3) (Fin n) ℝ
  b : Fin m → Fin 3 → ℝ

def DualNonsmoothOptimizationProblem.objective
    {n m : ℕ} (P : DualNonsmoothOptimizationProblem n m) : (Fin m → Fin 3 → ℝ) → ℝ :=
  fun nu =>
    ∑ i : Fin m,
      ((∑ k : Fin 3, P.b i k * nu i k) -
        l2Norm3 (nu i) - (1 / 2 : ℝ) * l2Norm3 (nu i) ^ 2)

def DualNonsmoothOptimizationProblem.feasible
    {n m : ℕ} (P : DualNonsmoothOptimizationProblem n m) : (Fin m → Fin 3 → ℝ) → Prop :=
  fun nu =>
    ∀ j : Fin n,
      ∑ i : Fin m, ((P.A i).transpose.mulVec (nu i)) j = P.c j

def DualNonsmoothOptimizationProblem.isSolution
    {n m : ℕ} (P : DualNonsmoothOptimizationProblem n m) : (Fin m → Fin 3 → ℝ) → Prop :=
  fun nu =>
    P.feasible nu ∧
      ∀ nu' : Fin m → Fin 3 → ℝ,
        P.feasible nu' → P.objective nu' ≤ P.objective nu

/-
Let (m, n in mathbf{N} ). For each (i = 1,..., m ), let (A_i in mathbf{R}^{3 times n} ), (b_i in
mathbf{R}^3 ), and let (c in mathbf{R}^n ). Define (h: mathbf{R} to mathbf{R} ) by [ h(u) =
begin{cases} frac{(u-1)^2}{2}, & u ge 1, 0, & u < 1. end{cases} ] Let ( | cdot |_2 ) denote the
Euclidean norm on ( mathbf{R}^3 ). Consider the primal nonsmooth optimization problem. For dual
variables ( nu_i in mathbf{R}^3 ), the Lagrangian is [ L(x, y, nu) = sum_{i = 1}^m bigl(h( |y_i
|_2)+ nu_i^T b_i- nu_i^T y_i bigr)+ Bigl(sum_{i = 1}^m A_i^T nu_i-c Bigr)^T x. ] Prove that the
Lagrange dual function is [ g( nu) = begin{cases} displaystyle sum_{i = 1}^m (b_i^T nu_i- | nu_i
|_2- frac{1}{2} | nu_i |_2^2), & text{if} sum_{i = 1}^m A_i^T nu_i = c, - infty, & text{otherwise},
end{cases} ] and therefore the Lagrange dual problem is Lagrange dual problem.
-/
theorem lagrangeDualFunction_eq_piecewise_for_nonsmooth_problem
    {n m : ℕ}
    (P : PrimalNonsmoothOptimizationProblem n m)
    (h_def : P.h = fun u : ℝ => if 1 ≤ u then (u - 1) ^ 2 / 2 else 0) :
    ∀ ν : Fin m → Fin 3 → ℝ,
      let D : DualNonsmoothOptimizationProblem n m :=
        { c := P.c
          A := fun i => fun k j => P.A i (Pi.single j (1 : ℝ)) k
          b := P.b }
      (sInf
        (Set.range
          (fun xy : (Fin n → ℝ) × (Fin m → Fin 3 → ℝ) =>
            show EReal from
              (((∑ i : Fin m,
                    (P.h (l2Norm3 (xy.2 i)) + (∑ k : Fin 3, ν i k * P.b i k) -
                      (∑ k : Fin 3, ν i k * xy.2 i k))) +
                  ((∑ i : Fin m, ∑ k : Fin 3, ν i k * P.A i xy.1 k) -
                    ∑ j : Fin n, P.c j * xy.1 j)) : ℝ))) =
        if ∀ j : Fin n,
            ∑ i : Fin m, ∑ k : Fin 3, P.A i (Pi.single j (1 : ℝ)) k * ν i k = P.c j then
          ((∑ i : Fin m,
              ((∑ k : Fin 3, P.b i k * ν i k) -
                l2Norm3 (ν i) - (1 / 2 : ℝ) * l2Norm3 (ν i) ^ 2) : ℝ) : EReal)
        else ⊥) ∧
      (D.feasible ν ↔
        ∀ j : Fin n,
          ∑ i : Fin m, ∑ k : Fin 3, P.A i (Pi.single j (1 : ℝ)) k * ν i k = P.c j) ∧
      (D.objective ν =
        ∑ i : Fin m,
          ((∑ k : Fin 3, P.b i k * ν i k) -
            l2Norm3 (ν i) - (1 / 2 : ℝ) * l2Norm3 (ν i) ^ 2)) := by
  sorry

end «problem-53»
