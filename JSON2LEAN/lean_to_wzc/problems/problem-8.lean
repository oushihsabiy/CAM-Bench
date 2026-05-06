import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-8»
/-
For a function (f: X to mathbf{R} cup {+ infty}), [ operatorname*{argmin}_{x in X} f(x) = {x in X
mid f x le f z text{for all} z in X}. ]
-/
def argmin {X : Type*} (f : X → EReal) : Set X :=
  {x | ∀ z : X, f x ≤ f z}

/-
For an optimization problem with objective function (f) over a feasible set (S), the optimal value
is (\inf_{x in S} f(x)) for a minimization problem and (sup_{x in S} f(x)) for a maximization
problem.
-/
def optimalValueMin {X : Type*} (f : X → EReal) (S : Set X) : EReal :=
  sInf (f '' S)

def optimalValueMax {X : Type*} (f : X → EReal) (S : Set X) : EReal :=
  sSup (f '' S)

/-
[ begin{} text{maximize} & c_i text{subject to} & y^{(j)} ge 0, A^T y^{(j)} = c, (b^{(j)})^T
y^{(j)} = c^T x^{(j)}, j = 1, ..., r, end{} ]
-/
structure InverseOptimalityMaximizationLP (n m r : ℕ) where
  i : Fin n
  c : Fin n → ℝ
  A : Matrix (Fin m) (Fin n) ℝ
  x : Fin r → (Fin n → ℝ)
  b : Fin r → (Fin m → ℝ)
  y : Fin r → (Fin m → ℝ)

def InverseOptimalityMaximizationLP.is_feasible
    {n m r : ℕ} (P : InverseOptimalityMaximizationLP n m r) : Prop :=
  (∀ j : Fin r, ∀ i : Fin m, P.b j i ≤ Matrix.mulVec P.A (P.x j) i) ∧
  (∀ j : Fin r, ∀ k : Fin m, 0 ≤ P.y j k) ∧
  (∀ j : Fin r, Matrix.mulVec P.A.transpose (P.y j) = P.c) ∧
  (∀ j : Fin r, dotProduct (P.b j) (P.y j) = dotProduct P.c (P.x j))

def InverseOptimalityMaximizationLP.feasibleSet
    {n m r : ℕ} : Set (InverseOptimalityMaximizationLP n m r) :=
  {P | P.is_feasible}

def InverseOptimalityMaximizationLP.objective
    {n m r : ℕ} (P : InverseOptimalityMaximizationLP n m r) (i : Fin n) : ℝ :=
  P.c i

/-
[ begin{} text{minimize} & c_i text{subject to} & y^{(j)} ge 0, A^T y^{(j)} = c, (b^{(j)})^T
y^{(j)} = c^T x^{(j)}, j = 1, ..., r, end{} ] with variables (c in mathbf{R}^n) and (y^{(1)}, ...,
y^{(r)} in mathbf{R}^m).
-/
structure InverseOptimalityMinimizationLP (n m r : ℕ) where
  c : Fin n → ℝ
  A : Matrix (Fin m) (Fin n) ℝ
  x : Fin r → (Fin n → ℝ)
  b : Fin r → (Fin m → ℝ)
  y : Fin r → (Fin m → ℝ)
  objectiveIndex : Fin n
  primal_feasible : ∀ j : Fin r, ∀ i : Fin m, b j i ≤ Matrix.mulVec A (x j) i
  dual_nonneg : ∀ j : Fin r, ∀ i : Fin m, 0 ≤ y j i
  dual_feasible : ∀ j : Fin r, Matrix.mulVec Aᵀ (y j) = c
  strong_duality_eq : ∀ j : Fin r, dotProduct (b j) (y j) = dotProduct c (x j)

def InverseOptimalityMinimizationLP.is_feasible
    {n m r : ℕ} (P : InverseOptimalityMinimizationLP n m r) : Prop :=
  (∀ j : Fin r, ∀ i : Fin m, P.b j i ≤ Matrix.mulVec P.A (P.x j) i) ∧
  (∀ j : Fin r, ∀ i : Fin m, 0 ≤ P.y j i) ∧
  (∀ j : Fin r, Matrix.mulVec P.Aᵀ (P.y j) = P.c) ∧
  (∀ j : Fin r, dotProduct (P.b j) (P.y j) = dotProduct P.c (P.x j))

def InverseOptimalityMinimizationLP.objective
    {n m r : ℕ} (P : InverseOptimalityMinimizationLP n m r) : ℝ :=
  P.c P.objectiveIndex

/-
Let (A in mathbf{R}^{m \times n}) be given. For each (j = 1, ..., r), let (b^{(j)} in mathbf{R}^m)
and (x^{(j)} in mathbf{R}^n). Define [ C = left {c in mathbf{R}^n mid x^{(j)} in
operatorname*{argmin}_{x in mathbf{R}^n} {c^T x mid Ax ge b^{(j)}} text{for every} j = 1, ..., r
right}, ] where (Ax ge b^{(j)}) is interpreted componentwise. Prove that a vector (c in
mathbf{R}^n) belongs to (C) if and only if for each (j = 1, ..., r) there exists (y^{(j)} in
mathbf{R}^m) such that [ y^{(j)} ge 0, A^T y^{(j)} = c, (b^{(j)})^T y^{(j)} = c^T x^{(j)}. ]
-/
def inverseOptimalitySet
    {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin r → (Fin n → ℝ))
    (b : Fin r → (Fin m → ℝ)) : Set (Fin n → ℝ) :=
  {c | ∀ j : Fin r,
    (∀ i : Fin m, b j i ≤ Matrix.mulVec A (x j) i) ∧
    x j ∈ argmin (fun x' : Fin n → ℝ =>
      if ∀ i : Fin m, b j i ≤ Matrix.mulVec A x' i
      then ((dotProduct c x' : ℝ) : EReal)
      else ⊤)}

theorem mem_inverseOptimalitySet_iff_exists_dualCertificates
    {n m r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin r → (Fin n → ℝ))
    (b : Fin r → (Fin m → ℝ))
    (c : Fin n → ℝ) :
    c ∈ inverseOptimalitySet A x b ↔
      ∀ j : Fin r,
        (∀ i : Fin m, b j i ≤ Matrix.mulVec A (x j) i) ∧
        ∃ y : Fin m → ℝ,
          (∀ i : Fin m, 0 ≤ y i) ∧
          Matrix.mulVec Aᵀ y = c ∧
          dotProduct (b j) y = dotProduct c (x j) := by
  sorry

/-
Let (A in mathbf{R}^{m \times n}) be given. For each (j = 1, ..., r), let (b^{(j)} in mathbf{R}^m)
and (x^{(j)} in mathbf{R}^n). Define [ C = left {c in mathbf{R}^n mid x^{(j)} in
operatorname*{argmin}_{x in mathbf{R}^n} {c^T x mid Ax ge b^{(j)}} text{for every} j = 1, ..., r
right}, ] where (Ax ge b^{(j)}) is interpreted componentwise. For a fixed index (i in {1, ..., n}
), define [ c_i^{max} = sup {c_i mid c in C}, c_i^{min} = inf {c_i mid c in C}. ] Prove that
(c_i^{max}) and (c_i^{min}) are the optimal values of the linear programs inverse optimality
maximization LP and inverse optimality minimization LP, respectively.
-/
theorem inverseOptimalityExtremalObjectiveValues_eq_optimalValues
    {n m r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin r → (Fin n → ℝ))
    (b : Fin r → (Fin m → ℝ))
    (i : Fin n) :
    optimalValueMax
        (fun P : InverseOptimalityMaximizationLP n m r => ((P.objective P.i : ℝ) : EReal))
        {P | P.A = A ∧ P.x = x ∧ P.b = b ∧ P.i = i ∧ P.is_feasible} =
      sSup (((fun c : Fin n → ℝ => ((c i : ℝ) : EReal)) '' inverseOptimalitySet A x b)) ∧
    optimalValueMin
        (fun P : InverseOptimalityMinimizationLP n m r => ((P.objective : ℝ) : EReal))
        {P | P.A = A ∧ P.x = x ∧ P.b = b ∧ P.objectiveIndex = i ∧ P.is_feasible} =
      sInf (((fun c : Fin n → ℝ => ((c i : ℝ) : EReal)) '' inverseOptimalitySet A x b)) := by
  sorry

end «problem-8»
