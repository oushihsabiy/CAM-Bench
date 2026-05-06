import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-143»

def l2Norm {K : ℕ} (u : Fin K → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin K, (u i) ^ 2)

/-
Let x ∈ ℝ^n be the decision variable. Let q ∈ ℝ^n, r ∈ ℝ, A ∈ ℝ^{m× n}, b ∈ ℝ^m, and let Pᵢ ∈ S_ +
^n
for i = 0, ..., K, where S_ + ^n denotes the set of symmetric positive semidefinite n× n matrices.
Define mathcal E = {P₀ + \sum_{i = 1}^K uᵢ Pᵢ | u = (u₁, ..., u_K)∈R^K, ‖u‖_2 ≤ 1}. Consider the
robust quadratic program minimize & sup_{P∈mathcal E}(frac12 xᵀ P x + qᵀ x + r); subject to
& Ax ≤ b, array where Ax ≤ b is interpreted componentwise.
-/
structure RobustQuadraticProgram (n m K : ℕ) where
  q : Fin n → ℝ
  r : ℝ
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  P0 : Matrix (Fin n) (Fin n) ℝ
  Pi : Fin K → Matrix (Fin n) (Fin n) ℝ
  P0_symm : P0.IsSymm
  P0_psd : ∀ x : Fin n → ℝ, 0 ≤ dotProduct x (P0.mulVec x)
  Pi_symm : ∀ i : Fin K, (Pi i).IsSymm
  Pi_psd : ∀ i : Fin K, ∀ x : Fin n → ℝ, 0 ≤ dotProduct x ((Pi i).mulVec x)

def RobustQuadraticProgram.uncertainMatrix
    {n m K : ℕ} (p : RobustQuadraticProgram n m K) (u : Fin K → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  p.P0 + ∑ i : Fin K, (u i) • p.Pi i

def RobustQuadraticProgram.uncertaintySet
    {n m K : ℕ} (p : RobustQuadraticProgram n m K) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  {P | ∃ u : Fin K → ℝ, l2Norm u ≤ 1 ∧ P = p.uncertainMatrix u}

def RobustQuadraticProgram.isFeasible
    {n m K : ℕ} (p : RobustQuadraticProgram n m K) (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin m, (p.A.mulVec x) i ≤ p.b i

def RobustQuadraticProgram.pointObjective
    {n m K : ℕ} (p : RobustQuadraticProgram n m K)
    (P : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * dotProduct x (P.mulVec x) + dotProduct p.q x + p.r

def RobustQuadraticProgram.robustObjective
    {n m K : ℕ} (p : RobustQuadraticProgram n m K) (x : Fin n → ℝ) : ℝ :=
  sSup {y : ℝ | ∃ P ∈ p.uncertaintySet, y = RobustQuadraticProgram.pointObjective p P x}

/-
minimize & frac12 xᵀ P₀ x + frac12(\sum_{i = 1}^K (xᵀ Pᵢ x)^2)^{1/2} + qᵀ x + r; subject to &
Ax ≤ b, array
-/
structure ConvexQuadraticReformulation (n m K : ℕ) where
  base : RobustQuadraticProgram n m K

def ConvexQuadraticReformulation.quadraticTerms
    {n m K : ℕ} (p : ConvexQuadraticReformulation n m K) (x : Fin n → ℝ) :
    Fin K → ℝ :=
  fun i => dotProduct x ((p.base.Pi i).mulVec x)

def ConvexQuadraticReformulation.isFeasible
    {n m K : ℕ} (p : ConvexQuadraticReformulation n m K) (x : Fin n → ℝ) : Prop :=
  RobustQuadraticProgram.isFeasible p.base x

def ConvexQuadraticReformulation.objective
    {n m K : ℕ} (p : ConvexQuadraticReformulation n m K) (x : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * dotProduct x (p.base.P0.mulVec x) +
    (1 / 2 : ℝ) * l2Norm (p.quadraticTerms x) +
    dotProduct p.base.q x + p.base.r

/-
minimize & frac12 xᵀ P₀ x + ‖y‖_2 + qᵀ x + r; subject to & frac12 xᵀ Pᵢ x ≤ yᵢ,
i = 1, ..., K,; & Ax ≤ b, array with variables x∈mathbf ℝ^n and y∈R^K.
-/
structure SecondOrderConeReformulation (n m K : ℕ) where
  base : RobustQuadraticProgram n m K

def SecondOrderConeReformulation.objective
    {n m K : ℕ} (p : SecondOrderConeReformulation n m K)
    (x : Fin n → ℝ) (y : Fin K → ℝ) : ℝ :=
  (1 / 2 : ℝ) * dotProduct x (p.base.P0.mulVec x) + l2Norm y + dotProduct p.base.q x + p.base.r

def SecondOrderConeReformulation.quadraticConstraint
    {n m K : ℕ} (p : SecondOrderConeReformulation n m K)
    (x : Fin n → ℝ) (y : Fin K → ℝ) (i : Fin K) : Prop :=
  (1 / 2 : ℝ) * dotProduct x ((p.base.Pi i).mulVec x) ≤ y i

def SecondOrderConeReformulation.isFeasible
    {n m K : ℕ} (p : SecondOrderConeReformulation n m K)
    (x : Fin n → ℝ) (y : Fin K → ℝ) : Prop :=
  (∀ i : Fin K, p.quadraticConstraint x y i) ∧
    RobustQuadraticProgram.isFeasible p.base x

def SecondOrderConeReformulation.canonicalY
    {n m K : ℕ} (p : SecondOrderConeReformulation n m K)
    (x : Fin n → ℝ) : Fin K → ℝ :=
  fun i => (1 / 2 : ℝ) * dotProduct x ((p.base.Pi i).mulVec x)

/-
Let x ∈ ℝ^n be the decision variable. Let q ∈ ℝ^n, r ∈ ℝ, A ∈ ℝ^{m× n}, b ∈ ℝ^m, and let Pᵢ ∈ S_ +
^n
for i = 0, ..., K, where S_ + ^n is the set of symmetric positive semidefinite n× n matrices. Define
mathcal E = {P₀ + \sum_{i = 1}^K uᵢ Pᵢ | u = (u₁, ..., u_K)∈R^K, ‖u‖_2 ≤ 1}. Consider the robust
quadratic program minimize & sup_{P∈mathcal E}(frac12 xᵀ P x + qᵀ x + r); subject to & Ax ≤
b, array where Ax ≤ b is componentwise. Prove that this problem is equivalent to the convex
optimization problem minimize & frac12 xᵀ P₀ x + frac12(\sum_{i = 1}^K (xᵀ Pᵢ
x)^2)^{1/2} + qᵀ x + r; subject to & Ax ≤ b, array
-/
theorem robust_quadratic_program_equiv_convex_reformulation
    {n m K : ℕ} (p : RobustQuadraticProgram n m K) :
    ∀ x : Fin n → ℝ,
      (RobustQuadraticProgram.isFeasible p x ↔
        ConvexQuadraticReformulation.isFeasible ({ base := p } : ConvexQuadraticReformulation n m K) x) ∧
      RobustQuadraticProgram.robustObjective p x =
        ConvexQuadraticReformulation.objective ({ base := p } : ConvexQuadraticReformulation n m K) x := by
  sorry

/-
Let x ∈ ℝ^n be the decision variable. Let q ∈ ℝ^n, r ∈ ℝ, A ∈ ℝ^{m× n}, b ∈ ℝ^m, and let Pᵢ ∈ S_ +
^n
for i = 0, ..., K, where S_ + ^n is the set of symmetric positive semidefinite n× n matrices. Define
mathcal E = {P₀ + \sum_{i = 1}^K uᵢ Pᵢ | u = (u₁, ..., u_K)∈R^K, ‖u‖_2 ≤ 1}. Consider the robust
quadratic program minimize & sup_{P∈mathcal E}(frac12 xᵀ P x + qᵀ x + r); subject to & Ax ≤
b, array where Ax ≤ b is componentwise. Prove that this problem is also equivalent to minimize &
frac12 xᵀ P₀ x + ‖y‖_2 + qᵀ x + r; subject to & frac12 xᵀ Pᵢ x ≤ yᵢ, i = 1, ...,
K,; & Ax ≤ b, array with variables x∈mathbf ℝ^n and y∈R^K. In particular, prove that the
robust problem can be formulated as a second - order cone program.
-/
theorem robust_quadratic_program_equiv_second_order_cone_reformulation
    {n m K : ℕ} (p : RobustQuadraticProgram n m K) :
    ∀ x : Fin n → ℝ,
      (RobustQuadraticProgram.isFeasible p x ↔
        ∃ y : Fin K → ℝ,
          SecondOrderConeReformulation.isFeasible
            ({ base := p } : SecondOrderConeReformulation n m K) x y) ∧
      (RobustQuadraticProgram.isFeasible p x →
        SecondOrderConeReformulation.isFeasible
          ({ base := p } : SecondOrderConeReformulation n m K) x
          (SecondOrderConeReformulation.canonicalY
            ({ base := p } : SecondOrderConeReformulation n m K) x) ∧
        RobustQuadraticProgram.robustObjective p x =
          SecondOrderConeReformulation.objective
            ({ base := p } : SecondOrderConeReformulation n m K) x
            (SecondOrderConeReformulation.canonicalY
              ({ base := p } : SecondOrderConeReformulation n m K) x) ∧
        RobustQuadraticProgram.robustObjective p x =
          sInf {z : ℝ | ∃ y : Fin K → ℝ,
            SecondOrderConeReformulation.isFeasible
              ({ base := p } : SecondOrderConeReformulation n m K) x y ∧
            z =
              SecondOrderConeReformulation.objective
                ({ base := p } : SecondOrderConeReformulation n m K) x y}) := by
  sorry

end «problem-143»
