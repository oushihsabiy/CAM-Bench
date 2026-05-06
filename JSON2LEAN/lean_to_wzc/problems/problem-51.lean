import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-51»
/-
A second-order cone program is an optimization problem with an affine objective, affine equality or
inequality constraints, and finitely many second-order cone constraints of the form ‖Aᵢ x + bᵢ‖_2 ≤
c_iᵀ x + dᵢ.
-/
structure SecondOrderConeProgram where
  n : ℕ
  m : ℕ
  k : ℕ
  objective : Fin n → ℝ
  objectiveConst : ℝ
  eqA : Fin m → Fin n → ℝ
  eqb : Fin m → ℝ
  ineqA : Fin m → Fin n → ℝ
  ineqb : Fin m → ℝ
  socDim : Fin k → ℕ
  socA : (i : Fin k) → Fin (socDim i) → Fin n → ℝ
  socb : (i : Fin k) → Fin (socDim i) → ℝ
  socc : Fin k → Fin n → ℝ
  socd : Fin k → ℝ

def SecondOrderConeProgram.objectiveValue (P : SecondOrderConeProgram) (x : Fin P.n → ℝ) : ℝ :=
  ∑ j : Fin P.n, P.objective j * x j + P.objectiveConst

def SecondOrderConeProgram.satisfiesSocConstraint
    (P : SecondOrderConeProgram) (i : Fin P.k) (x : Fin P.n → ℝ) : Prop :=
  Real.sqrt
      (∑ r : Fin (P.socDim i),
        (∑ j : Fin P.n, P.socA i r j * x j + P.socb i r) ^ 2) ≤
    (∑ j : Fin P.n, P.socc i j * x j) + P.socd i

def SecondOrderConeProgram.IsFeasible
    (P : SecondOrderConeProgram) (x : Fin P.n → ℝ) : Prop :=
  (∀ h : Fin P.m, (∑ j : Fin P.n, P.eqA h j * x j) + P.eqb h = 0) ∧
    (∀ h : Fin P.m, (∑ j : Fin P.n, P.ineqA h j * x j) + P.ineqb h ≤ 0) ∧
    ∀ i : Fin P.k, P.satisfiesSocConstraint i x


/-
A point is feasible for an optimization problem if it satisfies all the constraints.
-/
def SecondOrderConeProgram.IsOptimalMinimizer
    (P : SecondOrderConeProgram) (xStar : Fin P.n → ℝ) : Prop :=
  P.IsFeasible xStar ∧
    ∀ x : Fin P.n → ℝ, P.IsFeasible x → P.objectiveValue xStar ≤ P.objectiveValue x

def SecondOrderConeProgram.optimalValueMin (P : SecondOrderConeProgram) : ℝ :=
  sInf { v : ℝ | ∃ x : Fin P.n → ℝ, P.IsFeasible x ∧ P.objectiveValue x = v }

structure ReciprocalSumMaximization where
  n : ℕ
  m : ℕ
  a : Fin m → Fin n → ℝ
  b : Fin m → ℝ

def ReciprocalSumMaximization.objectiveValue
    (P : ReciprocalSumMaximization) : (Fin P.n → ℝ) → ℝ :=
  fun x : Fin P.n → ℝ =>
    (∑ i : Fin P.m, ((∑ j : Fin P.n, P.a i j * x j) - P.b i)⁻¹)⁻¹

def ReciprocalSumMaximization.isFeasible
    (P : ReciprocalSumMaximization) : (Fin P.n → ℝ) → Prop :=
  fun x : Fin P.n → ℝ =>
    ∀ i : Fin P.m, (∑ j : Fin P.n, P.a i j * x j) > P.b i

def ReciprocalSumMaximization.IsOptimalSolution
    (P : ReciprocalSumMaximization) (xStar : Fin P.n → ℝ) : Prop :=
  P.isFeasible xStar ∧
    ∀ x : Fin P.n → ℝ, P.isFeasible x →
      P.objectiveValue x ≤ P.objectiveValue xStar

/-
Consider the second-order cone program minimize & sum_{i = 1}^m tᵢ; subject to & ≤ ft‖[2; tᵢ-(a_iᵀ
x-bᵢ)]‖_2 ≤ tᵢ+(a_iᵀ x-bᵢ), i = 1,..., m,; & tᵢ ≥ 0, i = 1,..., m, array
-/
structure ReciprocalSumSOCP where
  n : ℕ
  m : ℕ
  a : Fin m → Fin n → ℝ
  b : Fin m → ℝ
  socLeft : (Fin n → ℝ) → (Fin m → ℝ) → Fin m → (Fin 2 → ℝ) :=
    fun x t i =>
      fun r =>
        if _ : (r : ℕ) = 0 then
          2
        else
          t i - ((∑ j : Fin n, a i j * x j) - b i)
  socRight : (Fin n → ℝ) → (Fin m → ℝ) → Fin m → ℝ :=
    fun x t i =>
      t i + ((∑ j : Fin n, a i j * x j) - b i)

def ReciprocalSumSOCP.objectiveValue
    (P : ReciprocalSumSOCP) : (Fin P.m → ℝ) → ℝ :=
  fun t => ∑ i : Fin P.m, t i

def ReciprocalSumSOCP.satisfiesSocConstraint
    (P : ReciprocalSumSOCP) : (Fin P.n → ℝ) → (Fin P.m → ℝ) → Fin P.m → Prop :=
  fun x t i =>
    Real.sqrt (∑ r : Fin 2, (P.socLeft x t i r) ^ 2) ≤ P.socRight x t i

def ReciprocalSumSOCP.isFeasible
    (P : ReciprocalSumSOCP) : (Fin P.n → ℝ) → (Fin P.m → ℝ) → Prop :=
  fun x t =>
    (∀ i : Fin P.m, P.satisfiesSocConstraint x t i) ∧
      ∀ i : Fin P.m, 0 ≤ t i

/-
Let A ∈ ℝ^{m × n}, b ∈ ℝ^m, and let a_iᵀ denote the ith row of A. For x ∈ ℝ^n and y, z ∈ ℝ, prove
that xᵀ x ≤ yz, y ≥ 0, z ≥ 0 if and only if ≤ ft‖[2x; y-z]‖_2 ≤ y+z, y ≥ 0, z ≥ 0.
-/
theorem sq_le_mul_iff_soc_constraint
    {n : ℕ} (x : Fin n → ℝ) (y z : ℝ) :
    ((∑ i : Fin n, (x i) ^ 2) ≤ y * z ∧ 0 ≤ y ∧ 0 ≤ z) ↔
      (Real.sqrt
          ((∑ i : Fin n, (2 * x i) ^ 2) + (y - z) ^ 2) ≤ y + z ∧
        0 ≤ y ∧ 0 ≤ z) := by
  sorry

/-
Let A ∈ ℝ^{m × n}, b ∈ ℝ^m, and let a_iᵀ denote the ith row of A. Also prove that reciprocal sum
maximization is equivalent to equivalent second-order cone program in the following sense: for each
feasible x, the minimum over t equals sum_{i = 1}^m (1)/(a_iᵀ x-bᵢ), so the two problems have the
same optimal solutions in x, and if p* is the optimal value of the original problem and q* is the
optimal value of the SOCP, then p* = 1/q*.
-/
theorem reciprocal_sum_maximization_equiv_socp
    (P : ReciprocalSumMaximization)
    (hsoc_attained :
      let Q : ReciprocalSumSOCP := {
        n := P.n
        m := P.m
        a := P.a
        b := P.b
      }
      ∃ xStar : Fin P.n → ℝ, ∃ tStar : Fin P.m → ℝ,
        Q.isFeasible xStar tStar ∧
        0 < Q.objectiveValue tStar ∧
        ∀ x : Fin P.n → ℝ, ∀ t : Fin P.m → ℝ,
          Q.isFeasible x t → Q.objectiveValue tStar ≤ Q.objectiveValue t) :
    let Q : ReciprocalSumSOCP := {
      n := P.n
      m := P.m
      a := P.a
      b := P.b
    }
    (∀ x : Fin P.n → ℝ, P.isFeasible x →
      sInf {v : ℝ | ∃ t : Fin P.m → ℝ, Q.isFeasible x t ∧ Q.objectiveValue t = v} =
        ∑ i : Fin P.m, (((∑ j : Fin P.n, P.a i j * x j) - P.b i)⁻¹)) ∧
    (∀ xStar : Fin P.n → ℝ,
      P.IsOptimalSolution xStar ↔
        ∃ tStar : Fin P.m → ℝ,
          Q.isFeasible xStar tStar ∧
          ∀ x : Fin P.n → ℝ, ∀ t : Fin P.m → ℝ,
            Q.isFeasible x t → Q.objectiveValue tStar ≤ Q.objectiveValue t) ∧
    (sSup {v : ℝ | ∃ x : Fin P.n → ℝ, P.isFeasible x ∧ P.objectiveValue x = v} =
      (sInf {v : ℝ | ∃ xt : (Fin P.n → ℝ) × (Fin P.m → ℝ),
        Q.isFeasible xt.1 xt.2 ∧ Q.objectiveValue xt.2 = v})⁻¹) := by
  sorry

end «problem-51»
