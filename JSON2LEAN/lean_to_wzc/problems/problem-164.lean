import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-164»
/-
Consider the optimization problem maximize & sum_i = 1^n log(\frac{sum_j = 1^n B_ijpⱼ}{sum_j = 1^n
B_ijpⱼ - pᵢ}); subject to & sum_i = 1^n pᵢ = 1,; & pᵢ ≥ 0, i = 1, ..., n, with variable p ∈ ℝ^n.
Define
y = Bp.
-/
structure LogFractionMaximizationProblem (n : ℕ) where
  B : Matrix (Fin n) (Fin n) ℝ
  p : Fin n → ℝ
  yVec : Fin n → ℝ
  objective : ℝ
  h_y : yVec = fun i => ∑ j, B i j * p j
  h_objective : objective = ∑ i, Real.log ((yVec i) / (yVec i - p i))
  h_sum_one : ∑ i, p i = 1
  h_nonneg : ∀ i, 0 ≤ p i

def LogFractionMaximizationProblem.objectiveFn {n : ℕ} (P : LogFractionMaximizationProblem n)
    (p : Fin n → ℝ) : ℝ :=
  ∑ i, Real.log (((∑ j, P.B i j * p j)) / ((∑ j, P.B i j * p j) - p i))

def LogFractionMaximizationProblem.isFeasible {n : ℕ}
    (_P : LogFractionMaximizationProblem n) (p : Fin n → ℝ) : Prop :=
  (∑ i, p i = 1) ∧ ∀ i, 0 ≤ p i

def BMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => A i j + v i

def logFractionFeasible {n : ℕ} (p : Fin n → ℝ) : Prop :=
  (∑ i, p i = 1) ∧ ∀ i, 0 ≤ p i

def logFractionObjective {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ) : ℝ :=
  ∑ i, Real.log (((B.mulVec p) i) / ((B.mulVec p) i - p i))

def transformedFeasible {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    Prop :=
  (∑ i, y i - ∑ i, (C.mulVec y) i = 1) ∧
    ∀ i, 0 ≤ y i - (C.mulVec y) i

def transformedObjective {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    ℝ :=
  ∑ i, Real.log (y i / (C.mulVec y) i)

/-
Consider the transformed optimization problem obtained from the change of variables y = Bp and
p = (I - C)y. Its feasibility constraints are
\sum_i y_i - \sum_i (Cy)_i = 1 and y_i - (Cy)_i ≥ 0, and its objective is
\sum_i log (y_i / (Cy)_i).
-/
structure EquivalentTransformedOptimizationProblem (n : ℕ) where
  C : Matrix (Fin n) (Fin n) ℝ
  y : Fin n → ℝ
  objective : ℝ
  h_objective : objective = transformedObjective C y
  h_balance : (∑ i, y i) - ∑ i, ∑ j, C i j * y j = 1
  h_nonneg_gap : ∀ i, 0 ≤ y i - ∑ j, C i j * y j

def EquivalentTransformedOptimizationProblem.Cy {n : ℕ}
    (P : EquivalentTransformedOptimizationProblem n) :
    Fin n → ℝ :=
  fun i => ∑ j, P.C i j * P.y j

def EquivalentTransformedOptimizationProblem.isFeasible {n : ℕ}
    (P : EquivalentTransformedOptimizationProblem n) : Prop :=
  ((∑ i, P.y i) - ∑ i, P.Cy i = 1) ∧ ∀ i, 0 ≤ P.y i - P.Cy i

/-
Exercise 12.3 | 14 | thm

Let n ∈ ℕ. Let A ∈ ℝ^{n×n} and v ∈ ℝⁿ satisfy A_{ij} ≥ 0, vᵢ ≥ 0, and A_{ii} = 1 for all i, j = 1,
…, n. Let 1 ∈ ℝⁿ be the all - ones vector, define B = A + v1ᵀ, and assume that B is nonsingular with

B⁻¹ = I - C,

where C ∈ ℝ^{n×n}. Consider the log-fraction maximization problem. Prove that the change of variables
y = Bp, equivalently p = (I - C)y, gives an equivalent transformed problem: feasibility is preserved
in both directions and the objectives agree.
-/
theorem logFractionProblem_equivalent_to_transformedProblem
    (n : ℕ)
    (A C : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ)
    (hB_unit : IsUnit (BMatrix A v))
    (hB_inv : (BMatrix A v)⁻¹ = 1 - C) :
    (∀ p : Fin n → ℝ,
      let y := (BMatrix A v).mulVec p
      (∀ i, 0 < y i ∧ 0 < (C.mulVec y) i) →
        (logFractionFeasible p ↔ transformedFeasible C y) ∧
          logFractionObjective (BMatrix A v) p = transformedObjective C y) ∧
    (∀ y : Fin n → ℝ,
      let p : Fin n → ℝ := fun i => y i - (C.mulVec y) i
      (∀ i, 0 < y i ∧ 0 < (C.mulVec y) i) →
        (BMatrix A v).mulVec p = y ∧
          (transformedFeasible C y ↔ logFractionFeasible p) ∧
          transformedObjective C y = logFractionObjective (BMatrix A v) p) := by
  sorry

end «problem-164»
