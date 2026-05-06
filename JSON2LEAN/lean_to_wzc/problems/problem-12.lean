import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-12»
/-
For X ∈ S_{+ +}^n, the log - determinant is logdet X = log(det X), where det X > 0.
-/
def logDet {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℝ) : ℝ :=
  Real.log (Matrix.det X)

/-
[BLOCK Exercise 8.8 - (a) | 4 | opt_prob] Let Sⁿ denote the vector space of real symmetric n × n
matrices, let S₊₊ⁿ = {X ∈ Sⁿ ∣ X ≻ 0}, let diag(X) ∈ ℝⁿ denote the diagonal of X, let 1 ∈ ℝⁿ be the
all - ones vector, and let C ∈ Sⁿ. Consider the optimization problem

minimize tr(CX) − log det X

subject to diag(X) = 1,

with variable X ∈ Sⁿ, where the objective is defined only for X ∈ S₊₊ⁿ.
-/
structure LogDetSemidefiniteProgram (n : Type*) [Fintype n] [DecidableEq n] where
  C : Matrix n n ℝ
  C_symm : C.IsSymm

def LogDetSemidefiniteProgram.isFeasible {n : Type*} [Fintype n] [DecidableEq n]
    (_ : LogDetSemidefiniteProgram n) (X : Matrix n n ℝ) : Prop :=
  X.IsSymm ∧
  X.PosDef ∧
  X.diag = fun _ => (1 : ℝ)

def LogDetSemidefiniteProgram.objective {n : Type*} [Fintype n] [DecidableEq n]
    (P : LogDetSemidefiniteProgram n) (X : Matrix n n ℝ) : ℝ :=
  Matrix.trace (P.C * X) - logDet X

/-
Let S^n be the vector space of real n × n symmetric matrices, let S_{+ +}^n = {X∈ S^n| Xsucc 0}, let
diag(X)∈ ℝ^n denote the diagonal of X, let 1∈ ℝ^n be the all - ones vector, and let C∈ S^n. Consider
the log - det semidefinite program minimize & tr(CX) - logdet X; subject to & diag(X) = 1, array
with
variable X∈ S^n and objective domain restricted to X∈ S_{+ +}^n. Show that X is optimal if and only
if Xsucc 0, X^{- 1} - C is diagonal, diag(X) = 1. 8. 26
-/
theorem logDetSemidefiniteProgram_optimality_iff
    {n : Type*} [Fintype n] [DecidableEq n]
    (P : LogDetSemidefiniteProgram n) (X : Matrix n n ℝ) :
    P.isFeasible X ∧
      IsMinOn (fun Y : Matrix n n ℝ => P.objective Y)
        {Y | P.isFeasible Y} X ↔
      X.IsSymm ∧
      X.PosDef ∧
      (∃ d : n → ℝ, X⁻¹ - P.C = Matrix.diagonal d) ∧
      X.diag = fun _ => (1 : ℝ) := by
  sorry

end «problem-12»
