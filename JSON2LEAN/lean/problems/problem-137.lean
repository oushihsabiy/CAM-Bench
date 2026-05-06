import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-137»

/- [BLOCK chapter2 Ex.2.11-(b) | 9 | defn]
A function f : C₁ × C₂ → ℝ cup {+∞} is jointly convex in (x,y) if, for all (x₁,y₁),(x₂,y₂) ∈ C₁
× C₂ and all θ ∈ [0,1],
f(θ x₁+(1-θ)x₂,θ y₁+(1-θ)y₂) ≤ θ f(x₁,y₁)+(1-θ)f(x₂,y₂).
-/
def JointlyConvex
    {E₁ E₂ : Type*}
    [AddCommMonoid E₁] [Module ℝ E₁]
    [AddCommMonoid E₂] [Module ℝ E₂]
    (C₁ : Set E₁) (C₂ : Set E₂) (f : E₁ × E₂ → EReal) : Prop :=
  ∀ ⦃x₁ x₂ : E₁⦄, x₁ ∈ C₁ → x₂ ∈ C₁ →
    ∀ ⦃y₁ y₂ : E₂⦄, y₁ ∈ C₂ → y₂ ∈ C₂ →
    ∀ ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 →
      f (θ • x₁ + (1 - θ) • x₂, θ • y₁ + (1 - θ) • y₂) ≤
        θ * f (x₁, y₁) + (1 - θ) * f (x₂, y₂)

/- [BLOCK chapter2 Ex.2.11-(b) | 10 | defn]
A semidefinite program is an optimization problem in which the decision variable is a symmetric
matrix, the objective function is linear in the decision variables, and the constraints include a
linear matrix inequality of the form F₀ + sum_i=1^p xᵢ Fᵢ succeq 0.
-/
structure SemidefiniteProgram (n p : ℕ) where
  X : Matrix (Fin n) (Fin n) ℝ
  symmetric : Xᵀ = X
  objective : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ
  F0 : Matrix (Fin n) (Fin n) ℝ
  F0_symm : F0.IsSymm
  x : Fin p → ℝ
  F : Fin p → Matrix (Fin n) (Fin n) ℝ
  F_symm : ∀ i, (F i).IsSymm
  
def SemidefiniteProgram.matrix {n p : ℕ} (sdp : SemidefiniteProgram n p) :
    Matrix (Fin n) (Fin n) ℝ :=
  sdp.F0 + ∑ i : Fin p, sdp.x i • sdp.F i

def SemidefiniteProgram.lmiMatrix {n p : ℕ} (sdp : SemidefiniteProgram n p) :
    Matrix (Fin n) (Fin n) ℝ :=
  sdp.X

def SemidefiniteProgram.objectiveValue {n p : ℕ} (sdp : SemidefiniteProgram n p) : ℝ :=
  sdp.objective sdp.X

def SemidefiniteProgram.IsFeasible {n p : ℕ} (sdp : SemidefiniteProgram n p) : Prop :=
  sdp.X = sdp.matrix ∧ sdp.X.PosSemidef

/- [BLOCK chapter2 Ex.2.11-(b) | 11 | opt_prob]
Let A ∈ S_++^m and B ∈ ℝ^m × n. Consider the semidefinite program with decision variable X
∈ S^n:
min_X ∈ S^n Tr(X)
quad
subject to
quad
(
A & B ; B^→p & X
) succeq 0.
-/
structure TraceMinimizationSDP (m n : ℕ) where
  A : Matrix (Fin m) (Fin m) ℝ
  A_isSymm : A.IsSymm
  A_posDef : A.PosDef
  B : Matrix (Fin m) (Fin n) ℝ
  X : Matrix (Fin n) (Fin n) ℝ
  X_isSymm : X.IsSymm
  feasible : (Matrix.fromBlocks A B B.transpose X).PosSemidef

def TraceMinimizationSDP.objective {m n : ℕ} (p : TraceMinimizationSDP m n) : ℝ :=
  Matrix.trace p.X

def TraceMinimizationSDP.blockMatrix {m n : ℕ} (p : TraceMinimizationSDP m n)
    (X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
  Matrix.fromBlocks p.A p.B p.B.transpose X

def TraceMinimizationSDP.isFeasible {m n : ℕ} (p : TraceMinimizationSDP m n)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  X.IsSymm ∧ (p.blockMatrix X).PosSemidef

def TraceMinimizationSDP.objFun {m n : ℕ} (_p : TraceMinimizationSDP m n)
    (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Matrix.trace X

/- [BLOCK chapter2 Ex.2.11-(b) | 12 | thm]
Let S^n be the set of all n × n real symmetric matrices, and let S_{++}^m be the set of all m × m
real symmetric positive definite matrices. Given A ∈ S_{++}^m and B ∈ ℝ^{m × n}, consider the trace
minimization semidefinite program. Define the function f(A,B)=Tr(B^→p A^{-1}B), with domain domf =
S_{++}^m × ℝ^{m × n}. Prove that the function f(A,B) is jointly convex in the pair of variables
(A,B) on domf.
-/
theorem trace_Bt_Ainv_B_jointlyConvex :
    JointlyConvex
      {A : Matrix (Fin m) (Fin m) ℝ | A.IsSymm ∧ A.PosDef}
      (Set.univ : Set (Matrix (Fin m) (Fin n) ℝ))
      (fun p : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ =>
        ((Matrix.trace (p.2ᵀ * p.1⁻¹ * p.2) : ℝ) : EReal)) := by
  sorry

end «problem-137»
