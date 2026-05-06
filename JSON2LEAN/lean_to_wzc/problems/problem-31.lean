import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-31»
/- [BLOCK Exercise 3.11-(a) | 22 | defn]
A semidefinite program is an optimization problem in which the decision variable is subject to an
affine linear matrix inequality of the form F₀+sum_{i=1}^n xᵢ Fᵢ succeq 0, together with optional
affine equality or inequality constraints, and the objective function is affine in the variables.
-/
structure SemidefiniteProgram (n m p q : ℕ) where
  F : Fin (n + 1) → Matrix (Fin m) (Fin m) ℝ
  F_isSymm : ∀ i : Fin (n + 1), (F i).IsSymm
  objectiveLinear : Fin n → ℝ
  objectiveConstant : ℝ
  eqLinear : Fin p → Fin n → ℝ
  eqConstant : Fin p → ℝ
  ineqLinear : Fin q → Fin n → ℝ
  ineqConstant : Fin q → ℝ

def SemidefiniteProgram.lmiMatrix {n m p q : ℕ} (sdp : SemidefiniteProgram n m p q)
    (x : Fin n → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  sdp.F 0 + ∑ i : Fin n, x i • sdp.F ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩

def SemidefiniteProgram.objective {n m p q : ℕ} (sdp : SemidefiniteProgram n m p q)
    (x : Fin n → ℝ) : ℝ :=
  sdp.objectiveConstant + ∑ i : Fin n, sdp.objectiveLinear i * x i

def SemidefiniteProgram.satisfiesEqConstraints {n m p q : ℕ} (sdp : SemidefiniteProgram n m p q)
    (x : Fin n → ℝ) : Prop :=
  ∀ j : Fin p, (∑ i : Fin n, sdp.eqLinear j i * x i) = sdp.eqConstant j

def SemidefiniteProgram.satisfiesIneqConstraints {n m p q : ℕ} (sdp : SemidefiniteProgram n m p q)
    (x : Fin n → ℝ) : Prop :=
  ∀ j : Fin q, (∑ i : Fin n, sdp.ineqLinear j i * x i) ≤ sdp.ineqConstant j

def SemidefiniteProgram.IsFeasible {n m p q : ℕ} (sdp : SemidefiniteProgram n m p q)
    (x : Fin n → ℝ) : Prop :=
  Matrix.PosSemidef (sdp.lmiMatrix x) ∧
    sdp.satisfiesEqConstraints x ∧
    sdp.satisfiesIneqConstraints x

/- [BLOCK Exercise 3.11-(a) | 23 | defn]
A linear matrix inequality is a constraint of the form F₀+sum_{i=1}^n xᵢ Fᵢ succeq 0, where
F₀,dots,Fₙ are fixed symmetric matrices and the left-hand side depends affinely on the decision
variables.
-/
structure LinearMatrixInequality (n m : ℕ) where
  data : Fin (n + 1) → Matrix (Fin m) (Fin m) ℝ
  isSymm : ∀ i : Fin (n + 1), (data i).IsSymm

instance {n m : ℕ} : CoeFun (LinearMatrixInequality n m)
    (fun _ => Fin (n + 1) → Matrix (Fin m) (Fin m) ℝ) where
  coe L := L.data

def LinearMatrixInequality.holds {n m : ℕ} (L : LinearMatrixInequality n m) :
    (Fin n → ℝ) → Prop :=
  fun x =>
    Matrix.PosSemidef
      (L.data 0 + ∑ i : Fin n, x i • L.data ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

/- [BLOCK Exercise 3.11-(a) | 24 | opt_prob]
array{ll}
minimize & cᵀ F(x)^{-1} c ;
subject\ to & F(x) succ 0
array
-/
structure MatrixFractionalMinimization (n m : ℕ) where
  F : LinearMatrixInequality n m
  c : Fin m → ℝ

def MatrixFractionalMinimization.matrix {n m : ℕ} (p : MatrixFractionalMinimization n m)
    (x : Fin n → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  p.F 0 + ∑ i : Fin n, x i • p.F ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩

def MatrixFractionalMinimization.objective {n m : ℕ} (p : MatrixFractionalMinimization n m) :
    (Fin n → ℝ) → ℝ :=
  fun x =>
    let Fx : Matrix (Fin m) (Fin m) ℝ := p.matrix x
    dotProduct p.c (fun i => ∑ j : Fin m, Fx⁻¹ i j * p.c j)

def MatrixFractionalMinimization.IsFeasible {n m : ℕ} (p : MatrixFractionalMinimization n m) :
    (Fin n → ℝ) → Prop :=
  fun x => Matrix.PosDef (p.matrix x)

/- [BLOCK Exercise 3.11-(a) | 25 | opt_prob]
array{ll}
minimize & t ;
over & x ∈ ℝ^n,\ t ∈ ℝ ;
subject\ to & ( F(x) & c ; cᵀ & t ) succeq 0
array
-/
structure SchurComplementSemidefiniteProgram (n m : ℕ) where
  F : LinearMatrixInequality n m
  c : Fin m → ℝ

def SchurComplementSemidefiniteProgram.matrix {n m : ℕ} (p : SchurComplementSemidefiniteProgram n m)
    (x : Fin n → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  p.F 0 + ∑ i : Fin n, x i • p.F ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩

def SchurComplementSemidefiniteProgram.blockMatrix {n m : ℕ}
    (p : SchurComplementSemidefiniteProgram n m) (x : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun i j =>
    if hi : i.1 < m then
      if hj : j.1 < m then
        p.matrix x ⟨i.1, hi⟩ ⟨j.1, hj⟩
      else
        p.c ⟨i.1, hi⟩
    else
      if hj : j.1 < m then
        p.c ⟨j.1, hj⟩
      else
        t

def SchurComplementSemidefiniteProgram.IsFeasible {n m : ℕ}
    (p : SchurComplementSemidefiniteProgram n m) (x : Fin n → ℝ) (t : ℝ) : Prop :=
  Matrix.PosSemidef (p.blockMatrix x t)

def SchurComplementSemidefiniteProgram.objective {n m : ℕ}
    (_p : SchurComplementSemidefiniteProgram n m) (_x : Fin n → ℝ) (t : ℝ) : ℝ :=
  t

/- [BLOCK Exercise 3.11-(a) | 26 | thm]
Let F₀,F₁,dots,Fₙ ∈ S^m, let c ∈ ℝ^m, and define F(x)=F₀+sum_{i=1}^n x_iF_i for x=(x₁,dots,xₙ)∈ℝ^n.
Assume there exists x∈ℝ^n such that F(x)succ0. Prove that the optimization problem matrix fractional
minimization is equivalent to the semidefinite program Schur complement semidefinite program. That
is, for every x with F(x)succ0 and every t∈ℝ, one has
( F(x) & c ; cᵀ & t ) succeq 0
quadif and only ifquad
t ≥ cᵀ F(x)^{-1} c,
so both problems have the same optimal value and the same optimal x-solutions.
-/
theorem schurComplement_blockMatrix_posSemidef_iff_objective_le
    {n m : ℕ} (p : MatrixFractionalMinimization n m)
    (x : Fin n → ℝ) (t : ℝ)
    (hpd : Matrix.PosDef (p.matrix x)) :
    Matrix.PosSemidef
        (({ F := p.F, c := p.c } : SchurComplementSemidefiniteProgram n m).blockMatrix x t) ↔
      t ≥ p.objective x := by
  sorry
end «problem-31»
