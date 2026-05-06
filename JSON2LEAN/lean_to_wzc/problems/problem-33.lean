import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-33»

/- [BLOCK Exercise 12.12-(a) | 28 | defn]
A matrix A ∈ ℝ^n×n is called a symmetric Toeplitz matrix if there exist t₀,dots,t_n-1 ∈ ℝ
such that A_ij=t_|i-j| for all i,j ∈ {1,dots,n}; equivalently, A is constant along each
diagonal and satisfies A=Aᵀ.
-/
def IsSymmetricToeplitzMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ t : ℕ → ℝ, ∀ i j : Fin n, A i j = t (Nat.dist i j)

/- [BLOCK Exercise 12.12-(a) | 29 | defn]
A semidefinite program is an optimization problem of the form: minimize cᵀ x subject to F(x)
succeq 0, where F(x)=F₀+sum_i=1^m xᵢ Fᵢ is an affine map into the symmetric matrices.
-/
structure SemidefiniteProgram where
  m : ℕ
  n : ℕ
  c : Fin m → ℝ
  F : Fin n → Fin n → ℝ
  Fs : Fin m → Fin n → Fin n → ℝ
  symmetric_F : Matrix.IsSymm F
  symmetric_Fs : ∀ i : Fin m, Matrix.IsSymm (Fs i)

def SemidefiniteProgram.affineMap (P : SemidefiniteProgram) (x : Fin P.m → ℝ) :
    Matrix (Fin P.n) (Fin P.n) ℝ :=
  fun i j => P.F i j + ∑ k : Fin P.m, x k * P.Fs k i j

def SemidefiniteProgram.objective (P : SemidefiniteProgram) (x : Fin P.m → ℝ) : ℝ :=
  ∑ i : Fin P.m, P.c i * x i

def SemidefiniteProgram.IsFeasible (P : SemidefiniteProgram) (x : Fin P.m → ℝ) : Prop :=
  Matrix.PosSemidef (P.affineMap x)

/- [BLOCK Exercise 12.12-(a) | 30 | defn]
For a primal semidefinite program in standard form, minimize cᵀ x subject to F₀+sum_i=1^m xᵢ Fᵢ
succeq 0, the dual semidefinite program is: maximize -langle F₀,Zrangle subject to Z succeq 0
and langle Fᵢ,Zrangle = cᵢ for all i.
-/
open scoped BigOperators
def SemidefiniteProgram.dual
    (P : SemidefiniteProgram) :
    SemidefiniteProgram where
  m := P.n * P.n
  n := P.m + 1
  c := fun z =>
    -(P.F (Fin.divNat z) (Fin.modNat z))
  F := fun i j =>
    if hi : i = 0 then
      if hj : j = 0 then
        0
      else
        P.c (Fin.pred j hj)
    else
      if hj : j = 0 then
        P.c (Fin.pred i hi)
      else
        0
  Fs := fun z i j =>
    let ia : Fin P.n := Fin.divNat z
    let ib : Fin P.n := Fin.modNat z
    if hi : i = 0 then
      if hj : j = 0 then
        if ia = ib then 1 else 0
      else
        -P.Fs (Fin.pred j hj) ia ib
    else
      if hj : j = 0 then
        -P.Fs (Fin.pred i hi) ia ib
      else
        0
  symmetric_F := by
    ext i j
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · simp [hi, hj]
      · simp [hi, hj]
    · by_cases hj : j = 0
      · simp [hi, hj]
      · simp [hi, hj]
  symmetric_Fs := by
    intro z
    ext i j
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · simp [hi, hj]
      · simp [hi, hj]
    · by_cases hj : j = 0
      · simp [hi, hj]
      · simp [hi, hj]

/- [BLOCK Exercise 12.12-(a) | 31 | opt_prob]
Consider the primal semidefinite program
aligned
minimizequad & cᵀ x ;
subject toquad & Tₙ(x₁,ldots,xₙ) succeq e₁ e_1ᵀ,
aligned
where the variable is x ∈ ℝ^n.
-/
structure PrimalToeplitzSemidefiniteProgram where
  n : ℕ
  c : Fin n → ℝ

namespace PrimalToeplitzSemidefiniteProgram

def toeplitzMatrix (P : PrimalToeplitzSemidefiniteProgram) :
    (Fin P.n → ℝ) → Matrix (Fin P.n) (Fin P.n) ℝ :=
  fun x i j =>
    if _hij : i.1 ≤ j.1 then
      x ⟨j.1 - i.1, lt_of_le_of_lt (Nat.sub_le _ _) j.is_lt⟩
    else
      x ⟨i.1 - j.1, lt_of_le_of_lt (Nat.sub_le _ _) i.is_lt⟩

def e₁e₁T (P : PrimalToeplitzSemidefiniteProgram) :
    Matrix (Fin P.n) (Fin P.n) ℝ :=
  fun i j => if i.1 = 0 ∧ j.1 = 0 then 1 else 0

def isFeasible (P : PrimalToeplitzSemidefiniteProgram) :
    (Fin P.n → ℝ) → Prop :=
  fun x => Matrix.PosSemidef (P.toeplitzMatrix x - P.e₁e₁T)

def objectiveFn (P : PrimalToeplitzSemidefiniteProgram) :
    (Fin P.n → ℝ) → ℝ :=
  fun x => ∑ i : Fin P.n, P.c i * x i

end PrimalToeplitzSemidefiniteProgram

/- [BLOCK Exercise 12.12-(a) | 32 | thm]
Let n ∈ ℕ with n ≥ 1, let c ∈ ℝ^n, and let e₁=(1,0,ldots,0)ᵀ ∈ ℝ^n. For x=(x₁,ldots,xₙ) ∈ ℝ^n,
define the symmetric Toeplitz matrix Tₙ(x₁,ldots,xₙ) ∈ S^{n × n} by
Tₙ(x₁,ldots,xₙ)=
[
x₁ & x₂ & x₃ & ·s & x_{n-1} & xₙ ;
x₂ & x₁ & x₂ & ·s & x_{n-2} & x_{n-1} ;
x₃ & x₂ & x₁ & ·s & x_{n-3} & x_{n-2} ;
vdots & vdots & vdots & ddots & vdots & vdots ;
x_{n-1} & x_{n-2} & x_{n-3} & ·s & x₁ & x₂ ;
xₙ & x_{n-1} & x_{n-2} & ·s & x₂ & x₁
].
For A,B ∈ S^{n × n}, write A succeq B when A-B is positive semidefinite. For each k=1,ldots,n, let
Eₖ ∈ S^{n× n} be the matrix whose (i,j)-entry is 1 if |i-j|=k-1 and 0 otherwise, so that
Tₙ(x₁,ldots,xₙ)=sum_{k=1}^n xₖ Eₖ. Consider the primal Toeplitz semidefinite program. Prove that its
dual semidefinite program is
aligned
maximizequad & langle e₁ e_1ᵀ, Z rangle = Z_{11} ;
subject toquad & Z succeq 0, ;
& langle Eₖ, Z rangle = cₖ, k=1,ldots,n,
aligned
with dual variable Z ∈ S^{n×n}.
-/
theorem primalToeplitzSemidefiniteProgram_dual_form
    (P : PrimalToeplitzSemidefiniteProgram) (hpos : 1 ≤ P.n) :
    let E : Fin P.n → Matrix (Fin P.n) (Fin P.n) ℝ :=
      fun k i j => if Nat.dist i.1 j.1 = k.1 then 1 else 0
    let dualFeasible : Matrix (Fin P.n) (Fin P.n) ℝ → Prop :=
      fun Z => Matrix.PosSemidef Z ∧ ∀ k : Fin P.n, Matrix.trace (E k * Z) = P.c k
    let dualObjective : Matrix (Fin P.n) (Fin P.n) ℝ → ℝ :=
      fun Z => Matrix.trace (P.e₁e₁T * Z)
    ∀ Z : Matrix (Fin P.n) (Fin P.n) ℝ,
      dualFeasible Z →
      dualObjective Z = Z ⟨0, hpos⟩ ⟨0, hpos⟩ := by
  sorry

end «problem-33»
