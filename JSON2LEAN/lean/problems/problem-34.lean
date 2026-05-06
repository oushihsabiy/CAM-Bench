import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-34»
/- [BLOCK Exercise 3.33-(a) | 31 | defn]
For a constrained optimization problem, a point x is feasible if it satisfies all the constraints.
-/
def IsFeasible {α : Type*} (constraints : Set (α → Prop)) (x : α) : Prop :=
  ∀ c ∈ constraints, c x

/- [BLOCK Exercise 3.33-(a) | 32 | opt_prob]
A semidefinite program is an optimization problem of the form
aligned
minimizequad & tr(CX) ;
subject\ toquad & tr(A_iX)=bᵢ,quad i=1,ldots,m,;
& Xsucceq 0,
aligned
where X ∈ S^n, C,A₁,ldots,Aₘ ∈ S^n, and b₁,
ldots,bₘ ∈ ℝ.
-/
structure SemidefiniteProgram (n m : ℕ) where
  C : Matrix (Fin n) (Fin n) ℝ
  A : Fin m → Matrix (Fin n) (Fin n) ℝ
  b : Fin m → ℝ
  C_symm : C.IsSymm
  A_symm : ∀ i, (A i).IsSymm

def SemidefiniteProgram.isFeasible {n m : ℕ} (p : SemidefiniteProgram n m)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  X.IsSymm ∧
  Matrix.PosSemidef X ∧
  ∀ i : Fin m, Matrix.trace (p.A i * X) = p.b i

def SemidefiniteProgram.objective {n m : ℕ} (p : SemidefiniteProgram n m)
    (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Matrix.trace (p.C * X)

/- [BLOCK Exercise 3.33-(a) | 33 | thm]
Let S^n be the set of real symmetric n × n matrices, and for M ∈ S^n, let M succeq 0 mean that M is
positive semidefinite. Consider the semidefinite program alignedminimizequad & tr(CX) ; subject\
toquad & tr(A_iX)=bᵢ,quad i=1,ldots,m,; & Xsucceq 0,aligned where X ∈ S^n, C,A₁,ldots,Aₘ ∈ S^n, and
b₁,ldots,bₘ ∈ ℝ. Let hat X ∈ S^n be a feasible point of rank r, and suppose that hat X=[Q₁ &
Q₂][Lambda_1 & 0; 0 & 0][Q₁ & Q₂]ᵀ, where [Q₁ & Q₂] is an orthogonal n × n matrix, Q₁ has r columns,
Q₂ has n-r columns, and Lambda_1 is a diagonal r × r matrix with strictly positive diagonal entries.
Show that a matrix V ∈ S^n satisfies tr(A_iV)=0 quad (i=1,ldots,m), hat X+Vsucceq 0, hat X-Vsucceq 0
if and only if there exists Y ∈ S^r such that V=Q_1YQ_1ᵀ, and tr(Q_1ᵀA_iQ_1Y)=0 quad (i=1,ldots,m),
Lambda_1+Ysucceq 0, Lambda_1-Ysucceq 0.
-/
theorem sdp_feasible_perturbation_iff_compressed
    {n m r : ℕ}
    (p : SemidefiniteProgram n m)
    (Xhat V : Matrix (Fin n) (Fin n) ℝ)
    (Q₁ : Matrix (Fin n) (Fin r) ℝ)
    (Q₂ : Matrix (Fin n) (Fin (n - r)) ℝ)
    (Λ₁ : Matrix (Fin r) (Fin r) ℝ)
    (hV_symm : V.IsSymm)
    (hQ₁_orthonormal : Q₁.transpose * Q₁ = 1)
    (hQ₂_orthonormal : Q₂.transpose * Q₂ = 1)
    (hQ₁Q₂_orthogonal : Q₁.transpose * Q₂ = 0)
    (hQ₂Q₁_orthogonal : Q₂.transpose * Q₁ = 0)
    (h_complete : Q₁ * Q₁.transpose + Q₂ * Q₂.transpose = 1)
    (hΛ₁_diag : Λ₁.IsDiag)
    (hΛ₁_pos : ∀ i : Fin r, 0 < Λ₁ i i)
    (hXhat_decomp : Xhat = Q₁ * Λ₁ * Q₁.transpose)
    (hXhat_feas : p.isFeasible Xhat) :
    ((∀ i : Fin m, Matrix.trace (p.A i * V) = 0) ∧
      Matrix.PosSemidef (Xhat + V) ∧
      Matrix.PosSemidef (Xhat - V)) ↔
    ∃ Y : Matrix (Fin r) (Fin r) ℝ,
      Y.IsSymm ∧
      V = Q₁ * Y * Q₁.transpose ∧
      (∀ i : Fin m, Matrix.trace (Q₁.transpose * p.A i * Q₁ * Y) = 0) ∧
      Matrix.PosSemidef (Λ₁ + Y) ∧
      Matrix.PosSemidef (Λ₁ - Y) := by
  sorry

end «problem-34»
