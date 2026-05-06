import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-75»


open Matrix
/-
A candidate point for the semidefinite program above, packaging the fixed data A, k together with
decision variables X, U, V and the SDP constraints.
-/
structure KyFanNormSDP (m n : Type) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] where
  A : Matrix m n ℝ
  k : ℕ
  X : Matrix m n ℝ
  U : Matrix m m ℝ
  V : Matrix n n ℝ
  U_symm : U.IsSymm
  V_symm : V.IsSymm
  block_psd :
    PosSemidef
      (Matrix.fromBlocks U X X.transpose V)
  U_le_one :
    PosSemidef ((1 : Matrix m m ℝ) - U)
  V_le_one :
    PosSemidef ((1 : Matrix n n ℝ) - V)
  trace_eq :
    Matrix.trace U + Matrix.trace V = 2 * k

/-
The feasibility predicate encoding the four SDP constraints: block positive semidefiniteness, U ≼ I,
V ≼ I, and tr(U) + tr(V) = 2k.
-/
def KyFanNormSDP.isFeasible
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (P : KyFanNormSDP m n) : Prop :=
  PosSemidef (Matrix.fromBlocks P.U P.X P.X.transpose P.V) ∧
  PosSemidef ((1 : Matrix m m ℝ) - P.U) ∧
  PosSemidef ((1 : Matrix n n ℝ) - P.V) ∧
  Matrix.trace P.U + Matrix.trace P.V = 2 * P.k

/-
The SDP objective tr(Aᵀ X).
-/
def KyFanNormSDP.objective
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (P : KyFanNormSDP m n) : ℝ :=
  Matrix.trace (P.A.transpose * P.X)

/- [BLOCK Exercise 4.29-(a) | 33 | thm]
Let A ∈ ℝ^{m × n} with m ≥ n, and let k be an integer with 1 ≤ k ≤ n. Let σ_1(A) ≥ ·s ≥ σ_n(A) be
the singular values of A, and define f(A)=sum_{i=1}^k σ_i(A). Let S^m and S^n denote the sets of
real symmetric m × m and n × n matrices, respectively. For symmetric matrices P,Q, write P succeq 0
if P is positive semidefinite, and P preceq Q if Q-P succeq 0. Show that f(A) is the optimal value
of the semidefinite program for Ky Fan norm
aligned
maximize quad & tr(Aᵀ X) ; ;
subject to quad & [ U & X ; ; Xᵀ & V ] succeq 0, ; ;
& U preceq I, ; ;
& V preceq I, ; ;
& tr(U)+tr(V)=2k,
aligned
where the decision variables are X ∈ ℝ^{m × n}, U ∈ S^m, and V ∈ S^n, and I is the identity matrix
of the appropriate dimension.
-/
theorem kyFanNormSDP_optimal_value
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (k : ℕ)
    (hmn : Fintype.card n ≤ Fintype.card m)
    (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card n) :
    let fA : ℝ := sSup {r : ℝ | ∃ U : Matrix m (Fin k) ℝ, ∃ V : Matrix n (Fin k) ℝ,
        U.transpose * U = 1 ∧ V.transpose * V = 1 ∧
        r = Matrix.trace (U.transpose * A * V)}
    (∀ P : KyFanNormSDP m n, P.A = A → P.k = k → P.objective ≤ fA) ∧
    (∀ ε > 0, ∃ P : KyFanNormSDP m n, P.A = A ∧ P.k = k ∧ fA - ε < P.objective) := by
  sorry

end «problem-75»
