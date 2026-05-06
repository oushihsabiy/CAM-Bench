import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-139»

-- chapter5_Ex_18

/- [BLOCK chapter5 Ex.18 | 10 | defn]
A point z* in the domain of a function f is a local minimizer if there exists varepsilon>0 such that
f(z*)≤ f(z) for all z satisfying ‖z-z*‖< varepsilon.
-/
def IsLocalMinimizer {E β : Type*} [NormedAddCommGroup E] [Preorder β] (f : E → β) (zStar : E) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ z : E, ‖z - zStar‖ < ε → f zStar ≤ f z


/- [BLOCK chapter5 Ex.18 | 13 | opt_prob]
Let A∈ℝ^{m× n} and r ∈ ℕ be given. The decision variables are X∈ℝ^{m× r} and Y∈ℝ^{r× n}. Consider
the optimization problem
min_{X,Y} f(X,Y), f(X,Y)=‖A-XY‖_F^2.
-/
structure LowRankMatrixFactorizationProblem (m n r : Type*)
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r] where
  A : Matrix m n ℝ
  objective : Matrix m r ℝ → Matrix r n ℝ → ℝ :=
    fun X Y => ∑ i, ∑ j, (A i j - (X * Y) i j) ^ 2

def LowRankMatrixFactorizationProblem.isOptimal
    {m n r : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype r] [DecidableEq r]
    (p : LowRankMatrixFactorizationProblem m n r) (X : Matrix m r ℝ) (Y : Matrix r n ℝ) : Prop :=
  ∀ X' : Matrix m r ℝ, ∀ Y' : Matrix r n ℝ,
    p.objective X Y ≤ p.objective X' Y'

/- [BLOCK chapter5 Ex.18 | 14 | thm]
Let a given matrix A ∈ ℝ^{m × n} and a given rank parameter r ∈ ℕ be specified. The decision
variables are X ∈ ℝ^{m × r} and Y ∈ ℝ^{r × n}. Consider the low-rank matrix factorization problem
min_{X,Y} f(X,Y), f(X,Y)=‖A-XY‖_F^2, where ‖·‖_F denotes the Frobenius norm, i.e., the square root
of the sum of the squares of all matrix entries. The dimensions of the matrix product XY are
guaranteed by the above specification to be well-defined. Let (X*,Y*) ∈ ℝ^{m × r} × ℝ^{r × n} be a
local minimizer of this problem. Write down the necessary conditions for (X*,Y*) to be a local
minimizer. In the statement, explicitly give the first-order stationary conditions of the objective
function with respect to X and Y, and further explain the second-order necessary conditions that a
local minimizer should satisfy.
-/
open scoped RealInnerProductSpace

theorem lowRankMatrixFactorization_localMinimizer_necessary_conditions
    {m n r : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]
    [InnerProductSpace ℝ (Matrix m r ℝ × Matrix r n ℝ)]
    (p : LowRankMatrixFactorizationProblem m n r)
    (XStar : Matrix m r ℝ) (YStar : Matrix r n ℝ)
    (hloc :
      IsLocalMinimizer
        (fun Z : Matrix m r ℝ × Matrix r n ℝ =>
          ∑ i, ∑ j, (p.A i j - (Z.1 * Z.2) i j) ^ 2)
        (XStar, YStar)) :
    fderiv ℝ
        (fun X : Matrix m r ℝ => ∑ i, ∑ j, (p.A i j - (X * YStar) i j) ^ 2)
        XStar = 0 ∧
      fderiv ℝ
        (fun Y : Matrix r n ℝ => ∑ i, ∑ j, (p.A i j - (XStar * Y) i j) ^ 2)
        YStar = 0 ∧
      (ContDiffAt ℝ 2
          (fun Z : Matrix m r ℝ × Matrix r n ℝ =>
            ∑ i, ∑ j, (p.A i j - (Z.1 * Z.2) i j) ^ 2)
          (XStar, YStar) →
        ∀ d : Matrix m r ℝ × Matrix r n ℝ,
          0 ≤
            ⟪d,
              (fderiv ℝ
                (gradient
                  (fun Z : Matrix m r ℝ × Matrix r n ℝ =>
                    ∑ i, ∑ j, (p.A i j - (Z.1 * Z.2) i j) ^ 2))
                (XStar, YStar)) d⟫) := by
  sorry

end «problem-139»
