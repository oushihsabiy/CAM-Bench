import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-182»
/- [BLOCK Exercise 4.17-(a) | 34 | opt_prob]
Then
\[
\sup\{\operatorname{tr}(AX) \mid X \in S^n,\ \operatorname{tr}(X)=r,\ 0 \preceq X,\ X \preceq I\} = f(A).
\]
-/
structure SpectralTraceMaximization where
  n : Type*
  fintype_n : Fintype n
  decEq_n : DecidableEq n
  A : Matrix n n ℝ
  r : ℝ
  f : Matrix n n ℝ → ℝ

def SpectralTraceMaximization.feasibleSet (P : SpectralTraceMaximization) :
    Set (Matrix P.n P.n ℝ) :=
  letI := P.fintype_n
  letI := P.decEq_n
  {X | X.IsSymm ∧ Matrix.trace X = P.r ∧ X.PosSemidef ∧ (1 - X).PosSemidef}

def SpectralTraceMaximization.objective (P : SpectralTraceMaximization) :
    Matrix P.n P.n ℝ → ℝ :=
  letI := P.fintype_n
  letI := P.decEq_n
  fun X => Matrix.trace (P.A * X)

/- [BLOCK Exercise 4.17-(a) | 35 | thm]
Let \(S^n\) be the set of real \(n \times n\) symmetric matrices. Let \(A \in S^n\), and let \(\lambda_1(A),\ldots,\lambda_n(A)\) be the eigenvalues of \(A\) ordered so that \(\lambda_1(A) \ge \lambda_2(A) \ge \cdots \ge \lambda_n(A)\). Fix \(r \in \{1,\ldots,n\}\), and define \(f(A)=\sum_{k=1}^r \lambda_k(A)\). Then spectral trace maximization.
-/
theorem spectral_trace_maximization
    (n r : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm)
    (hr_lower : 1 ≤ r)
    (hr_upper : r ≤ n)
    (hordered :
      ∀ i j : Fin n,
        i.1 ≤ j.1 →
          (by simpa using hA : A.IsHermitian).eigenvalues i ≥
            (by simpa using hA : A.IsHermitian).eigenvalues j) :
    sSup {t : ℝ | ∃ X : Matrix (Fin n) (Fin n) ℝ,
      X.IsSymm ∧
      Matrix.trace X = (r : ℝ) ∧
      X.PosSemidef ∧
      (1 - X).PosSemidef ∧
      t = Matrix.trace (A * X)} =
      ∑ k : Fin r,
        (by simpa using hA : A.IsHermitian).eigenvalues
          ⟨k.1, Nat.lt_of_lt_of_le k.2 hr_upper⟩ := by
  sorry

end «problem-182»
