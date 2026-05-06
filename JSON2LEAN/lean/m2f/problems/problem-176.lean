import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-176»
/-
Let m and n be natural numbers with n > = 1. Let A ∈ ℝ^(m x n) and b ∈ ℝ^m. For x ∈ ℝ^n, write x > 0
if every component of x is strictly positive. For y ∈ ℝ^n, write y > = 0 if every component of y is
nonnegative. Show that there exists x ∈ ℝ^n such that x > 0 and Ax = b if and only if there does not
exist λ ∈ ℝ^m such that Aᵀ λ > = 0, Aᵀ λ ! = 0, and bᵀ λ < = 0.
-/
/-- The claimed equivalence fails for the `1 × 1` zero matrix with right-hand side `1`. -/
lemma zero_matrix_singleton_counterexample :
    ¬ (((∃ x : Fin 1 → ℝ, (∀ i, 0 < x i) ∧
          (0 : Matrix (Fin 1) (Fin 1) ℝ).mulVec x = fun _ => (1 : ℝ)) ↔
        ¬ ∃ lam : Fin 1 → ℝ,
          (∀ i, 0 ≤ ((0 : Matrix (Fin 1) (Fin 1) ℝ).transpose.mulVec lam) i) ∧
          ((0 : Matrix (Fin 1) (Fin 1) ℝ).transpose.mulVec lam ≠ 0) ∧
          dotProduct (fun _ => (1 : ℝ)) lam ≤ 0)) := by
  intro h
  have hprimal :
      ¬ ∃ x : Fin 1 → ℝ, (∀ i, 0 < x i) ∧
          (0 : Matrix (Fin 1) (Fin 1) ℝ).mulVec x = fun _ => (1 : ℝ) := by
    intro hx
    rcases hx with ⟨x, hx_pos, hx_eq⟩
    -- The zero matrix sends every vector to zero, so the claimed equation forces `0 = 1`.
    have hcoord := congrFun hx_eq 0
    norm_num at hcoord
  have hdual :
      ¬ ∃ lam : Fin 1 → ℝ,
        (∀ i, 0 ≤ ((0 : Matrix (Fin 1) (Fin 1) ℝ).transpose.mulVec lam) i) ∧
        ((0 : Matrix (Fin 1) (Fin 1) ℝ).transpose.mulVec lam ≠ 0) ∧
        dotProduct (fun _ => (1 : ℝ)) lam ≤ 0 := by
    intro hlam
    rcases hlam with ⟨lam, hnonneg, hne, hdot⟩
    -- The transposed zero matrix also annihilates every vector, contradicting the nonzero side condition.
    have hzero : ((0 : Matrix (Fin 1) (Fin 1) ℝ).transpose.mulVec lam) = 0 := by
      simp
    exact hne hzero
  -- The dual side is true while the primal side is false, so the equivalence cannot hold.
  exact hprimal (h.mpr hdual)

/-- The universal equivalence statement is refuted by the singleton zero-matrix example. -/
lemma not_forall_exists_strictly_positive_solution_iff_no_dual_certificate :
    ¬ ∀ {m n : ℕ}, 1 ≤ n → ∀ (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
        (∃ x : Fin n → ℝ, (∀ i, 0 < x i) ∧ A.mulVec x = b) ↔
          ¬ ∃ lam : Fin m → ℝ,
            (∀ i, 0 ≤ (A.transpose.mulVec lam) i) ∧
            A.transpose.mulVec lam ≠ 0 ∧
            dotProduct b lam ≤ 0 := by
  intro h
  -- Specialize the universal claim to the `1 × 1` zero-matrix instance isolated above.
  exact zero_matrix_singleton_counterexample
    (h (m := 1) (n := 1) le_rfl 0 (fun _ => (1 : ℝ)))

/-- Any global proof of the claimed alternative would contradict the singleton counterexample. -/
lemma no_global_proof_of_exists_strictly_positive_solution_iff_no_dual_certificate
    (h : ∀ {m n : ℕ}, 1 ≤ n → ∀ (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
        (∃ x : Fin n → ℝ, (∀ i, 0 < x i) ∧ A.mulVec x = b) ↔
          ¬ ∃ lam : Fin m → ℝ,
            (∀ i, 0 ≤ (A.transpose.mulVec lam) i) ∧
            A.transpose.mulVec lam ≠ 0 ∧
            dotProduct b lam ≤ 0) :
    False := by
  -- The previously proved singleton specialization already refutes any such global theorem.
  exact not_forall_exists_strictly_positive_solution_iff_no_dual_certificate h

/-- The current statement is false: its singleton zero-matrix specialization is refuted above. -/
theorem exists_strictly_positive_solution_iff_no_dual_certificate
    {m n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∃ x : Fin n → ℝ, (∀ i, 0 < x i) ∧ A.mulVec x = b) ↔
      ¬ ∃ lam : Fin m → ℝ,
        (∀ i, 0 ≤ (A.transpose.mulVec lam) i) ∧
        A.transpose.mulVec lam ≠ 0 ∧
        dotProduct b lam ≤ 0 := by
  -- Route correction: the target statement is false as written. Specializing to
  -- `(m := 1) (n := 1) (hn := le_rfl) (A := 0) (b := fun _ => (1 : ℝ))`
  -- gives exactly the proposition negated by
  -- `zero_matrix_singleton_counterexample`.
  -- TODO: repair the theorem statement upstream. If this theorem were proved,
  -- then applying
  -- `no_global_proof_of_exists_strictly_positive_solution_iff_no_dual_certificate`
  -- to the resulting global proof would derive `False`.
  sorry

end «problem-176»
