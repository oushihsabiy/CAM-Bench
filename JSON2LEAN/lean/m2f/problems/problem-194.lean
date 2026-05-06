import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-194»

def l2Norm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, (x i) ^ 2)

/- [BLOCK Exercise 18.9 | 4 | opt_prob]
Let Aₖ ∈ ℝ^{m × n}, cₖ ∈ ℝ^m, and Delta_k ∈ ℝ with Delta_k ≥ 0. Consider the problem
min_{v ∈ ℝ^n} ‖Aₖ v + cₖ‖_2^2
quad subject to quad
‖v‖_2 ≤ 0.8Delta_k.
Here
Range(A_kᵀ)={A_kᵀ y : y ∈ ℝ^m}.
-/
structure LeastSquaresTrustRegionProblem where
  m : ℕ
  n : ℕ
  A : Matrix (Fin m) (Fin n) ℝ
  c : Fin m → ℝ
  Δ : ℝ
  Δ_nonneg : 0 ≤ Δ
  transposeRange : Set (Fin n → ℝ) := Set.range A.transpose.mulVec

def LeastSquaresTrustRegionProblem.objective (p : LeastSquaresTrustRegionProblem) :
    (Fin p.n → ℝ) → ℝ :=
  fun v => l2Norm (p.A.mulVec v + p.c) ^ 2

def LeastSquaresTrustRegionProblem.feasibleSet (p : LeastSquaresTrustRegionProblem) :
    Set (Fin p.n → ℝ) :=
  {v | l2Norm v ≤ (0.8 : ℝ) * p.Δ}

def LeastSquaresTrustRegionProblem.residual (p : LeastSquaresTrustRegionProblem) (v : Fin p.n → ℝ) :
    Fin p.m → ℝ :=
  fun i => (∑ j, p.A i j * v j) + p.c i

/-- A concrete instance where the `transposeRange` field is overridden to be empty. -/
private def emptyTransposeRangeCounterexample : LeastSquaresTrustRegionProblem :=
  { m := 1
    n := 1
    A := 0
    c := 0
    Δ := 0
    Δ_nonneg := le_rfl
    transposeRange := ∅ }

/-- The zero vector is feasible for the empty-range counterexample. -/
private lemma zero_mem_feasibleSet_emptyTransposeRangeCounterexample :
    (0 : Fin emptyTransposeRangeCounterexample.n → ℝ) ∈
      emptyTransposeRangeCounterexample.feasibleSet := by
  -- The trust-region radius is `0`, and the zero vector has zero norm.
  simp [LeastSquaresTrustRegionProblem.feasibleSet, emptyTransposeRangeCounterexample, l2Norm]

/-- The objective is identically zero in the empty-range counterexample. -/
private lemma zero_minimizes_objective_emptyTransposeRangeCounterexample :
    ∀ w : Fin emptyTransposeRangeCounterexample.n → ℝ,
      w ∈ emptyTransposeRangeCounterexample.feasibleSet →
        emptyTransposeRangeCounterexample.objective
            (0 : Fin emptyTransposeRangeCounterexample.n → ℝ) ≤
          emptyTransposeRangeCounterexample.objective w := by
  -- Both residuals vanish because `A = 0` and `c = 0`.
  intro w hw
  simp [LeastSquaresTrustRegionProblem.objective, emptyTransposeRangeCounterexample, l2Norm]

/-- The empty-range counterexample still has a feasible minimizer; only the
range-membership requirement fails. -/
private lemma exists_feasible_minimizer_emptyTransposeRangeCounterexample :
    ∃ v : Fin emptyTransposeRangeCounterexample.n → ℝ,
      v ∈ emptyTransposeRangeCounterexample.feasibleSet ∧
      ∀ w : Fin emptyTransposeRangeCounterexample.n → ℝ,
        w ∈ emptyTransposeRangeCounterexample.feasibleSet →
          emptyTransposeRangeCounterexample.objective v ≤
            emptyTransposeRangeCounterexample.objective w := by
  -- The zero vector is feasible for the radius-zero trust region.
  refine Exists.intro (0 : Fin emptyTransposeRangeCounterexample.n → ℝ) ?_
  refine And.intro zero_mem_feasibleSet_emptyTransposeRangeCounterexample ?_
  -- The objective is identically zero, so the feasible zero vector is minimal.
  intro w hw
  exact zero_minimizes_objective_emptyTransposeRangeCounterexample w hw

/-- No witness can satisfy the theorem's range requirement in the empty-range counterexample. -/
private lemma no_required_witness_emptyTransposeRangeCounterexample :
    ¬ ∃ v : Fin emptyTransposeRangeCounterexample.n → ℝ,
      v ∈ emptyTransposeRangeCounterexample.feasibleSet ∧
      v ∈ emptyTransposeRangeCounterexample.transposeRange ∧
      ∀ w : Fin emptyTransposeRangeCounterexample.n → ℝ,
        w ∈ emptyTransposeRangeCounterexample.feasibleSet →
          emptyTransposeRangeCounterexample.objective v ≤
            emptyTransposeRangeCounterexample.objective w := by
  -- Any such witness would have to lie in `∅`, which is impossible.
  intro h
  rcases h with ⟨v, _, hvRange, _⟩
  simp [emptyTransposeRangeCounterexample] at hvRange

/-- The empty-range counterexample has a feasible minimizer, but none of the required
theorem witnesses can lie in the overridden transpose range. -/
private lemma emptyTransposeRangeCounterexample_has_minimizer_but_no_required_witness :
    (∃ v : Fin emptyTransposeRangeCounterexample.n → ℝ,
      v ∈ emptyTransposeRangeCounterexample.feasibleSet ∧
      ∀ w : Fin emptyTransposeRangeCounterexample.n → ℝ,
        w ∈ emptyTransposeRangeCounterexample.feasibleSet →
          emptyTransposeRangeCounterexample.objective v ≤
            emptyTransposeRangeCounterexample.objective w) ∧
    ¬ ∃ v : Fin emptyTransposeRangeCounterexample.n → ℝ,
      v ∈ emptyTransposeRangeCounterexample.feasibleSet ∧
      v ∈ emptyTransposeRangeCounterexample.transposeRange ∧
      ∀ w : Fin emptyTransposeRangeCounterexample.n → ℝ,
        w ∈ emptyTransposeRangeCounterexample.feasibleSet →
          emptyTransposeRangeCounterexample.objective v ≤
            emptyTransposeRangeCounterexample.objective w := by
  -- The first component records the explicit feasible minimizer already constructed above.
  refine And.intro ?_ ?_
  · exact exists_feasible_minimizer_emptyTransposeRangeCounterexample
  -- The second component is the contradiction caused by the overridden empty range.
  · exact no_required_witness_emptyTransposeRangeCounterexample

/-- The theorem's universal existence claim is false because of the empty-range counterexample. -/
private lemma not_forall_exists_solution_in_transposeRange :
    ¬ (∀ p : LeastSquaresTrustRegionProblem,
      ∃ v : Fin p.n → ℝ,
        v ∈ p.feasibleSet ∧
        v ∈ p.transposeRange ∧
        ∀ w : Fin p.n → ℝ, w ∈ p.feasibleSet → p.objective v ≤ p.objective w) := by
  -- Route correction: instantiate the claimed universal statement at the concrete
  -- problem whose `transposeRange` field was overridden to be empty.
  intro hUniversal
  -- The resulting witness contradicts the impossibility lemma established above.
  exact no_required_witness_emptyTransposeRangeCounterexample
    (hUniversal emptyTransposeRangeCounterexample)

/-- Any universal witness function for the target statement contradicts the concrete
empty-range problem already isolated above. -/
private lemma specialize_universal_solution_claim_to_empty_counterexample
    (hUniversal : ∀ p : LeastSquaresTrustRegionProblem,
      ∃ v : Fin p.n → ℝ,
        v ∈ p.feasibleSet ∧
        v ∈ p.transposeRange ∧
        ∀ w : Fin p.n → ℝ, w ∈ p.feasibleSet → p.objective v ≤ p.objective w) :
    ∃ v : Fin emptyTransposeRangeCounterexample.n → ℝ,
      v ∈ emptyTransposeRangeCounterexample.feasibleSet ∧
      v ∈ emptyTransposeRangeCounterexample.transposeRange ∧
      ∀ w : Fin emptyTransposeRangeCounterexample.n → ℝ,
        w ∈ emptyTransposeRangeCounterexample.feasibleSet →
          emptyTransposeRangeCounterexample.objective v ≤
            emptyTransposeRangeCounterexample.objective w := by
  -- Route correction: make the contradiction explicit by specializing the
  -- claimed universal family at the concrete empty-range counterexample.
  exact hUniversal emptyTransposeRangeCounterexample

/-- Any universal witness function for the target statement contradicts the concrete
empty-range problem already isolated above. -/
private lemma universal_solution_claim_conflicts
    (hUniversal : ∀ p : LeastSquaresTrustRegionProblem,
      ∃ v : Fin p.n → ℝ,
        v ∈ p.feasibleSet ∧
        v ∈ p.transposeRange ∧
        ∀ w : Fin p.n → ℝ, w ∈ p.feasibleSet → p.objective v ≤ p.objective w) :
    False := by
  -- The specialized witness is exactly what the empty-range impossibility lemma forbids.
  exact no_required_witness_emptyTransposeRangeCounterexample
    (specialize_universal_solution_claim_to_empty_counterexample hUniversal)

/- [BLOCK Exercise 18.9 | 5 | thm]
Let Aₖ ∈ ℝ^{m × n}, cₖ ∈ ℝ^m, and Delta_k ∈ ℝ with Delta_k ≥ 0. Consider the least-squares
trust-region problem
min_{v ∈ ℝ^n} ‖Aₖ v + cₖ‖_2^2
quad subject to quad
‖v‖_2 ≤ 0.8Delta_k.
Here Range(A_kᵀ)={A_kᵀ y : y ∈ ℝ^m}. Show that this problem has at least one solution vₖ such that
vₖ ∈ Range(A_kᵀ).
-/
theorem exists_solution_in_transposeRange (p : LeastSquaresTrustRegionProblem) :
    ∃ v : Fin p.n → ℝ,
      v ∈ p.feasibleSet ∧
      v ∈ p.transposeRange ∧
      ∀ w : Fin p.n → ℝ, w ∈ p.feasibleSet → p.objective v ≤ p.objective w := by
  -- Route correction: the obstruction is semantic, not an optimization proof gap,
  -- so this target is refuted by an in-file counterexample rather than blocked on
  -- a missing minimization lemma.
  -- `transposeRange` is mutable structure data, so `emptyTransposeRangeCounterexample`
  -- sets it to `∅` while keeping the feasible set nonempty.
  -- The local lemma `exists_feasible_minimizer_emptyTransposeRangeCounterexample`
  -- shows a minimizer exists; the only failing requirement is membership in
  -- the overridden empty range.
  -- Specializing this theorem at `p = emptyTransposeRangeCounterexample` would
  -- therefore produce exactly the forbidden witness from
  -- `no_required_witness_emptyTransposeRangeCounterexample`.
  -- The packaged contradiction is also available as
  -- `universal_solution_claim_conflicts`.
  -- Equivalently, `fun q => exists_solution_in_transposeRange q` would be the
  -- universal witness family refuted by
  -- `not_forall_exists_solution_in_transposeRange`.
  -- TODO: repair the model by forcing
  -- `p.transposeRange = Set.range p.A.transpose.mulVec`, then reprove the theorem.
  sorry

end «problem-194»
