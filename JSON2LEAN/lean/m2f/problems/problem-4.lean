import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-4»
/-
Let N, n ∈ ℕ with N ≥ 1. Let x₁, ..., x_N ∈ ℝ^n and μ ∈ ℝ^n. For π = (π_1, ..., π_N) ∈ ℝ^N, define
f(π) = - \sum_{i = 1}^N π_i log π_i, with the convention 0 log 0 = 0. Define the feasible set C = {π
∈
ℝ^N | π_i ≥ 0 for i = 1, ..., N, \sum_{i = 1}^N π_i = 1, \sum_{i = 1}^N π_i xᵢ = μ}. Consider the
optimization problem maximize f(π) subject to π ∈ C.
-/
open scoped BigOperators

/-
Let N, n ∈ ℕ with N ≥ 1. Let x₁, …, x_N ∈ ℝⁿ and μ ∈ ℝⁿ.
-/
structure MaximumEntropyProblem where
  N : ℕ
  n : ℕ
  hN : 1 ≤ N
  x : Fin N → (Fin n → ℝ)
  μ : Fin n → ℝ

/-
For π = (π₁, …, π_N) ∈ ℝ^N, define

f(π) = - ∑_{i = 1}^N π_i log π_i,

with the convention 0 log 0 = 0.
-/
def MaximumEntropyProblem.entropyTerm (t : ℝ) : ℝ :=
  if t = 0 then 0 else -t * Real.log t

/-
For π = (π₁, …, π_N) ∈ ℝ^N, define

f(π) = - ∑_{i = 1}^N π_i log π_i,

with the convention 0 log 0 = 0.
-/
def MaximumEntropyProblem.objective (P : MaximumEntropyProblem) (π : Fin P.N → ℝ) : ℝ :=
  ∑ i, MaximumEntropyProblem.entropyTerm (π i)

/-
C = {π ∈ ℝ^N | π_i ≥ 0 for i = 1, ..., N, \sum_{i = 1}^N π_i = 1, \sum_{i = 1}^N π_i xᵢ = μ}.
-/
def MaximumEntropyProblem.IsFeasible (P : MaximumEntropyProblem) (π : Fin P.N → ℝ) : Prop :=
  (∀ i, 0 ≤ π i) ∧
    (∑ i, π i = 1) ∧
      ∀ j, ∑ i, π i * P.x i j = P.μ j

/-- `entropyTerm` is the standard scalar entropy integrand from mathlib. -/
lemma MaximumEntropyProblem.entropyTerm_eq_negMulLog (t : ℝ) :
    MaximumEntropyProblem.entropyTerm t = Real.negMulLog t := by
  -- Split on the zero case to match the convention `0 log 0 = 0`.
  by_cases ht : t = 0
  · simp [MaximumEntropyProblem.entropyTerm, Real.negMulLog, ht]
  · simp [MaximumEntropyProblem.entropyTerm, Real.negMulLog, ht]

/-- The nonnegative orthant in `ℝ^N` is convex. -/
lemma MaximumEntropyProblem.convex_nonnegativeOrthant (P : MaximumEntropyProblem) :
    Convex ℝ {π : Fin P.N → ℝ | ∀ i, 0 ≤ π i} := by
  -- Check convexity coordinatewise using nonnegativity of convex combinations.
  rw [convex_iff_add_mem]
  intro π hπ σ hσ a b ha hb hab i
  simpa [Pi.add_apply, Pi.smul_apply] using
    add_nonneg (mul_nonneg ha (hπ i)) (mul_nonneg hb (hσ i))

/-- Each coordinate entropy contribution is concave on the nonnegative orthant. -/
lemma MaximumEntropyProblem.concaveOn_coordinateEntropy (P : MaximumEntropyProblem) (i : Fin P.N) :
    ConcaveOn ℝ {π : Fin P.N → ℝ | ∀ j, 0 ≤ π j}
      (fun π => MaximumEntropyProblem.entropyTerm (π i)) := by
  let proj : (Fin P.N → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj i
  have hproj : ConcaveOn ℝ (proj ⁻¹' Set.Ici (0 : ℝ)) (Real.negMulLog ∘ proj) :=
    Real.concaveOn_negMulLog.comp_linearMap proj
  -- Restrict the scalar entropy theorem to the common orthant domain.
  refine (hproj.subset ?_ (P.convex_nonnegativeOrthant)).congr ?_
  · intro π hπ
    simpa [proj, LinearMap.proj_apply] using hπ i
  · intro π hπ
    simp [proj, Function.comp, MaximumEntropyProblem.entropyTerm_eq_negMulLog, LinearMap.proj_apply]

/-- The entropy objective is concave on the nonnegative orthant. -/
lemma MaximumEntropyProblem.concaveOn_objective (P : MaximumEntropyProblem) :
    ConcaveOn ℝ {π : Fin P.N → ℝ | ∀ i, 0 ≤ π i} P.objective := by
  let s : Set (Fin P.N → ℝ) := {π : Fin P.N → ℝ | ∀ i, 0 ≤ π i}
  have hs : Convex ℝ s := P.convex_nonnegativeOrthant
  have hsum :
      ∀ t : Finset (Fin P.N),
        ConcaveOn ℝ s (fun π => ∑ i ∈ t, MaximumEntropyProblem.entropyTerm (π i)) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        -- The empty sum is the constant zero function.
        simpa using concaveOn_const (𝕜 := ℝ) (s := s) (0 : ℝ) hs
    | @insert i t hi ht =>
        -- Add one more concave coordinate term to the induction hypothesis.
        simpa [Finset.sum_insert hi] using (P.concaveOn_coordinateEntropy i).add ht
  -- Unfold the objective and apply the finite-sum concavity statement.
  simpa [MaximumEntropyProblem.objective, s] using hsum Finset.univ

/-- The feasible set is convex because all constraints are affine. -/
lemma MaximumEntropyProblem.convex_feasibleSet (P : MaximumEntropyProblem) :
    Convex ℝ {π : Fin P.N → ℝ | P.IsFeasible π} := by
  -- Verify each feasibility clause for a convex combination.
  rw [convex_iff_add_mem]
  intro π hπ σ hσ a b ha hb hab
  rcases hπ with ⟨hπ_nonneg, hπ_sum, hπ_moment⟩
  rcases hσ with ⟨hσ_nonneg, hσ_sum, hσ_moment⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Nonnegativity is preserved coordinatewise.
    intro i
    simpa [Pi.add_apply, Pi.smul_apply] using
      add_nonneg (mul_nonneg ha (hπ_nonneg i)) (mul_nonneg hb (hσ_nonneg i))
  · -- The total mass constraint is affine.
    calc
      ∑ i, (a • π + b • σ) i
          = ∑ i, (a * π i + b * σ i) := by simp [Pi.add_apply, Pi.smul_apply]
      _ = ∑ i, a * π i + ∑ i, b * σ i := by rw [Finset.sum_add_distrib]
      _ = a * ∑ i, π i + b * ∑ i, σ i := by rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ = 1 := by rw [hπ_sum, hσ_sum]; nlinarith
  · -- Each moment equation is affine for the same reason.
    intro j
    calc
      ∑ i, (a • π + b • σ) i * P.x i j
          = ∑ i, (a * (π i * P.x i j) + b * (σ i * P.x i j)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [Pi.add_apply, Pi.smul_apply, add_mul, mul_assoc]
      _ = ∑ i, a * (π i * P.x i j) + ∑ i, b * (σ i * P.x i j) := by
            rw [Finset.sum_add_distrib]
      _ = a * ∑ i, π i * P.x i j + b * ∑ i, σ i * P.x i j := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ = a * P.μ j + b * P.μ j := by rw [hπ_moment, hσ_moment]
      _ = P.μ j := by rw [← add_mul, hab, one_mul]

/-
Consider the optimization problem: maximize f(π) subject to π ∈ C.
-/
theorem maximumEntropyProblem_is_convexOptimizationProblem
    (P : MaximumEntropyProblem) :
    ConcaveOn ℝ {π : Fin P.N → ℝ | ∀ i, 0 ≤ π i} P.objective ∧
      Convex ℝ {π : Fin P.N → ℝ | P.IsFeasible π} := by
  constructor
  · -- Use coordinatewise entropy concavity and sum over all coordinates.
    exact P.concaveOn_objective
  · -- Use direct affine preservation of the feasibility constraints.
    exact P.convex_feasibleSet
end «problem-4»
