import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-107»
/-
Let x_[1] ≥ x_[2] ≥ ··· ≥ x_[n] be the nonincreasing rearrangement of the components of x ∈ ℝ^n, and
let α₁ ≥ α₂ ≥ ··· ≥ α_n ≥ 0. Define f(x) = ∑_{i = 1}^n α_i x_[i]. Prove that f is convex on ℝ^n.
-/
/-- The permutation-weighted values of `x` form the range of the permutation evaluation map. -/
lemma permWeightedValues_eq_range
    (n : ℕ) (α : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    {r : ℝ | ∃ σ : Equiv.Perm (Fin n), r = ∑ i : Fin n, α i * x (σ i)} =
      Set.range (fun σ : Equiv.Perm (Fin n) => ∑ i : Fin n, α i * x (σ i)) := by
  -- Repackage the existential description as an ordinary range.
  ext r
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨σ, rfl⟩
  · rintro ⟨σ, rfl⟩
    exact ⟨σ, rfl⟩

/-- The set of permutation-weighted values is bounded above because it is finite. -/
lemma permWeightedValues_bddAbove
    (n : ℕ) (α : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    BddAbove (Set.range (fun σ : Equiv.Perm (Fin n) => ∑ i : Fin n, α i * x (σ i))) := by
  -- Finite ranges in a linear order are automatically bounded above.
  exact (Set.finite_range _).bddAbove

/-- The permutation-weighted value set is nonempty, witnessed by the identity permutation. -/
lemma permWeightedValues_nonempty
    (n : ℕ) (α : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    (Set.range (fun σ : Equiv.Perm (Fin n) => ∑ i : Fin n, α i * x (σ i))).Nonempty := by
  -- The identity permutation contributes one value to the range.
  exact Set.range_nonempty _

/-- Evaluating a permutation-weighted sum on a convex combination distributes over the sum. -/
lemma permWeightedSum_smul_add
    (n : ℕ) (α : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (x y : EuclideanSpace ℝ (Fin n)) (a b : ℝ) :
    (∑ i : Fin n, α i * (a • x + b • y) (σ i)) =
      a * (∑ i : Fin n, α i * x (σ i)) + b * (∑ i : Fin n, α i * y (σ i)) := by
  -- Expand the convex combination coordinatewise inside the finite sum.
  calc
    ∑ i : Fin n, α i * (a • x + b • y) (σ i)
        = ∑ i : Fin n, (a * (α i * x (σ i)) + b * (α i * y (σ i))) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp
            ring
    _ = (∑ i : Fin n, a * (α i * x (σ i))) + ∑ i : Fin n, b * (α i * y (σ i)) := by
          rw [Finset.sum_add_distrib]
    _ = a * (∑ i : Fin n, α i * x (σ i)) + b * (∑ i : Fin n, α i * y (σ i)) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]

theorem weighted_sorted_sum_convexOn
    (n : ℕ) (α : Fin n → ℝ)
    (hα_mono : Antitone α)
    (hα_nonneg : ∀ i : Fin n, 0 ≤ α i) :
    ConvexOn ℝ Set.univ
      (fun x : EuclideanSpace ℝ (Fin n) =>
        sSup {r : ℝ | ∃ σ : Equiv.Perm (Fin n), r = ∑ i : Fin n, α i * x (σ i)}) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  -- Evaluate the function at the convex combination and both endpoints explicitly.
  simpa [smul_eq_mul] using
    (show
      sSup {r : ℝ | ∃ σ : Equiv.Perm (Fin n), r = ∑ i : Fin n, α i * (a • x + b • y) (σ i)} ≤
        a * sSup {r : ℝ | ∃ σ : Equiv.Perm (Fin n), r = ∑ i : Fin n, α i * x (σ i)} +
          b * sSup {r : ℝ | ∃ σ : Equiv.Perm (Fin n), r = ∑ i : Fin n, α i * y (σ i)} from by
      -- Rewrite each supremum over existential witnesses as a supremum over a finite range.
      rw [permWeightedValues_eq_range, permWeightedValues_eq_range, permWeightedValues_eq_range]
      -- Each concrete permutation value at the convex combination is bounded by the same
      -- convex combination of the two permutation suprema.
      refine csSup_le (permWeightedValues_nonempty n α (a • x + b • y)) ?_
      intro r hr
      rcases hr with ⟨σ, rfl⟩
      -- Reduce the range witness to the corresponding concrete permutation sum.
      change (∑ i : Fin n, α i * (a • x + b • y) (σ i)) ≤
        a * sSup (Set.range fun τ : Equiv.Perm (Fin n) => ∑ i : Fin n, α i * x (τ i)) +
          b * sSup (Set.range fun τ : Equiv.Perm (Fin n) => ∑ i : Fin n, α i * y (τ i))
      rw [permWeightedSum_smul_add]
      gcongr
      · exact le_csSup (permWeightedValues_bddAbove n α x) ⟨σ, rfl⟩
      · exact le_csSup (permWeightedValues_bddAbove n α y) ⟨σ, rfl⟩)

end «problem-107»
