import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-112»
/-
For x ∈ ℝ^n let |x| _ [ 1] ≥ |x|_ [2] ≥ ··· ≥ |x|_[n] be the nonincreasing rearrangement of (|x₁|,
…, |xₙ|). For 1 ≤ r ≤ n define f(x) = ∑_{i = 1}^r |x|_[i]. Prove that f is convex on ℝ^n.
-/
theorem top_r_abs_sum_convexOn
    (n r : ℕ) (hr₁ : 1 ≤ r) (hr₂ : r ≤ n) :
    ConvexOn ℝ Set.univ
      (fun x : EuclideanSpace ℝ (Fin n) =>
        sSup (({s : Finset (Fin n) | s.card = r}).image (fun s => ∑ i, if i ∈ s then ‖x i‖ else 0))) := by
  classical
  -- Route correction: prove convexity directly from the `csSup` characterization instead of
  -- introducing a separate finite-sup API; the image set is nonempty and explicitly bounded.
  let topSet :
      EuclideanSpace ℝ (Fin n) → Set ℝ :=
    fun x =>
      ({s : Finset (Fin n) | s.card = r}).image
        (fun s => ∑ i, (if i ∈ s then ‖x i‖ else 0))
  have hbase_nonempty : ({s : Finset (Fin n) | s.card = r} : Set (Finset (Fin n))).Nonempty := by
    -- Choose one `r`-subset of `Fin n` from the standard `powersetCard` witness.
    have hr₂' : r ≤ (Finset.univ : Finset (Fin n)).card := by
      simpa using hr₂
    obtain ⟨s, hs⟩ : (((Finset.univ : Finset (Fin n)).powersetCard r).Nonempty) :=
      Finset.powersetCard_nonempty.2 hr₂'
    refine ⟨s, ?_⟩
    simpa [Set.mem_setOf_eq] using (Finset.mem_powersetCard_univ.1 hs)
  have htop_nonempty : ∀ x : EuclideanSpace ℝ (Fin n), (topSet x).Nonempty := by
    intro x
    rcases hbase_nonempty with ⟨s, hs⟩
    exact ⟨∑ i, (if i ∈ s then ‖x i‖ else 0), Set.mem_image_of_mem _ hs⟩
  have htop_bddAbove : ∀ x : EuclideanSpace ℝ (Fin n), BddAbove (topSet x) := by
    intro x
    -- Every candidate subset sum is bounded by the full sum of coordinate norms.
    refine ⟨∑ i, ‖x i‖, ?_⟩
    intro u hu
    rcases hu with ⟨s, hs, rfl⟩
    refine Finset.sum_le_sum ?_
    intro i hi
    by_cases his : i ∈ s
    · simp [his]
    · simp [his]
  refine ⟨convex_univ, ?_⟩
  intro x _hx y _hy a b ha hb _hab
  -- It suffices to bound each candidate subset sum for the convex combination.
  refine csSup_le (htop_nonempty (a • x + b • y)) ?_
  intro u hu
  rcases hu with ⟨s, hs, rfl⟩
  calc
    ∑ i, (if i ∈ s then ‖(a • x + b • y) i‖ else 0)
        ≤ ∑ i, (if i ∈ s then (a * ‖x i‖ + b * ‖y i‖) else 0) := by
          -- Apply the triangle inequality coordinatewise on the chosen subset.
          refine Finset.sum_le_sum ?_
          intro i hi
          by_cases his : i ∈ s
          · simpa [his] using
              (calc
                ‖(a • x + b • y) i‖ = ‖a * x i + b * y i‖ := by
                  simp
                _ ≤ ‖a * x i‖ + ‖b * y i‖ := norm_add_le _ _
                _ = a * ‖x i‖ + b * ‖y i‖ := by
                  simp [norm_mul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb])
          · simp [his]
    _ = ∑ i, ((if i ∈ s then a * ‖x i‖ else 0) + (if i ∈ s then b * ‖y i‖ else 0)) := by
          -- Rewrite the subset indicator of a sum as the sum of two subset indicators.
          refine Finset.sum_congr rfl ?_
          intro i hi
          by_cases his : i ∈ s <;> simp [his]
    _ = (∑ i, (if i ∈ s then a * ‖x i‖ else 0)) + ∑ i, (if i ∈ s then b * ‖y i‖ else 0) := by
          rw [Finset.sum_add_distrib]
    _ = a * (∑ i, (if i ∈ s then ‖x i‖ else 0)) + b * (∑ i, (if i ∈ s then ‖y i‖ else 0)) := by
          -- Split the sum into the `x` and `y` parts and factor out the coefficients.
          congr 1
          · symm
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases his : i ∈ s <;> simp [his]
          · symm
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases his : i ∈ s <;> simp [his]
    _ ≤ a * sSup (topSet x) + b * sSup (topSet y) := by
          -- Each fixed subset sum is bounded by the corresponding global supremum.
          exact add_le_add
            (mul_le_mul_of_nonneg_left
              (le_csSup (htop_bddAbove x) (Set.mem_image_of_mem _ hs)) ha)
            (mul_le_mul_of_nonneg_left
              (le_csSup (htop_bddAbove y) (Set.mem_image_of_mem _ hs)) hb)

end «problem-112»
