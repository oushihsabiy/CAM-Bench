import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-192»

/- [BLOCK Exercise 1.6-(c) | 7 | defn]
For a set C ⊆ ℝ^n, its polar is
C^{circ} = {y ∈ ℝ^n | yᵀ x ≤ 1 for all x ∈ C}.
-/
def polar (C : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {y | ∀ x ∈ C, dotProduct y x ≤ 1}

/- [BLOCK Exercise 1.6-(c) | 8 | defn]
Given a norm ‖·‖ on ℝ^n, its dual norm is defined by
‖y‖_* = yᵀ x | ‖x‖ ≤ 1, y ∈ ℝ^n.
-/
def dualNorm (norm : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x : Fin n → ℝ, norm x ≤ 1 ∧ r = dotProduct y x}

/-- The raw norm is invariant under negation because it is absolutely homogeneous. -/
lemma rawNorm_neg
    (norm : (Fin n → ℝ) → ℝ)
    (hnorm_smul : ∀ (a : ℝ) (x : Fin n → ℝ), norm (a • x) = |a| * norm x)
    (x : Fin n → ℝ) :
    norm (-x) = norm x := by
  -- Negation is scalar multiplication by `-1`, and `|-1| = 1`.
  simpa using hnorm_smul (-1) x

/-- The raw norm of a finite sum is bounded by the sum of the raw norms. -/
lemma rawNorm_sum_le
    (norm : (Fin n → ℝ) → ℝ)
    (hnorm_zero : norm 0 = 0)
    (hnorm_add : ∀ x y : Fin n → ℝ, norm (x + y) ≤ norm x + norm y)
    {α : Type*} (s : Finset α) (f : α → Fin n → ℝ) :
    norm (Finset.sum s f) ≤ Finset.sum s (fun a => norm (f a)) := by
  classical
  -- Induct over the finite sum and use the assumed triangle inequality at each step.
  refine Finset.induction_on s ?_ ?_
  · simp [hnorm_zero]
  · intro a s ha hs
    have hstep : norm (f a + Finset.sum s f) ≤ norm (f a) + Finset.sum s (fun b => norm (f b)) := by
      -- Apply the triangle inequality once, then insert the induction bound.
      exact (hnorm_add _ _).trans (by gcongr)
    simpa [ha] using hstep

/-- The raw norm is bounded above by the ambient norm times a fixed coordinate constant. -/
lemma rawNorm_le_ambient_mul
    (norm : (Fin n → ℝ) → ℝ)
    (hnorm_nonneg : ∀ x : Fin n → ℝ, 0 ≤ norm x)
    (hnorm_zero : norm 0 = 0)
    (hnorm_smul : ∀ (a : ℝ) (x : Fin n → ℝ), norm (a • x) = |a| * norm x)
    (hnorm_add : ∀ x y : Fin n → ℝ, norm (x + y) ≤ norm x + norm y) :
    ∃ C, 0 ≤ C ∧ ∀ z : Fin n → ℝ, norm z ≤ C * ‖z‖ := by
  let C : ℝ := ∑ i, norm ((Pi.single i (1 : ℝ)) : Fin n → ℝ)
  refine ⟨C, Finset.sum_nonneg fun i _ => hnorm_nonneg _, ?_⟩
  intro z
  have hz : (∑ i, z i • ((Pi.single i (1 : ℝ)) : Fin n → ℝ)) = z := by
    -- Expand a vector into the standard coordinate singletons.
    ext j
    simp [Pi.single_apply]
  calc
    norm z = norm (∑ i, z i • ((Pi.single i (1 : ℝ)) : Fin n → ℝ)) := by rw [hz]
    _ ≤ ∑ i, norm (z i • ((Pi.single i (1 : ℝ)) : Fin n → ℝ)) :=
      rawNorm_sum_le norm hnorm_zero hnorm_add _ _
    _ = ∑ i, |z i| * norm (((Pi.single i (1 : ℝ)) : Fin n → ℝ)) := by simp [hnorm_smul]
    _ ≤ ∑ i, ‖z‖ * norm (((Pi.single i (1 : ℝ)) : Fin n → ℝ)) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact mul_le_mul_of_nonneg_right
        (by simpa [Real.norm_eq_abs] using (norm_le_pi_norm z i))
        (hnorm_nonneg _)
    _ = ‖z‖ * C := by simp [C, Finset.mul_sum]
    _ = C * ‖z‖ := by ring

/-- The reverse triangle inequality for the raw norm. -/
lemma rawNorm_sub_le
    (norm : (Fin n → ℝ) → ℝ)
    (hnorm_smul : ∀ (a : ℝ) (x : Fin n → ℝ), norm (a • x) = |a| * norm x)
    (hnorm_add : ∀ x y : Fin n → ℝ, norm (x + y) ≤ norm x + norm y)
    (u v : Fin n → ℝ) :
    |norm u - norm v| ≤ norm (u - v) := by
  have huv : norm u ≤ norm v + norm (u - v) := by
    -- Rewrite `u` as `v + (u - v)` and apply the triangle inequality.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hnorm_add v (u - v)
  have hsymm : norm (v - u) = norm (u - v) := by
    -- The raw norm is invariant under negation, so the order of subtraction does not matter.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      rawNorm_neg norm hnorm_smul (u - v)
  have hvu : norm v ≤ norm u + norm (u - v) := by
    calc
      norm v ≤ norm u + norm (v - u) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hnorm_add u (v - u)
      _ = norm u + norm (u - v) := by rw [hsymm]
  have h₁ : norm u - norm v ≤ norm (u - v) := by linarith
  have h₂ : norm v - norm u ≤ norm (u - v) := by linarith
  exact abs_sub_le_iff.2 ⟨h₁, h₂⟩

/-- The raw norm is continuous for the ambient topology. -/
lemma rawNorm_continuous
    (norm : (Fin n → ℝ) → ℝ)
    (hnorm_nonneg : ∀ x : Fin n → ℝ, 0 ≤ norm x)
    (hnorm_zero : norm 0 = 0)
    (hnorm_smul : ∀ (a : ℝ) (x : Fin n → ℝ), norm (a • x) = |a| * norm x)
    (hnorm_add : ∀ x y : Fin n → ℝ, norm (x + y) ≤ norm x + norm y) :
    Continuous norm := by
  obtain ⟨C, hC_nonneg, hC⟩ :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin n → ℝ, norm z ≤ C * ‖z‖ :=
    rawNorm_le_ambient_mul norm hnorm_nonneg hnorm_zero hnorm_smul hnorm_add
  let K : NNReal := ⟨C, hC_nonneg⟩
  -- The reverse triangle inequality plus the ambient comparison makes the raw norm Lipschitz.
  refine (LipschitzWith.of_dist_le_mul (K := K) fun u v => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm]
  calc
    |norm u - norm v| ≤ norm (u - v) := rawNorm_sub_le norm hnorm_smul hnorm_add u v
    _ ≤ C * ‖u - v‖ := hC (u - v)
    _ = (K : ℝ) * dist u v := by simp [K, dist_eq_norm]

/-- The raw unit ball is bounded in the ambient norm on `Fin n → ℝ`. -/
lemma ambientNorm_bounded_on_rawUnitBall
    (norm : (Fin n → ℝ) → ℝ)
    (hnorm_nonneg : ∀ x : Fin n → ℝ, 0 ≤ norm x)
    (hnorm_zero : norm 0 = 0)
    (hnorm_smul : ∀ (a : ℝ) (x : Fin n → ℝ), norm (a • x) = |a| * norm x)
    (hnorm_add : ∀ x y : Fin n → ℝ, norm (x + y) ≤ norm x + norm y)
    (hnorm_pos : ∀ x : Fin n → ℝ, norm x = 0 → x = 0) :
    ∃ K, 0 ≤ K ∧ ∀ x : Fin n → ℝ, norm x ≤ 1 → ‖x‖ ≤ K := by
  classical
  by_cases hne : Nonempty (Fin n)
  · let f : (Fin n → ℝ) → ℝ := norm
    have hf_cont : Continuous f := rawNorm_continuous norm hnorm_nonneg hnorm_zero hnorm_smul hnorm_add
    have hsphere_nonempty : (Metric.sphere (0 : Fin n → ℝ) 1).Nonempty := by
      refine ⟨(fun _ : Fin n => (1 : ℝ)), ?_⟩
      simpa [Metric.mem_sphere, dist_eq_norm] using
        (pi_norm_const' (ι := Fin n) (a := (1 : ℝ)))
    obtain ⟨u, hu_sphere, hu_min⟩ :=
      (isCompact_sphere (0 : Fin n → ℝ) 1).exists_isMinOn hsphere_nonempty hf_cont.continuousOn
    have hu_ne_zero : u ≠ 0 := by
      intro hu0
      have : ‖u‖ = 0 := by simpa [hu0]
      have hu_norm : ‖u‖ = 1 := by simp [Metric.mem_sphere, dist_eq_norm] at hu_sphere; exact hu_sphere
      linarith
    have hu_pos : 0 < norm u := by
      have hu_nonneg : 0 ≤ norm u := hnorm_nonneg u
      have hu_ne : norm u ≠ 0 := by
        intro hzero
        exact hu_ne_zero (hnorm_pos u hzero)
      exact lt_of_le_of_ne hu_nonneg (Ne.symm hu_ne)
    refine ⟨(norm u)⁻¹, inv_nonneg.mpr hu_pos.le, ?_⟩
    intro x hx
    by_cases hx0 : x = 0
    · simpa [hx0] using (inv_nonneg.mpr hu_pos.le)
    · let v : Fin n → ℝ := ‖x‖⁻¹ • x
      have hv_sphere : v ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
        -- Normalize a nonzero vector to the ambient unit sphere.
        have hxnorm_ne : ‖x‖ ≠ 0 := by simpa [norm_eq_zero] using hx0
        simp [v, hxnorm_ne, norm_smul]
      have hu_min' : ∀ z ∈ Metric.sphere (0 : Fin n → ℝ) 1, norm u ≤ norm z := by
        simpa [isMinOn_iff] using hu_min
      have hmin_le : norm u ≤ norm v := hu_min' v hv_sphere
      have hv_bound : norm v ≤ ‖x‖⁻¹ := by
        -- Raw homogeneity converts the unit-ball hypothesis into an upper bound on `norm v`.
        calc
          norm v = |‖x‖⁻¹| * norm x := by
            simp [v, hnorm_smul]
          _ = ‖x‖⁻¹ * norm x := by
            simp [abs_of_nonneg, norm_nonneg]
          _ ≤ ‖x‖⁻¹ * 1 := by
            exact mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr (norm_nonneg x))
          _ = ‖x‖⁻¹ := by ring
      have hmul : norm u * ‖x‖ ≤ 1 := by
        have hxnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
        have := mul_le_mul_of_nonneg_right (hmin_le.trans hv_bound) hxnorm_pos.le
        simpa [hxnorm_pos.ne', mul_assoc, mul_left_comm, mul_comm] using this
      -- Rearranging the positive minimum bound yields a uniform ambient bound.
      have hmul' : ‖x‖ * norm u ≤ 1 := by simpa [mul_comm] using hmul
      simpa [one_div] using (le_div_iff₀ hu_pos).2 hmul'
  · refine ⟨0, le_rfl, ?_⟩
    intro x _hx
    have hx0 : x = 0 := by
      funext i
      exact False.elim (hne ⟨i⟩)
    simp [hx0]

/-- Each admissible dot product is controlled by the ambient supremum norm of the test vector. -/
lemma dotProduct_le_sumAbs_mul_ambientNorm (y x : Fin n → ℝ) :
    dotProduct y x ≤ (∑ i, |y i|) * ‖x‖ := by
  -- Take absolute values and then bound each coordinate by the ambient norm.
  calc
    dotProduct y x ≤ |dotProduct y x| := le_abs_self _
    _ = |∑ i, y i * x i| := by simp [dotProduct]
    _ ≤ ∑ i, |y i * x i| := by
      simpa using (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun i : Fin n => y i * x i))
    _ = ∑ i, |y i| * |x i| := by
      simp [abs_mul]
    _ ≤ ∑ i, |y i| * ‖x‖ := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (by simpa [Real.norm_eq_abs] using (norm_le_pi_norm x i))
        (abs_nonneg _)
    _ = (∑ i, |y i|) * ‖x‖ := by
      rw [Finset.sum_mul]

/-- The candidate set defining the dual norm is bounded above. -/
lemma dualNormCandidateSet_bddAbove
    (norm : (Fin n → ℝ) → ℝ)
    (hnorm_nonneg : ∀ x : Fin n → ℝ, 0 ≤ norm x)
    (hnorm_zero : norm 0 = 0)
    (hnorm_smul : ∀ (a : ℝ) (x : Fin n → ℝ), norm (a • x) = |a| * norm x)
    (hnorm_add : ∀ x y : Fin n → ℝ, norm (x + y) ≤ norm x + norm y)
    (hnorm_pos : ∀ x : Fin n → ℝ, norm x = 0 → x = 0)
    (y : Fin n → ℝ) :
    BddAbove {r : ℝ | ∃ x : Fin n → ℝ, norm x ≤ 1 ∧ r = dotProduct y x} := by
  obtain ⟨K, _hKpos, hK⟩ :=
    ambientNorm_bounded_on_rawUnitBall norm hnorm_nonneg hnorm_zero hnorm_smul hnorm_add hnorm_pos
  refine ⟨(∑ i, |y i|) * K, ?_⟩
  intro r hr
  rcases hr with ⟨x, hx, rfl⟩
  have hambient : ‖x‖ ≤ K := hK x hx
  -- The ambient bound on the raw unit ball turns the coordinate estimate into a uniform scalar bound.
  calc
    dotProduct y x ≤ (∑ i, |y i|) * ‖x‖ := dotProduct_le_sumAbs_mul_ambientNorm y x
    _ ≤ (∑ i, |y i|) * K := by
      exact mul_le_mul_of_nonneg_left hambient (Finset.sum_nonneg fun i _ => abs_nonneg _)

/- [BLOCK Exercise 1.6-(c) | 9 | thm]
Let ‖·‖ be a norm on ℝ^n, and let its unit ball be B = {x ∈ ℝ^n | ‖x‖ ≤ 1}. For any set C ⊆ ℝ^n,
define its polar by C^{circ} = {y ∈ ℝ^n | yᵀ x ≤ 1 for all x ∈ C}, where yᵀ x is the standard
Euclidean inner product on ℝ^n. Define the dual norm ‖·‖_* by ‖y‖_* = yᵀ x | ‖x‖ ≤ 1. Prove that
B^{circ} = {y ∈ ℝ^n | ‖y‖_* ≤ 1}.
-/
theorem polar_unitBall_eq_dualNorm_le_one
    (norm : (Fin n → ℝ) → ℝ)
    (hnorm_nonneg : ∀ x : Fin n → ℝ, 0 ≤ norm x)
    (hnorm_zero : norm 0 = 0)
    (hnorm_smul : ∀ (a : ℝ) (x : Fin n → ℝ), norm (a • x) = |a| * norm x)
    (hnorm_add : ∀ x y : Fin n → ℝ, norm (x + y) ≤ norm x + norm y)
    (hnorm_pos : ∀ x : Fin n → ℝ, norm x = 0 → x = 0) :
    polar {x : Fin n → ℝ | norm x ≤ 1} = {y : Fin n → ℝ | dualNorm norm y ≤ 1} := by
  ext y
  change
    (∀ x : Fin n → ℝ, norm x ≤ 1 → dotProduct y x ≤ 1) ↔
      sSup {r : ℝ | ∃ x : Fin n → ℝ, norm x ≤ 1 ∧ r = dotProduct y x} ≤ 1
  set S : Set ℝ := {r : ℝ | ∃ x : Fin n → ℝ, norm x ≤ 1 ∧ r = dotProduct y x}
  constructor
  · intro hy
    -- In the polar direction, the polar inequality itself gives `1` as a uniform upper bound.
    have hS_nonempty : S.Nonempty := by
      refine ⟨0, ?_⟩
      refine ⟨0, ?_, by simp⟩
      simp [hnorm_zero]
    have hbound : ∀ r ∈ S, r ≤ 1 := by
      intro r hr
      rcases hr with ⟨x, hx, rfl⟩
      exact hy x hx
    exact csSup_le hS_nonempty hbound
  · intro hy x hx
    -- Route correction: instead of building a shadow normed-space structure, work entirely in the
    -- ambient norm, prove the raw unit ball is ambiently bounded, and then use a coordinate bound
    -- for `dotProduct`.
    have hS_bdd : BddAbove S := by
      -- The auxiliary lemma already packages the raw unit ball bound and the dot-product estimate.
      simpa [S] using
        dualNormCandidateSet_bddAbove norm hnorm_nonneg hnorm_zero hnorm_smul hnorm_add hnorm_pos y
    -- The value `yᵀx` is one admissible candidate, so it lies below the supremum.
    have hmem : dotProduct y x ∈ S := ⟨x, hx, rfl⟩
    exact (le_csSup hS_bdd hmem).trans hy

end «problem-192»
