import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-144»
/-
Let f: ℝ^n → ℝ be convex and g: ℝ^n → ℝ be concave, with g(x) ≤ f(x) for all x ∈ ℝ^n. Prove that
there exists an affine function h(x) = aᵀx + b such that g(x) ≤ h(x) ≤ f(x) for all x ∈ ℝ^n.
-/

/-- The vertical vector `(0, t)` is the scalar multiple `t • (0, 1)` in the product space. -/
lemma zero_prod_eq_smul_vertical {n : ℕ} (t : ℝ) :
    (((0 : Fin n → ℝ), t) : (Fin n → ℝ) × ℝ) = t • ((0 : Fin n → ℝ), (1 : ℝ)) := by
  -- Check the two product coordinates directly.
  ext <;> simp [smul_eq_mul]

/-- A continuous linear functional on a product splits into horizontal and vertical parts. -/
lemma separator_apply_eq_add_mul {n : ℕ}
    (L : StrongDual ℝ ((Fin n → ℝ) × ℝ)) (x : Fin n → ℝ) (t : ℝ) :
    L (x, t) = (L.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) ℝ)) x + L (0, 1) * t := by
  -- Split `(x, t)` into its horizontal and vertical components.
  have hsplit : (((x, t) : (Fin n → ℝ) × ℝ)) = (x, 0) + ((0 : Fin n → ℝ), t) := by
    ext <;> simp
  rw [hsplit, map_add]
  -- Evaluate the vertical part by linearity along the line spanned by `(0, 1)`.
  rw [zero_prod_eq_smul_vertical t, map_smul, smul_eq_mul]
  simp [ContinuousLinearMap.comp_apply, mul_comm]

/-- Evaluating a separator on the vertical axis is multiplication by its value at `(0, 1)`. -/
lemma separator_apply_vertical {n : ℕ}
    (L : StrongDual ℝ ((Fin n → ℝ) × ℝ)) (t : ℝ) :
    L ((0 : Fin n → ℝ), t) = L (0, 1) * t := by
  -- The vertical axis is the span of `(0, 1)`.
  rw [zero_prod_eq_smul_vertical t, map_smul, smul_eq_mul]
  simp [mul_comm]

/-- Expanding against the standard basis expresses a continuous linear map as a coordinate sum. -/
lemma continuousLinearMap_apply_eq_sum_pi_single {n : ℕ}
    (l : (Fin n → ℝ) →L[ℝ] ℝ) (x : Fin n → ℝ) :
    l x = ∑ i, l (Pi.single i 1) * x i := by
  -- This is the standard coordinate expansion for linear maps on a finite product.
  calc
    l x = ∑ i, x i * l (fun j => if i = j then (1 : ℝ) else 0) := by
      simpa using (LinearMap.pi_apply_eq_sum_univ (f := (l : (Fin n → ℝ) →ₗ[ℝ] ℝ)) x)
    _ = ∑ i, l (Pi.single i 1) * x i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hfun : (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
        ext j
        by_cases h : i = j
        · subst h
          simp
        · simp [h]
      have hl : l (fun j => if i = j then (1 : ℝ) else 0) = l (Pi.single i 1) := by
        simpa using congrArg l hfun
      rw [hl]
      ring

/-- The separator must have a positive vertical coefficient, otherwise it cannot separate the two
graphs in the required order. -/
lemma separator_vertical_coefficient_pos {n : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hgf : ∀ x : Fin n → ℝ, g x ≤ f x)
    {L : StrongDual ℝ ((Fin n → ℝ) × ℝ)} {u : ℝ}
    (hS : ∀ p : (Fin n → ℝ) × ℝ, p.2 < g p.1 → L p < u)
    (hT : ∀ p : (Fin n → ℝ) × ℝ, f p.1 ≤ p.2 → u ≤ L p) :
    0 < L (0, 1) := by
  -- Evaluate the separator on one point strictly below `g 0` and one point on the epigraph of `f`.
  have hbelow : L ((0 : Fin n → ℝ), g 0 - 1) < u := by
    apply hS
    linarith
  have habove : u ≤ L ((0 : Fin n → ℝ), f 0) := by
    exact hT ((0 : Fin n → ℝ), f 0) le_rfl
  have hstrict :
      L (0, 1) * (g 0 - 1) < L (0, 1) * f 0 := by
    rw [separator_apply_vertical L (g 0 - 1)] at hbelow
    rw [separator_apply_vertical L (f 0)] at habove
    linarith
  have hgap : 0 < f 0 - (g 0 - 1) := by
    linarith [hgf (0 : Fin n → ℝ)]
  have hmul : 0 < L (0, 1) * (f 0 - (g 0 - 1)) := by
    linarith
  by_contra hnonpos
  have hle : L (0, 1) ≤ 0 := le_of_not_gt hnonpos
  have hnonpos_mul : L (0, 1) * (f 0 - (g 0 - 1)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hle hgap.le
  linarith

/-- A separator with positive vertical coefficient induces the desired scalar affine bounds. -/
lemma separator_induces_affine_bounds {n : ℕ} {f g : (Fin n → ℝ) → ℝ}
    {L : StrongDual ℝ ((Fin n → ℝ) × ℝ)} {u : ℝ}
    (hS : ∀ p : (Fin n → ℝ) × ℝ, p.2 < g p.1 → L p < u)
    (hT : ∀ p : (Fin n → ℝ) × ℝ, f p.1 ≤ p.2 → u ≤ L p)
    (hα : 0 < L (0, 1)) (x : Fin n → ℝ) :
    g x ≤
        (u - (L.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) ℝ)) x) / L (0, 1) ∧
      (u - (L.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) ℝ)) x) / L (0, 1) ≤ f x := by
  let l : (Fin n → ℝ) →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) ℝ)
  let α : ℝ := L (0, 1)
  have hTfx : u ≤ l x + α * f x := by
    -- Put the epigraph point `(x, f x)` into the separator inequality.
    have hmem := hT (x, f x) le_rfl
    rw [separator_apply_eq_add_mul] at hmem
    simpa [l, α] using hmem
  have hGle : l x + α * g x ≤ u := by
    -- If the separator value were above `u` at height `g x`, we could move slightly below `g x`
    -- and still stay above `u`, contradicting strict separation on the open hypograph.
    by_contra hcontra
    have hlt : u < l x + α * g x := lt_of_not_ge hcontra
    let t : ℝ := g x - (l x + α * g x - u) / (2 * α)
    have ht_lt : t < g x := by
      dsimp [t]
      have hpos_num : 0 < l x + α * g x - u := by linarith
      have hpos_den : 0 < 2 * α := by linarith
      have hpos_frac : 0 < (l x + α * g x - u) / (2 * α) :=
        div_pos hpos_num hpos_den
      linarith
    have hsep_t : l x + α * t < u := by
      have hmem := hS (x, t) ht_lt
      rw [separator_apply_eq_add_mul] at hmem
      simpa [l, α] using hmem
    have hu_lt : u < l x + α * t := by
      dsimp [t]
      field_simp [α, hα.ne']
      linarith
    linarith
  constructor
  · -- Solve the lower bound by dividing through the positive vertical coefficient.
    have hmul : α * g x ≤ u - l x := by
      linarith
    exact (le_div_iff₀ hα).2 (by simpa [mul_comm] using hmul)
  · -- Solve the upper bound in the same way using the epigraph point.
    have hmul : u - l x ≤ α * f x := by
      linarith
    exact (div_le_iff₀ hα).2 (by simpa [mul_comm] using hmul)

theorem exists_affine_between_convex_and_concave
    {n : ℕ} (f g : (Fin n → ℝ) → ℝ)
    (hf : ConvexOn ℝ Set.univ f)
    (hg : ConcaveOn ℝ Set.univ g)
    (hgf : ∀ x : Fin n → ℝ, g x ≤ f x) :
    ∃ a : Fin n → ℝ, ∃ b : ℝ, ∀ x : Fin n → ℝ, g x ≤ ∑ i, a i * x i + b ∧ ∑ i, a i * x i + b ≤ f x := by
  let S : Set ((Fin n → ℝ) × ℝ) := { p | p.2 < g p.1 }
  let T : Set ((Fin n → ℝ) × ℝ) := { p | f p.1 ≤ p.2 }
  have hfcont : Continuous f := by
    -- Convex functions on all of `ℝ^n` are continuous.
    simpa [continuousOn_univ] using hf.continuousOn isOpen_univ
  have hgcont : Continuous g := by
    -- Concave functions on all of `ℝ^n` are continuous.
    simpa [continuousOn_univ] using hg.continuousOn isOpen_univ
  have hSopen : IsOpen S := by
    -- The strict hypograph is open because `g` is continuous.
    simpa [S] using isOpen_lt continuous_snd (hgcont.comp continuous_fst)
  have hSconv : Convex ℝ S := by
    -- The strict hypograph of a concave function is convex.
    simpa [S] using hg.convex_strict_hypograph
  have hTconv : Convex ℝ T := by
    -- The epigraph of a convex function is convex.
    simpa [T] using hf.convex_epigraph
  have hdisj : Disjoint S T := by
    -- The pointwise hypothesis `g ≤ f` makes the two sets disjoint.
    refine Set.disjoint_left.2 ?_
    intro p hpS hpT
    exact (not_lt_of_ge (le_trans (hgf p.1) hpT)) hpS
  -- Separate the open strict hypograph from the epigraph.
  obtain ⟨L, u, hLS, hLT⟩ := geometric_hahn_banach_open hSconv hSopen hTconv hdisj
  have hSsep : ∀ p : (Fin n → ℝ) × ℝ, p.2 < g p.1 → L p < u := by
    intro p hp
    exact hLS p hp
  have hTsep : ∀ p : (Fin n → ℝ) × ℝ, f p.1 ≤ p.2 → u ≤ L p := by
    intro p hp
    exact hLT p hp
  have hα : 0 < L (0, 1) := separator_vertical_coefficient_pos hgf hSsep hTsep
  let l : (Fin n → ℝ) →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) ℝ)
  let α : ℝ := L (0, 1)
  let a : Fin n → ℝ := fun i => -(l (Pi.single i 1)) / α
  let b : ℝ := u / α
  refine ⟨a, b, ?_⟩
  intro x
  -- Convert the separator inequalities into the target affine bounds.
  have hbounds := separator_induces_affine_bounds hSsep hTsep hα x
  have hcoords : l x = ∑ i, l (Pi.single i 1) * x i :=
    continuousLinearMap_apply_eq_sum_pi_single l x
  have haff :
      (u - l x) / α = ∑ i, a i * x i + b := by
    -- Expand the linear part in coordinates and clear denominators.
    rw [hcoords]
    calc
      (u - ∑ i, l (Pi.single i 1) * x i) / α
          = u / α - ∑ i, (l (Pi.single i 1) * x i) / α := by
              rw [sub_div, Finset.sum_div]
      _ = u / α + ∑ i, (-(l (Pi.single i 1)) / α * x i) := by
            rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
            congr 1
            refine Finset.sum_congr rfl ?_
            intro i hi
            field_simp [hα.ne']
      _ = ∑ i, a i * x i + b := by
            simp [a, b, add_comm]
  constructor
  · -- Rewrite the scalar affine bound into the required coordinate form.
    rw [← haff]
    exact hbounds.1
  · -- Do the same for the upper bound.
    rw [← haff]
    exact hbounds.2
end «problem-144»
