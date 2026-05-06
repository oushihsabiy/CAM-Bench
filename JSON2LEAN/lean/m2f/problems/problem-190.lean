import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-190»

/- [BLOCK Exercise 3.28-(b) | 26 | defn]
The epigraph of a function f : ℝ^n → ℝ cup {∞} is
epi f = {(x,t) ∈ ℝ^n × ℝ | f(x) ≤ t}.
-/
def epigraph {n : ℕ} (f : (Fin n → ℝ) → WithTop ℝ) : Set ((Fin n → ℝ) × ℝ) :=
  { p | f p.1 ≤ p.2 }

/-- Any continuous linear functional on `Fin n → ℝ` is a coordinate sum. -/
lemma continuousLinearMap_eq_fin_sum {n : ℕ} (L : StrongDual ℝ (Fin n → ℝ)) :
    ∃ a : Fin n → ℝ, ∀ z, L z = ∑ i, a i * z i := by
  -- Expand the vector in the standard basis and apply linearity termwise.
  refine ⟨fun i => L ((Pi.basisFun ℝ (Fin n)) i), ?_⟩
  intro z
  nth_rewrite 1 [← Module.Basis.sum_repr (Pi.basisFun ℝ (Fin n)) z]
  rw [map_sum]
  simpa [smul_eq_mul, mul_comm, Pi.basisFun_repr]

/-- A continuous linear functional on `ℝ` is multiplication by its value at `1`. -/
lemma continuousLinearMap_real_eq_mul (L : StrongDual ℝ ℝ) (t : ℝ) :
    L t = t * L 1 := by
  -- Rewrite `t` as a scalar multiple of `1` and use linearity.
  calc
    L t = L (t • (1 : ℝ)) := by simp
    _ = t • L 1 := by rw [map_smul]
    _ = t * L 1 := by rw [smul_eq_mul]

/-- The epigraph is upward closed in the vertical coordinate. -/
lemma epigraph_vertical_mono {n : ℕ} {f : (Fin n → ℝ) → WithTop ℝ} {z : Fin n → ℝ} {t s : ℝ}
    (ht : (z, t) ∈ epigraph f) (hts : t ≤ s) : (z, s) ∈ epigraph f := by
  -- Moving upward only weakens the defining inequality `f z ≤ _`.
  have ht' : f z ≤ (t : WithTop ℝ) := by simpa [epigraph] using ht
  have hts' : (t : WithTop ℝ) ≤ (s : WithTop ℝ) := by exact_mod_cast hts
  exact show f z ≤ (s : WithTop ℝ) from ht'.trans hts'

/-- A nonempty epigraph is equivalent to the existence of one finite value of `f`. -/
lemma epigraph_nonempty_iff_exists_finite_value {n : ℕ} {f : (Fin n → ℝ) → WithTop ℝ} :
    (epigraph f).Nonempty ↔ ∃ z, f z ≠ ⊤ := by
  constructor
  · rintro ⟨⟨z, t⟩, hz⟩
    -- Any epigraph point forces the corresponding function value to be finite.
    refine ⟨z, fun htop => ?_⟩
    simpa [epigraph, htop] using hz
  · rintro ⟨z, hz⟩
    -- A finite value gives an explicit point on the epigraph.
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hz
    exact ⟨(z, t), by simpa [epigraph, ht]⟩

/-- On the product space, the second-coordinate functional is scalar multiplication by `L (0, 1)`. -/
lemma continuousLinearMap_prod_right_eq_mul {n : ℕ}
    (L : StrongDual ℝ ((Fin n → ℝ) × ℝ)) (t : ℝ) :
    L (0, t) = t * L (0, 1) := by
  -- Rewrite `(0, t)` as a scalar multiple of `(0, 1)` and use linearity.
  calc
    L (0, t) = L (t • ((0 : Fin n → ℝ), (1 : ℝ))) := by simp
    _ = t • L ((0 : Fin n → ℝ), (1 : ℝ)) := by rw [map_smul]
    _ = t * L ((0 : Fin n → ℝ), (1 : ℝ)) := by rw [smul_eq_mul]

/-- A continuous linear functional on the product splits into its horizontal and vertical parts. -/
lemma continuousLinearMap_prod_eq_add {n : ℕ}
    (L : StrongDual ℝ ((Fin n → ℝ) × ℝ)) (z : Fin n → ℝ) (t : ℝ) :
    L (z, t) = (L.comp (.inl ℝ (Fin n → ℝ) ℝ)) z + t * L (0, 1) := by
  -- This is the standard decomposition of a product functional.
  calc
    L (z, t) = L ((z, 0) + (0, t)) := by simp
    _ = L (z, 0) + L (0, t) := by rw [map_add]
    _ = (L.comp (.inl ℝ (Fin n → ℝ) ℝ)) z + t * L (0, 1) := by
      rw [continuousLinearMap_prod_right_eq_mul]
      rfl

/-- A separator with positive vertical coefficient yields an affine minorant taking value `r` at `x`.
-/
lemma exists_affine_minorant_eq_of_positive_separator
    {n : ℕ} {f : (Fin n → ℝ) → WithTop ℝ} {x : Fin n → ℝ} {r u : ℝ}
    (L : StrongDual ℝ ((Fin n → ℝ) × ℝ))
    (hxu : L (x, r) < u)
    (hsep : ∀ b ∈ epigraph f, u < L b)
    (hβ : 0 < L (0, 1)) :
    ∃ a : Fin n → ℝ, ∃ b : ℝ,
      (∀ z : Fin n → ℝ, (((∑ i, a i * z i) + b : ℝ) : WithTop ℝ) ≤ f z) ∧
      ((∑ i, a i * x i) + b : ℝ) = r := by
  let uLin : StrongDual ℝ (Fin n → ℝ) := L.comp (.inl ℝ (Fin n → ℝ) ℝ)
  let β : ℝ := L (0, 1)
  let c : ℝ := β⁻¹
  obtain ⟨α, hα⟩ := continuousLinearMap_eq_fin_sum uLin
  have hβ_def : β = L (0, 1) := rfl
  have hc : 0 < c := by
    -- The positive vertical coefficient can be inverted.
    exact inv_pos.2 (hβ_def ▸ hβ)
  have hcβ : c * β = 1 := by
    -- This is the normalization identity used by the affine formula.
    have hβnz : β ≠ 0 := by linarith
    dsimp [c]
    field_simp [hβnz]
  refine ⟨fun i => -c * α i, c * uLin x + r, ?_, ?_⟩
  · intro z
    -- Route correction: on points with `f z = ⊤` the minorant inequality is immediate,
    -- so only finite epigraph points need the separation inequality.
    by_cases hzTop : f z = ⊤
    · simp [hzTop]
    · obtain ⟨fz, hfz⟩ := WithTop.ne_top_iff_exists.1 hzTop
      have hzmem : (z, fz) ∈ epigraph f := by simpa [epigraph, hfz]
      have hlt : L (x, r) < L (z, fz) := lt_trans hxu (hsep _ hzmem)
      have hlt' : uLin x + β * r < uLin z + β * fz := by
        rw [continuousLinearMap_prod_eq_add L x r, continuousLinearMap_prod_eq_add L z fz] at hlt
        simpa [uLin, β, mul_comm, add_comm, add_left_comm, add_assoc] using hlt
      have hmul :=
        mul_le_mul_of_nonneg_left hlt'.le hc.le
      have hmul' : c * uLin x + r ≤ c * uLin z + fz := by
        have hcβr : c * (β * r) = r := by
          calc
            c * (β * r) = (c * β) * r := by ring
            _ = r := by rw [hcβ, one_mul]
        have hcβfz : c * (β * fz) = fz := by
          calc
            c * (β * fz) = (c * β) * fz := by ring
            _ = fz := by rw [hcβ, one_mul]
        rw [mul_add, mul_add, hcβr, hcβfz] at hmul
        exact hmul
      have hreal : ((∑ i, (-c * α i) * z i) + (c * uLin x + r) : ℝ) ≤ fz := by
        have hu : -c * uLin z + (c * uLin x + r) ≤ fz := by
          nlinarith
        have hcoord :
            ((∑ i, (-c * α i) * z i) + (c * uLin x + r) : ℝ) =
              -c * uLin z + (c * uLin x + r) := by
          calc
            ((∑ i, (-c * α i) * z i) + (c * uLin x + r) : ℝ)
                = (-c * ∑ i, α i * z i) + (c * uLin x + r) := by
                    rw [Finset.mul_sum]
                    congr 1
                    apply Finset.sum_congr rfl
                    intro i hi
                    ring
            _ = -c * uLin z + (c * uLin x + r) := by rw [← hα z]
        rw [hcoord]
        exact hu
      have hreal' :
          ((((∑ i, (-c * α i) * z i) + (c * uLin x + r) : ℝ) : WithTop ℝ)) ≤ ((fz : ℝ) : WithTop ℝ) := by
        exact_mod_cast hreal
      simpa [hfz] using hreal'
  · -- The affine function is normalized to hit the prescribed value at `x`.
    calc
      ((∑ i, (-c * α i) * x i) + (c * uLin x + r) : ℝ)
          = -c * uLin x + (c * uLin x + r) := by
              calc
                ((∑ i, (-c * α i) * x i) + (c * uLin x + r) : ℝ)
                    = (-c * ∑ i, α i * x i) + (c * uLin x + r) := by
                        rw [Finset.mul_sum]
                        congr 1
                        apply Finset.sum_congr rfl
                        intro i hi
                        ring
                _ = -c * uLin x + (c * uLin x + r) := by rw [← hα x]
      _ = r := by ring

/-- Any finite point of a closed convex epigraph admits an affine minorant passing through a lower
real level. -/
lemma exists_affine_minorant_eq_of_lt
    {n : ℕ} {f : (Fin n → ℝ) → WithTop ℝ} {x : Fin n → ℝ} {r : ℝ}
    (hconv : Convex ℝ (epigraph f))
    (hclosed : IsClosed (epigraph f))
    (hxfin : f x ≠ ⊤)
    (hr : (((r : ℝ) : WithTop ℝ)) < f x) :
    ∃ a : Fin n → ℝ, ∃ b : ℝ,
      (∀ z : Fin n → ℝ, (((∑ i, a i * z i) + b : ℝ) : WithTop ℝ) ≤ f z) ∧
      ((∑ i, a i * x i) + b : ℝ) = r := by
  obtain ⟨fx, hfx⟩ := WithTop.ne_top_iff_exists.1 hxfin
  have hnotmem : (x, r) ∉ epigraph f := by
    intro hxmem
    exact (not_le_of_gt hr) hxmem
  obtain ⟨L, u, hxu, hsep⟩ := geometric_hahn_banach_point_closed hconv hclosed hnotmem
  let uLin : StrongDual ℝ (Fin n → ℝ) := L.comp (.inl ℝ (Fin n → ℝ) ℝ)
  let β : ℝ := L (0, 1)
  have hxmem : (x, fx) ∈ epigraph f := by simp [epigraph, hfx]
  have hlt : L (x, r) < L (x, fx) := lt_trans hxu (hsep _ hxmem)
  have hlt' : uLin x + β * r < uLin x + β * fx := by
    rw [continuousLinearMap_prod_eq_add L x r, continuousLinearMap_prod_eq_add L x fx] at hlt
    simpa [uLin, β, mul_comm, add_comm, add_left_comm, add_assoc] using hlt
  have hr_coe : (((r : ℝ) : WithTop ℝ)) < (((fx : ℝ) : WithTop ℝ)) := by simpa [hfx] using hr
  have hr' : r < fx := by exact_mod_cast hr_coe
  have hβ : 0 < β := by
    -- Comparing the separator at `(x, r)` and at the finite epigraph point `(x, f x)` forces the
    -- vertical coefficient to be positive.
    nlinarith
  exact exists_affine_minorant_eq_of_positive_separator L hxu hsep hβ

/-- A nonempty closed convex epigraph has at least one global affine minorant. -/
lemma exists_base_affine_minorant_of_nonempty_epigraph
    {n : ℕ} {f : (Fin n → ℝ) → WithTop ℝ}
    (hconv : Convex ℝ (epigraph f))
    (hclosed : IsClosed (epigraph f))
    (hE : (epigraph f).Nonempty) :
    ∃ a : Fin n → ℝ, ∃ b : ℝ,
      ∀ z : Fin n → ℝ, (((∑ i, a i * z i) + b : ℝ) : WithTop ℝ) ≤ f z := by
  obtain ⟨x, hxfin⟩ := epigraph_nonempty_iff_exists_finite_value.1 hE
  obtain ⟨fx, hfx⟩ := WithTop.ne_top_iff_exists.1 hxfin
  have hlt_coe : (((fx - 1 : ℝ) : WithTop ℝ)) < (((fx : ℝ) : WithTop ℝ)) := by
    exact_mod_cast (show fx - 1 < fx by linarith)
  have hlt : (((fx - 1 : ℝ) : WithTop ℝ)) < f x := by simpa [hfx] using hlt_coe
  obtain ⟨a, b, hminor, _⟩ := exists_affine_minorant_eq_of_lt hconv hclosed hxfin hlt
  exact ⟨a, b, hminor⟩

/-- A separator of a nonempty epigraph cannot have negative vertical coefficient. -/
lemma separator_vertical_coeff_nonneg
    {n : ℕ} {f : (Fin n → ℝ) → WithTop ℝ}
    (hE : (epigraph f).Nonempty)
    (L : StrongDual ℝ ((Fin n → ℝ) × ℝ))
    {u : ℝ}
    (hsep : ∀ b ∈ epigraph f, u < L b) :
    0 ≤ L (0, 1) := by
  by_contra hneg
  obtain ⟨⟨z₀, t₀⟩, hz₀⟩ := hE
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (L (z₀, t₀) - u) / (-(L (0, 1))) < m := by
    exact exists_nat_gt ((L (z₀, t₀) - u) / (-(L (0, 1))))
  let s : ℝ := t₀ + m
  have hs_ge : t₀ ≤ s := by
    dsimp [s]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hsmem : (z₀, s) ∈ epigraph f := epigraph_vertical_mono hz₀ hs_ge
  have hssep : u < L (z₀, s) := hsep _ hsmem
  have hs_eval : L (z₀, s) = L (z₀, t₀) + m * L (0, 1) := by
    -- Evaluate the separator after moving vertically by `m`.
    rw [show (z₀, s) = (z₀, t₀) + (0, (m : ℝ)) by
      ext <;> simp [s, add_comm, add_left_comm, add_assoc]]
    rw [map_add, continuousLinearMap_prod_right_eq_mul]
  have hm' : (L (z₀, t₀) - u) / (-(L (0, 1))) < (m : ℝ) := by exact_mod_cast hm
  have hβneg : L (0, 1) < 0 := lt_of_not_ge hneg
  rw [hs_eval] at hssep
  have hden : 0 < -(L (0, 1)) := by linarith
  have hbound : L (z₀, t₀) - u < (m : ℝ) * (-(L (0, 1))) := by
    exact (div_lt_iff₀ hden).1 hm'
  nlinarith

/-- If `f x = ⊤`, affine minorants can be made arbitrarily large at `x`. -/
lemma exists_affine_minorant_gt_of_top
    {n : ℕ} {f : (Fin n → ℝ) → WithTop ℝ} {x : Fin n → ℝ}
    (hconv : Convex ℝ (epigraph f))
    (hclosed : IsClosed (epigraph f))
    (hx : f x = ⊤)
    (hE : (epigraph f).Nonempty)
    (r : ℝ) :
    ∃ a : Fin n → ℝ, ∃ b : ℝ,
      (∀ z : Fin n → ℝ, (((∑ i, a i * z i) + b : ℝ) : WithTop ℝ) ≤ f z) ∧
      r < ((∑ i, a i * x i) + b : ℝ) := by
  obtain ⟨a₀, b₀, hbase⟩ := exists_base_affine_minorant_of_nonempty_epigraph hconv hclosed hE
  have hnotmem : (x, r + 1) ∉ epigraph f := by
    simpa [epigraph, hx]
  obtain ⟨L, u, hxu, hsep⟩ := geometric_hahn_banach_point_closed hconv hclosed hnotmem
  let uLin : StrongDual ℝ (Fin n → ℝ) := L.comp (.inl ℝ (Fin n → ℝ) ℝ)
  let β : ℝ := L (0, 1)
  have hβnonneg : 0 ≤ β := by
    -- Upward closure of the epigraph rules out a negative vertical coefficient.
    simpa [β] using separator_vertical_coeff_nonneg hE L hsep
  by_cases hβpos : 0 < β
  · obtain ⟨a, b, hminor, hxval⟩ :=
      exists_affine_minorant_eq_of_positive_separator L hxu hsep hβpos
    refine ⟨a, b, hminor, ?_⟩
    -- In the positive-vertical case, we force equality at `r + 1`.
    rw [hxval]
    linarith
  · have hβle : β ≤ 0 := le_of_not_gt hβpos
    have hβzero : β = 0 := le_antisymm hβle hβnonneg
    obtain ⟨α, hα⟩ := continuousLinearMap_eq_fin_sum uLin
    have hβzero' : L (0, 1) = 0 := by simpa [β] using hβzero
    have hux : uLin x < u := by
      have hxu' : uLin x + (r + 1) * L (0, 1) < u := by
        rw [continuousLinearMap_prod_eq_add L x (r + 1)] at hxu
        simpa [uLin] using hxu
      simpa [hβzero'] using hxu'
    let cH : ℝ := (u - uLin x)⁻¹
    have hcH : 0 < cH := by
      -- The normalization denominator is positive because the separator strictly separates `x`.
      exact inv_pos.2 (sub_pos.2 hux)
    let K : ℝ := max 1 (r - (((∑ i, a₀ i * x i) + b₀ : ℝ)) + 1)
    have hK_nonneg : 0 ≤ K := by
      dsimp [K]
      exact le_trans (by norm_num) (le_max_left _ _)
    have htilted (w : Fin n → ℝ) :
        ((∑ i, (a₀ i - K * cH * α i) * w i) + (b₀ + K * cH * u) : ℝ) =
          ((∑ i, a₀ i * w i) + b₀) - K * (cH * uLin w - cH * u) := by
      -- This is the explicit coordinate form of `g₀ - K * h`.
      have hsum :
          (∑ i, (a₀ i - K * cH * α i) * w i : ℝ) =
            (∑ i, a₀ i * w i) - K * cH * (∑ i, α i * w i) := by
        calc
          (∑ i, (a₀ i - K * cH * α i) * w i : ℝ)
              = ∑ i, (a₀ i * w i - (K * cH * α i) * w i) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
          _ = (∑ i, a₀ i * w i) - ∑ i, (K * cH * α i) * w i := by
                  rw [Finset.sum_sub_distrib]
          _ = (∑ i, a₀ i * w i) - K * cH * (∑ i, α i * w i) := by
                  rw [Finset.mul_sum]
                  congr 1
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
      rw [hsum, hα w]
      ring
    refine ⟨fun i => a₀ i - K * cH * α i, b₀ + K * cH * u, ?_, ?_⟩
    · intro z
      -- Route correction: when `β = 0`, the separator only constrains the horizontal direction, so
      -- we tilt a fixed base minorant by a normalized horizontal functional.
      by_cases hzTop : f z = ⊤
      · simp [hzTop]
      · obtain ⟨fz, hfz⟩ := WithTop.ne_top_iff_exists.1 hzTop
        have hzmem : (z, fz) ∈ epigraph f := by simpa [epigraph, hfz]
        have hzsep : u < uLin z := by
          have : u < L (z, fz) := hsep _ hzmem
          have hzsep' : u < uLin z + fz * L (0, 1) := by
            rw [continuousLinearMap_prod_eq_add L z fz] at this
            simpa [uLin] using this
          simpa [hβzero'] using hzsep'
        have hbasez : (((∑ i, a₀ i * z i) + b₀ : ℝ) : WithTop ℝ) ≤ f z := hbase z
        have hbasez' : ((∑ i, a₀ i * z i) + b₀ : ℝ) ≤ fz := by
          exact_mod_cast (show ((((∑ i, a₀ i * z i) + b₀ : ℝ) : WithTop ℝ)) ≤ ((fz : ℝ) : WithTop ℝ) by
            simpa [hfz] using hbasez)
        have htilt_nonneg : 0 ≤ cH * uLin z - cH * u := by
          nlinarith [hzsep, hcH]
        have hreal : ((∑ i, (a₀ i - K * cH * α i) * z i) + (b₀ + K * cH * u) : ℝ) ≤ fz := by
          rw [htilted z]
          nlinarith
        have hreal' :
            ((((∑ i, (a₀ i - K * cH * α i) * z i) + (b₀ + K * cH * u) : ℝ) : WithTop ℝ)) ≤
              ((fz : ℝ) : WithTop ℝ) := by
          exact_mod_cast hreal
        simpa [hfz] using hreal'
    · have hxnorm : cH * uLin x - cH * u = -1 := by
        have hden : u - uLin x ≠ 0 := by linarith
        have hcH_mul : cH * (u - uLin x) = 1 := by
          dsimp [cH]
          field_simp [hden]
        nlinarith
      have hxvalue : ((∑ i, (a₀ i - K * cH * α i) * x i) + (b₀ + K * cH * u) : ℝ) =
          ((∑ i, a₀ i * x i) + b₀) + K := by
        rw [htilted x]
        nlinarith [hxnorm]
      rw [hxvalue]
      dsimp [K]
      nlinarith [le_max_right 1 (r - (((∑ i, a₀ i * x i) + b₀ : ℝ)) + 1)]

/- [BLOCK Exercise 3.28-(b) | 27 | thm]
Let f:ℝ^n → ℝ∞ be a convex function, and define bar f:ℝ^n → ℝ∞ by bar f(x)=sup{g(x)| g:ℝ^n→ℝ is
affine and g(z)≤ f(z) for all z∈ℝ^n}, where an affine function has the form g(x)=aᵀ x+b for some
a∈ℝ^n and b∈ℝ. The epigraph of f is epi f={(x,t)∈ℝ^n×ℝ| f(x)≤ t}. The function f is called closed if
epi f is a closed subset of ℝ^n×ℝ. Show that f=bar f if f is closed.
-/
theorem closed_convex_eq_sup_affine_minorants
    {n : ℕ} (f : (Fin n → ℝ) → WithTop ℝ)
    (hconv : Convex ℝ (epigraph f))
    (hclosed : IsClosed (epigraph f)) :
    f =
      fun x =>
        sSup {r : WithTop ℝ |
          ∃ a : Fin n → ℝ, ∃ b : ℝ,
            (∀ z : Fin n → ℝ, (((∑ i, a i * z i) + b : ℝ) : WithTop ℝ) ≤ f z) ∧
            r = (((∑ i, a i * x i) + b : ℝ) : WithTop ℝ)} := by
  ext x
  let Sx : Set (WithTop ℝ) := {r : WithTop ℝ |
    ∃ a : Fin n → ℝ, ∃ b : ℝ,
      (∀ z : Fin n → ℝ, (((∑ i, a i * z i) + b : ℝ) : WithTop ℝ) ≤ f z) ∧
      r = (((∑ i, a i * x i) + b : ℝ) : WithTop ℝ)}
  change f x = sSup (Sx : Set (WithTop ℝ))
  have hSx_nonempty : Sx.Nonempty := by
    by_cases hx : f x = ⊤
    · by_cases hE : (epigraph f).Nonempty
      · obtain ⟨a, b, hminor, hgt⟩ := exists_affine_minorant_gt_of_top hconv hclosed hx hE 0
        refine ⟨(((∑ i, a i * x i) + b : ℝ) : WithTop ℝ), ?_⟩
        exact ⟨a, b, hminor, rfl⟩
      · refine ⟨((0 : ℝ) : WithTop ℝ), ?_⟩
        refine ⟨0, 0, ?_, by simp⟩
        intro z
        have hz : f z = ⊤ := by
          by_contra hztop
          exact hE (epigraph_nonempty_iff_exists_finite_value.2 ⟨z, hztop⟩)
        simp [hz]
    · obtain ⟨fx, hfx⟩ := WithTop.ne_top_iff_exists.1 hx
      have hlt_coe : (((fx - 1 : ℝ) : WithTop ℝ)) < (((fx : ℝ) : WithTop ℝ)) := by
        exact_mod_cast (show fx - 1 < fx by linarith)
      have hlt : (((fx - 1 : ℝ) : WithTop ℝ)) < f x := by simpa [hfx] using hlt_coe
      obtain ⟨a, b, hminor, hxval⟩ := exists_affine_minorant_eq_of_lt hconv hclosed hx hlt
      refine ⟨((((∑ i, a i * x i) + b : ℝ)) : WithTop ℝ), ?_⟩
      exact ⟨a, b, hminor, rfl⟩
  refine (csSup_eq_of_forall_le_of_forall_lt_exists_gt hSx_nonempty ?_ ?_).symm
  · intro r hr
    rcases hr with ⟨a, b, hminor, rfl⟩
    -- Every affine minorant lies below `f`, so its value at `x` is an upper bound for `Sx`.
    exact hminor x
  · intro w hw
    have hwne : w ≠ ⊤ := by
      exact fun htop => by simpa [htop] using hw
    obtain ⟨r, rfl⟩ := WithTop.ne_top_iff_exists.1 hwne
    by_cases hx : f x = ⊤
    · by_cases hE : (epigraph f).Nonempty
      · obtain ⟨a, b, hminor, hgt⟩ := exists_affine_minorant_gt_of_top hconv hclosed hx hE r
        have hgt' : (((r : ℝ) : WithTop ℝ)) < ((((∑ i, a i * x i) + b : ℝ) : WithTop ℝ)) := by
          exact_mod_cast hgt
        refine ⟨(((∑ i, a i * x i) + b : ℝ) : WithTop ℝ), ?_, hgt'⟩
        exact ⟨a, b, hminor, rfl⟩
      · have hAllTop : ∀ z : Fin n → ℝ, f z = ⊤ := by
          intro z
          by_contra hz
          exact hE (epigraph_nonempty_iff_exists_finite_value.2 ⟨z, hz⟩)
        have hlt : (((r : ℝ) : WithTop ℝ)) < (((r + 1 : ℝ)) : WithTop ℝ) := by
          exact_mod_cast (show r < r + 1 by linarith)
        refine ⟨(((r + 1 : ℝ)) : WithTop ℝ), ?_, hlt⟩
        refine ⟨0, r + 1, ?_, by simp⟩
        intro z
        simp [hAllTop z]
    · obtain ⟨fx, hfx⟩ := WithTop.ne_top_iff_exists.1 hx
      have hrfx_coe : (((r : ℝ) : WithTop ℝ)) < (((fx : ℝ) : WithTop ℝ)) := by
        simpa [hfx] using hw
      have hrfx : r < fx := by exact_mod_cast hrfx_coe
      obtain ⟨r', hrr', hr'fx⟩ := exists_between hrfx
      have hr' : (((r' : ℝ) : WithTop ℝ)) < f x := by
        have hr'coe : (((r' : ℝ) : WithTop ℝ)) < (((fx : ℝ) : WithTop ℝ)) := by
          exact_mod_cast hr'fx
        simpa [hfx] using hr'coe
      obtain ⟨a, b, hminor, hxval⟩ := exists_affine_minorant_eq_of_lt hconv hclosed hx hr'
      refine ⟨(((∑ i, a i * x i) + b : ℝ) : WithTop ℝ), ?_, ?_⟩
      · exact ⟨a, b, hminor, rfl⟩
      · simpa [hxval] using hrr'

end «problem-190»
