import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-41»
/-
For a function f: ℝ^n → ℝ cup {+ ∞}, its convex conjugate f*: ℝ^n → ℝ cup {+ ∞} is defined by f*(y)
=
sup_{z ∈ ℝ^n} (yᵀ z - f(z)).
-/
open scoped BigOperators

def convexConjugate {n : ℕ} (f : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun y => sSup (Set.range fun z : Fin n → ℝ => (∑ i, y i * z i : ℝ) - f z)

/-- Convexity bounds the secant from `z` to `w` below by the derivative at `z`. -/
lemma convex_first_order_condition {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hconv : ConvexOn ℝ Set.univ f) {z : Fin n → ℝ} (hz : DifferentiableAt ℝ f z) :
    ∀ w, f z + (fderiv ℝ f z) (w - z) ≤ f w := by
  intro w
  -- Restrict the convex function to the affine line through `z` and `w`.
  let g : ℝ → ℝ := fun t => f (ContinuousAffineMap.lineMap (R := ℝ) z w t)
  -- Convexity is preserved when we precompose with that affine line.
  have hgconv : ConvexOn ℝ Set.univ g := by
    simpa [g, Set.preimage_univ, ContinuousAffineMap.coe_lineMap_eq] using
      (hconv.comp_affineMap (AffineMap.lineMap z w))
  -- Differentiate the one-dimensional restriction by chaining the derivative of `f`
  -- with the derivative of the line map.
  have hgderiv : HasDerivAt g ((fderiv ℝ f z) (w - z)) 0 := by
    let line : ℝ →ᴬ[ℝ] (Fin n → ℝ) := ContinuousAffineMap.lineMap (R := ℝ) z w
    have hz' : HasFDerivAt f (fderiv ℝ f z) (line 0) := by
      simpa [line, ContinuousAffineMap.coe_lineMap_eq] using hz.hasFDerivAt
    have hcompF : HasFDerivAt (f ∘ line) ((fderiv ℝ f z).comp line.contLinear) (0 : ℝ) :=
      hz'.comp (0 : ℝ) line.hasFDerivAt
    have hcomp : HasDerivAt (f ∘ line) (((fderiv ℝ f z).comp line.contLinear) 1) (0 : ℝ) :=
      hcompF.hasDerivAt
    simpa [g, line, ContinuousAffineMap.coe_lineMap_eq] using hcomp
  -- The derivative at `0` is bounded above by the secant slope from `0` to `1`.
  have hslope := ConvexOn.le_slope_of_hasDerivAt hgconv (by simp) (by simp) zero_lt_one hgderiv
  have hslope' : (fderiv ℝ f z) (w - z) ≤ f w - f z := by
    simpa [g, slope, ContinuousAffineMap.coe_lineMap_eq] using hslope
  -- Rearranging the slope inequality gives the desired first-order convex bound.
  linarith

/-- If the coordinate dual variable matches the derivative at `z`, then the convex conjugate is
attained at `z`. -/
lemma convexConjugate_eq_of_coordinate_derivative {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hconv : ConvexOn ℝ Set.univ f) {y z : Fin n → ℝ} (hz : DifferentiableAt ℝ f z)
    (hy : ∀ i, y i = (fderiv ℝ f z) (Pi.single i (1 : ℝ) : Fin n → ℝ)) :
    convexConjugate (fun w => (f w : EReal)) y = (((∑ i, y i * z i : ℝ) - f z : ℝ) : EReal) := by
  -- First identify the full derivative with the coordinate formula encoded by `y`.
  have hy_apply : ∀ v, (fderiv ℝ f z) v = ∑ i, y i * v i := by
    intro v
    calc
      (fderiv ℝ f z) v = (fderiv ℝ f z) (∑ i, v i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
        congr 1
        ext i
        simp [Pi.single_apply]
      _ = ∑ i, v i * (fderiv ℝ f z) (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
        simp
      _ = ∑ i, y i * v i := by
        simp [hy, mul_comm]
  -- The first-order convex inequality shows every candidate in the supremum is bounded above
  -- by the value attained at `z`.
  have h_upper_real : ∀ w, (∑ i, y i * w i : ℝ) - f w ≤ (∑ i, y i * z i : ℝ) - f z := by
    intro w
    have hsupport := convex_first_order_condition hconv hz w
    have hsupport' : f z + ∑ i, y i * (w - z) i ≤ f w := by
      simpa [hy_apply] using hsupport
    have hsum : (∑ i, y i * (w - z) i : ℝ) = (∑ i, y i * w i : ℝ) - ∑ i, y i * z i := by
      simp [sub_eq_add_neg, mul_add, Finset.sum_add_distrib]
    linarith [hsupport']
  -- Convert the real upper bound into an `EReal` bound so it applies to the supremum.
  have h_bdd : BddAbove (Set.range fun w : Fin n → ℝ => ((∑ i, y i * w i : ℝ) - (f w : EReal))) := by
    refine ⟨(((∑ i, y i * z i : ℝ) - f z : ℝ) : EReal), ?_⟩
    intro a ha
    rcases ha with ⟨w, rfl⟩
    change (((∑ i, y i * w i : ℝ) - f w : ℝ) : EReal) ≤ _
    exact_mod_cast h_upper_real w
  -- The supremum is both bounded above by the value at `z` and bounded below by the witness `z`.
  apply le_antisymm
  · refine csSup_le ?_ ?_
    · refine ⟨_, ⟨0, rfl⟩⟩
    · intro a ha
      rcases ha with ⟨w, rfl⟩
      change (((∑ i, y i * w i : ℝ) - f w : ℝ) : EReal) ≤ _
      exact_mod_cast h_upper_real w
  · refine le_csSup h_bdd ?_
    exact ⟨z, by simp⟩

/-- A continuous linear functional on `Fin n → ℝ` is determined by its values on the standard
basis vectors. -/
lemma continuousLinearMap_apply_eq_sum_piSingle {n : ℕ}
    (L : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    L v = ∑ i, v i * L (Pi.single i (1 : ℝ)) := by
  -- Expand `v` in the standard basis and use linearity term-by-term.
  calc
    L v = L (∑ i, v i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
      congr 1
      ext j
      simp [Pi.single_apply]
    _ = ∑ i, L (v i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
      simp
    _ = ∑ i, v i * L (Pi.single i (1 : ℝ)) := by
      simp

/-- A positive definite real matrix is symmetric. -/
lemma posDef_isSymm_real {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef) :
    M.IsSymm := by
  -- Over `ℝ`, Hermitian is exactly symmetric, so positivity gives the symmetry for free.
  simpa [Matrix.IsHermitian, Matrix.conjTranspose] using hM.isHermitian

/-- For a positive definite real matrix, the coordinate action of `Matrix.toLin'` can be read from
the corresponding column because the matrix is symmetric. -/
lemma posDef_matrix_toLin'_apply_eq_sum {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef) (v : Fin n → ℝ) (j : Fin n) :
    (Matrix.toLin' M v) j = ∑ i, v i * M i j := by
  have hsymm : M.IsSymm := posDef_isSymm_real hM
  -- Rewrite the matrix action in row form, then swap the indices using symmetry.
  calc
    (Matrix.toLin' M v) j = ∑ i, M j i * v i := by
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    _ = ∑ i, v i * M i j := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Matrix.IsSymm.apply hsymm j i, mul_comm]

/-- The coordinate-gradient map has derivative given by the Hessian matrix at the base point. -/
lemma gradF_hasFDerivAt_at_x
    {n : ℕ}
    {f : (Fin n → ℝ) → ℝ}
    {x : Fin n → ℝ}
    (hC2 : ContDiffAt ℝ 2 f x)
    (hpos :
      let hessf : Matrix (Fin n) (Fin n) ℝ :=
        fun i j =>
          (fderiv ℝ
            (fun x' => (fderiv ℝ f x') (Pi.single j (1 : ℝ))) x)
            (Pi.single i (1 : ℝ))
      hessf.PosDef) :
    let gradF : (Fin n → ℝ) → (Fin n → ℝ) :=
      fun z i => (fderiv ℝ f z) (Pi.single i (1 : ℝ))
    let hessf : Matrix (Fin n) (Fin n) ℝ :=
      fun i j =>
        (fderiv ℝ
          (fun x' => (fderiv ℝ f x') (Pi.single j (1 : ℝ))) x)
          (Pi.single i (1 : ℝ))
    HasFDerivAt gradF (LinearMap.toContinuousLinearMap (Matrix.toLin' hessf)) x := by
  dsimp
  let hessf : Matrix (Fin n) (Fin n) ℝ :=
    fun i j =>
      (fderiv ℝ
        (fun x' : Fin n → ℝ => (fderiv ℝ f x') (Pi.single j (1 : ℝ))) x)
        (Pi.single i (1 : ℝ))
  have hessf_pos : hessf.PosDef := by
    simpa [hessf] using hpos
  have hpi :
      HasFDerivAt
        (fun z : Fin n → ℝ => fun i => (fderiv ℝ f z) (Pi.single i (1 : ℝ)))
        (ContinuousLinearMap.pi fun j =>
          (ContinuousLinearMap.proj j).comp
            (LinearMap.toContinuousLinearMap (Matrix.toLin' hessf))) x := by
    refine hasFDerivAt_pi.2 ?_
    intro j
    have hcoordC1 :
        ContDiffAt ℝ 1
          (fun z : Fin n → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) x := by
      -- Differentiate the derivative field and then evaluate it on the fixed basis vector.
      exact (hC2.fderiv_right_succ.clm_apply
        (contDiffAt_const :
          ContDiffAt ℝ 1
            (fun _ : Fin n → ℝ => (Pi.single j (1 : ℝ) : Fin n → ℝ)) x))
    refine (hcoordC1.differentiableAt one_ne_zero).hasFDerivAt.congr_fderiv ?_
    ext v
    -- Express the scalar derivative via the basis, then rewrite it as matrix multiplication.
    change _ = (Matrix.toLin' hessf v) j
    rw [posDef_matrix_toLin'_apply_eq_sum hessf_pos]
    simpa [hessf] using continuousLinearMap_apply_eq_sum_piSingle
      (fderiv ℝ (fun z : Fin n → ℝ => (fderiv ℝ f z) (Pi.single j (1 : ℝ))) x) v
  -- The coordinate derivatives reassemble to the full derivative of the vector-valued map.
  refine hpi.congr_fderiv ?_
  ext v j
  rfl

/-
Let f: ℝ^n → ℝ be a convex C^2 function, and let f*: ℝ^n → ℝ + ∞ be its convex conjugate defined by
f*(y) = sup_{z∈ℝ^n}(yᵀz - f(z)). Assume that x, y∈ℝ^n satisfy y = ∇ f(x) and that ∇^2 f(x)succ 0.
Show
that f* is twice differentiable at y and that ∇^2 f*(y) = (∇^2 f(x))^{- 1}.
-/
theorem hessian_convexConjugate_eq_inverse_hessian_at_gradient
    {n : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (fStar : (Fin n → ℝ) → ℝ)
    (x y : Fin n → ℝ)
    (hy :
      y = fun i =>
        (fderiv ℝ f x) (Pi.single i (1 : ℝ)))
    (hconv : ConvexOn ℝ Set.univ f)
    (hC2 : ContDiffAt ℝ 2 f x)
    (hstar : ∀ z, convexConjugate (fun w => (f w : EReal)) z = (fStar z : EReal))
    (hpos :
      let hessf : Matrix (Fin n) (Fin n) ℝ :=
        fun i j =>
          (fderiv ℝ
            (fun x' => (fderiv ℝ f x') (Pi.single j (1 : ℝ))) x)
            (Pi.single i (1 : ℝ))
      hessf.PosDef) :
    let hessf : Matrix (Fin n) (Fin n) ℝ :=
      fun i j =>
        (fderiv ℝ
          (fun x' => (fderiv ℝ f x') (Pi.single j (1 : ℝ))) x)
          (Pi.single i (1 : ℝ))
    let hessfstar : Matrix (Fin n) (Fin n) ℝ :=
      fun i j =>
        (fderiv ℝ
          (fun y' =>
            (fderiv ℝ fStar y')
              (Pi.single j (1 : ℝ))) y)
          (Pi.single i (1 : ℝ))
    ContDiffAt ℝ 2 fStar y ∧ hessfstar = hessf⁻¹ := by
  -- Package the coordinate gradient map and both Hessian matrices exactly as they appear
  -- in the statement, so the remaining local inverse and conjugate computations are explicit.
  let gradF : (Fin n → ℝ) → (Fin n → ℝ) :=
    fun z i => (fderiv ℝ f z) (Pi.single i (1 : ℝ))
  let hessf : Matrix (Fin n) (Fin n) ℝ :=
    fun i j =>
      (fderiv ℝ
        (fun x' => (fderiv ℝ f x') (Pi.single j (1 : ℝ))) x)
        (Pi.single i (1 : ℝ))
  let hessfstar : Matrix (Fin n) (Fin n) ℝ :=
    fun i j =>
      (fderiv ℝ
        (fun y' =>
          (fderiv ℝ fStar y')
            (Pi.single j (1 : ℝ))) y)
        (Pi.single i (1 : ℝ))
  -- Rewrite the gradient hypothesis in terms of the packaged coordinate-gradient map.
  have hy_grad : y = gradF x := by
    simpa [gradF] using hy
  -- The positivity hypothesis already gives the Hessian matrix an inverse, which is the linear
  -- algebra input needed for the inverse-function step.
  have hessf_pos : hessf.PosDef := by
    simpa [hessf] using hpos
  have hessf_unit : IsUnit hessf := hessf_pos.isUnit
  -- The local inverse theorem needs the derivative of the coordinate-gradient map explicitly.
  have hgradF_C1 : ContDiffAt ℝ 1 gradF x := by
    -- Each coordinate is obtained by evaluating the derivative field on a fixed basis vector.
    rw [contDiffAt_pi]
    intro j
    exact (hC2.fderiv_right_succ.clm_apply
      (contDiffAt_const :
        ContDiffAt ℝ 1
          (fun _ : Fin n → ℝ => (Pi.single j (1 : ℝ) : Fin n → ℝ)) x))
  have hgradF :
      HasFDerivAt gradF
        (LinearMap.toContinuousLinearMap (Matrix.toLin' hessf)) x := by
    -- Route correction: the raw coordinate Jacobian is index-swapped, so we first use
    -- positive-definite symmetry to identify it with `Matrix.toLin' hessf`.
    simpa [gradF, hessf] using gradF_hasFDerivAt_at_x hC2 hpos
  let hessfEquiv : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
    (Matrix.toLinearEquiv' hessf hessf_unit.invertible).toContinuousLinearEquiv
  have hgradF_equiv : HasFDerivAt gradF (hessfEquiv : _ →L[ℝ] _) x := by
    simpa [hessfEquiv, Matrix.toLinearEquiv'_apply, hessf] using hgradF
  let g : (Fin n → ℝ) → (Fin n → ℝ) := hgradF_C1.localInverse hgradF_equiv one_ne_zero
  have hg_at_y : g y = x := by
    -- The inverse sends the gradient value back to the base point.
    simpa [g, hy_grad] using hgradF_C1.localInverse_apply_image hgradF_equiv one_ne_zero
  have hg_C1 : ContDiffAt ℝ 1 g y := by
    -- The local inverse inherits the same `C^1` regularity at the image point.
    simpa [g, hy_grad] using hgradF_C1.to_localInverse hgradF_equiv one_ne_zero
  have hg_deriv : HasFDerivAt g (hessfEquiv.symm : _ →L[ℝ] _) y := by
    -- The inverse-function theorem identifies the derivative of `g` with `hessf⁻¹`.
    have hstrict := (hgradF_C1.hasStrictFDerivAt' hgradF_equiv one_ne_zero).to_localInverse
    simpa [g, hy_grad] using hstrict.hasFDerivAt
  have hg_rightInv : ∀ᶠ u in 𝓝 y, gradF (g u) = u := by
    -- Near `y`, the local inverse really is a right inverse to the gradient map.
    simpa [g, hy_grad] using
      (hgradF_C1.hasStrictFDerivAt' hgradF_equiv one_ne_zero).eventually_right_inverse
  -- The `C²` hypothesis already gives differentiability at `x`, so we can evaluate the
  -- conjugate exactly at the gradient point from the statement.
  have hx_diff : DifferentiableAt ℝ f x := hC2.differentiableAt (by norm_num)
  have hstar_at_y : (fStar y : EReal) = (((∑ i, y i * x i : ℝ) - f x : ℝ) : EReal) := by
    -- Match the theorem's coordinate gradient hypothesis with the helper lemma's derivative data.
    calc
      (fStar y : EReal) = convexConjugate (fun w => (f w : EReal)) y := by
        symm
        exact hstar y
      _ = (((∑ i, y i * x i : ℝ) - f x : ℝ) : EReal) := by
        refine convexConjugate_eq_of_coordinate_derivative hconv hx_diff ?_
        intro i
        simpa [gradF] using congrArg (fun v : Fin n → ℝ => v i) hy_grad
  -- Route correction: the convex-conjugate identification at the base point is now proved.
  -- The local inverse of `gradF` is now in place with its derivative and right-inverse properties.
  -- The remaining step is local: build one open neighborhood on which the Legendre formula and
  -- its differentiated form both hold, so `contDiffAt_succ_iff_hasFDerivAt` can be applied directly.
  have hC2_near_x : ∀ᶠ z in 𝓝 x, ContDiffAt ℝ 2 f z := hC2.eventually (by norm_num)
  have hg_tendsto : Tendsto g (𝓝 y) (𝓝 x) := by
    simpa [hg_at_y] using hg_C1.continuousAt.tendsto
  have hC2_near_y : ∀ᶠ u in 𝓝 y, ContDiffAt ℝ 2 f (g u) :=
    hg_tendsto.eventually hC2_near_x
  have hg_C1_near_y : ∀ᶠ u in 𝓝 y, ContDiffAt ℝ 1 g u := hg_C1.eventually (by norm_num)
  have hgood :
      {u | gradF (g u) = u ∧ ContDiffAt ℝ 2 f (g u) ∧ ContDiffAt ℝ 1 g u} ∈ 𝓝 y := by
    filter_upwards [hg_rightInv, hC2_near_y, hg_C1_near_y] with u hright hfu hgu
    exact ⟨hright, hfu, hgu⟩
  obtain ⟨s, hs_subset, hs_open, hy_mem_s⟩ := mem_nhds_iff.mp hgood
  have hs_nhds : s ∈ 𝓝 y := hs_open.mem_nhds hy_mem_s
  have hs_good :
      ∀ u ∈ s, gradF (g u) = u ∧ ContDiffAt ℝ 2 f (g u) ∧ ContDiffAt ℝ 1 g u := by
    intro u hu
    exact hs_subset hu
  let proj : Fin n → (Fin n → ℝ) →L[ℝ] ℝ :=
    fun i => ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ : Fin n => ℝ) i
  let legendreLocal : (Fin n → ℝ) → ℝ :=
    fun u => (∑ i, u i * g u i : ℝ) - f (g u)
  let derivField : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] ℝ) :=
    fun u => Finset.univ.sum fun i : Fin n => g u i • proj i
  have hs_formula : ∀ u ∈ s, fStar u = legendreLocal u := by
    intro u hu
    rcases hs_good u hu with ⟨hgrad_u, hC2_u, _⟩
    -- The conjugate is attained at `g u` because the local inverse identifies the gradient there
    -- with the dual variable `u`.
    have hdiff_u : DifferentiableAt ℝ f (g u) := hC2_u.differentiableAt (by norm_num)
    have hcoord_u : ∀ i, u i = (fderiv ℝ f (g u)) (Pi.single i (1 : ℝ)) := by
      intro i
      simpa [gradF] using (congrArg (fun v : Fin n → ℝ => v i) hgrad_u).symm
    have hconj :
        (fStar u : EReal) = (((∑ i, u i * g u i : ℝ) - f (g u) : ℝ) : EReal) := by
      calc
        (fStar u : EReal) = convexConjugate (fun w => (f w : EReal)) u := by
          symm
          exact hstar u
        _ = (((∑ i, u i * g u i : ℝ) - f (g u) : ℝ) : EReal) := by
          refine convexConjugate_eq_of_coordinate_derivative hconv hdiff_u ?_
          intro i
          exact hcoord_u i
    change fStar u = ((∑ i, u i * g u i : ℝ) - f (g u))
    exact_mod_cast hconj
  have hs_legendre_hasFDeriv : ∀ u ∈ s, HasFDerivAt legendreLocal (derivField u) u := by
    intro u hu
    rcases hs_good u hu with ⟨hgrad_u, hC2_u, hgC1_u⟩
    -- Differentiate the local Legendre formula pointwise and rewrite the derivative of `f`
    -- using `gradF (g u) = u`, so the chain-rule terms cancel.
    have hdiff_u : DifferentiableAt ℝ f (g u) := hC2_u.differentiableAt (by norm_num)
    let Dg : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := fderiv ℝ g u
    have hgu : HasFDerivAt g (fderiv ℝ g u) u :=
      (hgC1_u.differentiableAt one_ne_zero).hasFDerivAt
    have hfLinear :
        fderiv ℝ f (g u) = Finset.univ.sum (fun i : Fin n => u i • proj i) := by
      ext v
      rw [continuousLinearMap_apply_eq_sum_piSingle]
      have hcoord_u : ∀ i, (fderiv ℝ f (g u)) (Pi.single i (1 : ℝ)) = u i := by
        intro i
        simpa [gradF] using congrArg (fun v : Fin n → ℝ => v i) hgrad_u
      simp [hcoord_u, proj, mul_comm]
    have hfu :
        HasFDerivAt f (Finset.univ.sum (fun i : Fin n => u i • proj i)) (g u) := by
      exact hdiff_u.hasFDerivAt.congr_fderiv hfLinear
    have hsum :
        HasFDerivAt
          (fun w => (∑ i : Fin n, w i * g w i : ℝ))
          (Finset.univ.sum fun i : Fin n =>
            u i • (proj i).comp Dg + g u i • proj i) u := by
      have hcoord :
          ∀ i : Fin n,
            HasFDerivAt
              (fun w => w i * g w i)
              (u i • (proj i).comp Dg + g u i • proj i) u := by
        intro i
        simpa [Dg, proj] using ((proj i).hasFDerivAt.mul ((proj i).hasFDerivAt.comp u hgu))
      exact
        (HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n))) (fun i _ => hcoord i))
    have hcomp_linear :
        ((Finset.univ.sum fun i : Fin n => u i • proj i).comp Dg)
          = Finset.univ.sum fun i : Fin n => u i • (proj i).comp Dg := by
      ext v
      simp
    have hcomp :
        HasFDerivAt
          (fun w => f (g w))
          (Finset.univ.sum fun i : Fin n => u i • (proj i).comp Dg) u := by
      exact (hfu.comp u hgu).congr_fderiv hcomp_linear
    have hderiv_eq :
        (Finset.univ.sum fun i : Fin n =>
            u i • (proj i).comp Dg + g u i • proj i)
          - (Finset.univ.sum fun i : Fin n => u i • (proj i).comp Dg)
          = derivField u := by
      ext v
      simp [Dg, derivField, sub_eq_add_neg, Finset.sum_add_distrib]
    have hraw :
        HasFDerivAt
          (fun w => ((∑ i : Fin n, w i * g w i : ℝ) - f (g w)))
          ((Finset.univ.sum fun i : Fin n =>
              u i • (proj i).comp Dg + g u i • proj i)
            - Finset.univ.sum fun i : Fin n => u i • (proj i).comp Dg) u :=
      hsum.sub hcomp
    simpa [legendreLocal, derivField] using hraw.congr_fderiv hderiv_eq
  have hs_fStar_hasFDeriv : ∀ u ∈ s, HasFDerivAt fStar (derivField u) u := by
    intro u hu
    -- Since the Legendre formula holds on the open neighborhood `s`, we can transfer its
    -- derivative to `fStar` at every point of `s`.
    have hs_mem_u : s ∈ 𝓝 u := hs_open.mem_nhds hu
    have hEq_u : (fun z => fStar z) =ᶠ[𝓝 u] legendreLocal := by
      filter_upwards [hs_mem_u] with z hz
      exact hs_formula z hz
    exact (hs_legendre_hasFDeriv u hu).congr_of_eventuallyEq hEq_u
  have hg_coord_C1 : ∀ i : Fin n, ContDiffAt ℝ 1 (fun u => g u i) y := by
    rw [contDiffAt_pi] at hg_C1
    simpa using hg_C1
  have hderivField_C1 : ContDiffAt ℝ 1 derivField y := by
    -- The derivative field is built from the `C¹` local inverse coordinates and fixed projections.
    simpa [derivField] using
      (ContDiffAt.sum (s := (Finset.univ : Finset (Fin n)))
        (fun i _ => ContDiffAt.smul_const (hg_coord_C1 i) (proj i)))
  have hC2_fStar : ContDiffAt ℝ 2 fStar y := by
    -- The explicit neighborhood witness `s` now fits exactly into the `C²` characterization.
    simpa using
      (contDiffAt_succ_iff_hasFDerivAt (n := 1)).2
        ⟨derivField, ⟨s, hs_nhds, hs_fStar_hasFDeriv⟩, hderivField_C1⟩
  let coordStar : Fin n → ((Fin n → ℝ) → ℝ) :=
    fun j u => (fderiv ℝ fStar u) (Pi.single j (1 : ℝ))
  have hderivField_apply : ∀ u j, derivField u (Pi.single j (1 : ℝ)) = g u j := by
    intro u j
    -- Evaluating the derivative field on a basis vector recovers the corresponding coordinate.
    simp only [derivField, ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_smul',
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    classical
    rw [Finset.sum_eq_single j]
    · simp [proj]
    · intro i _ hij
      have hzero : (proj i) (Pi.single j (1 : ℝ)) = 0 := by
        simp [proj, hij]
      simp [hzero]
    · simp [proj]
  have hs_coord_eq : ∀ j : Fin n, coordStar j =ᶠ[𝓝 y] fun u => g u j := by
    intro j
    filter_upwards [hs_nhds] with u hu
    change (fderiv ℝ fStar u) (Pi.single j (1 : ℝ)) = g u j
    rw [(hs_fStar_hasFDeriv u hu).fderiv]
    exact hderivField_apply u j
  have hcoordStar_C1 : ∀ j : Fin n, ContDiffAt ℝ 1 (coordStar j) y := by
    intro j
    -- The coordinate derivatives of `fStar` inherit `C¹` regularity from `ContDiffAt ℝ 2 fStar y`.
    exact hC2_fStar.fderiv_right_succ.clm_apply
      (contDiffAt_const :
        ContDiffAt ℝ 1 (fun _ : Fin n → ℝ => (Pi.single j (1 : ℝ) : Fin n → ℝ)) y)
  have hg_coord_deriv :
      ∀ j : Fin n,
        HasFDerivAt (fun u => g u j) ((proj j).comp (hessfEquiv.symm : _ →L[ℝ] _)) y := by
    intro j
    -- Differentiate the `j`th coordinate of the local inverse using the inverse-function theorem.
    simpa [proj] using ((proj j).hasFDerivAt.comp y hg_deriv)
  have hessf_inv_symm : (hessf⁻¹).IsSymm := (posDef_isSymm_real hessf_pos).inv
  have hhess : hessfstar = hessf⁻¹ := by
    ext i j
    -- The coordinate derivative field of `fStar` agrees near `y` with the corresponding
    -- coordinate of `g`, so uniqueness of derivatives identifies the Hessian entries.
    have hcoord_eqj :
        fderiv ℝ (coordStar j) y = (proj j).comp (hessfEquiv.symm : _ →L[ℝ] _) := by
      have hcoord_deriv :
          HasFDerivAt (coordStar j) (fderiv ℝ (coordStar j) y) y :=
        (hcoordStar_C1 j).differentiableAt one_ne_zero |>.hasFDerivAt
      have hcoord_as_g : HasFDerivAt (fun u => g u j) (fderiv ℝ (coordStar j) y) y :=
        hcoord_deriv.congr_of_eventuallyEq (hs_coord_eq j).symm
      exact hcoord_as_g.unique (hg_coord_deriv j)
    calc
      hessfstar i j = (fderiv ℝ (coordStar j) y) (Pi.single i (1 : ℝ)) := by
        rfl
      _ = ((proj j).comp (hessfEquiv.symm : _ →L[ℝ] _)) (Pi.single i (1 : ℝ)) := by
        exact congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single i (1 : ℝ))) hcoord_eqj
      _ = (hessf⁻¹) j i := by
        have hlin :
            (((hessfEquiv.toLinearEquiv).symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) = Matrix.toLin' hessf⁻¹ := by
          simpa [hessfEquiv] using Matrix.toLinearEquiv'_symm_apply hessf hessf_unit.invertible
        change (((hessfEquiv.toLinearEquiv).symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
            (Pi.single i (1 : ℝ))) j = (hessf⁻¹) j i
        rw [hlin]
        simp [Matrix.toLin'_apply]
      _ = (hessf⁻¹) i j := by
        rw [Matrix.IsSymm.apply hessf_inv_symm j i]
  simpa [hessf, hessfstar] using ⟨hC2_fStar, hhess⟩

end «problem-41»
