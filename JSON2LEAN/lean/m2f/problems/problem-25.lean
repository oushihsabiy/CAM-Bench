import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-25»
/-
A function f: ℝ^n → ℝ is called convex and twice continuously differentiable if it is convex and
belongs to C^2(ℝ^n), that is, all second - order partial derivatives of f exist and are continuous
on
ℝ^n.
-/
def IsConvexC2Function {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → ℝ) : Prop :=
  ConvexOn ℝ (Set.univ : Set E) f ∧ ContDiff ℝ 2 f

/-
The convex conjugate of a function f: ℝ^n → ℝ cup {+ ∞} is the function f*: ℝ^n → ℝ cup {+ ∞}
defined
by f*(y) = sup_{z ∈ ℝ^n} (yᵀ z - f(z)).
-/
def convexConjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → EReal) : E → EReal :=
  fun y => sSup (Set.range fun z : E => (⟪y, z⟫ : ℝ) - f z)

/-
A function g: ℝ^n → ℝ is differentiable at y ∈ ℝ^n if there exists a vector a ∈ ℝ^n such that lim_{h
→ 0} (g(y + h) - g(y) - aᵀ h)/(‖h‖) = 0; in this case, a is denoted by ∇ g(y).
-/
def IsDifferentiableAtWithGradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → ℝ) (y a : E) : Prop :=
  HasFDerivAt g ((InnerProductSpace.toDual ℝ E) a) y

/-
Let f: ℝ^n → ℝ be a convex twice continuously differentiable function. Let x ∈ ℝ^n, set y = ∇ f(x),
and assume that the Hessian ∇^2 f(x) is positive definite. Define the convex conjugate f*: ℝ^n → ℝ +
∞
by f*(y) = sup_{z∈ℝ^n}(yᵀ z - f(z)). Show that there is an open neighborhood of y on which f* is
represented by a real-valued function that is differentiable at y with gradient x.
-/
theorem gradient_convexConjugate_at_gradient_eq_point
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → ℝ)
    (x : E)
    (hf : IsConvexC2Function f)
    (hpd : ∀ v : E, v ≠ 0 →
      0 < (fderiv ℝ (fun z : E => fderiv ℝ f z v) x) v)
    (y : E)
    (hy : y = (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)) :
    ∃ s : Set E, IsOpen s ∧ y ∈ s ∧
      ∃ g : E → ℝ,
        (∀ y' : E, y' ∈ s → convexConjugate (fun z : E => (f z : EReal)) y' = (g y' : EReal)) ∧
        IsDifferentiableAtWithGradient g y x := by
  classical
  let G : E → E := ∇ f
  have hyG : y = G x := by
    simpa [G] using hy
  have hfdiff : Differentiable ℝ f := hf.2.differentiable (by norm_num)
  -- The gradient map is `C¹`, so it is differentiable at the base point.
  have hGContDiff : ContDiff ℝ 1 G := by
    simpa [G] using
      (((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv).contDiff.comp
        (hf.2.fderiv_right (m := 1) (by norm_num)))
  have hGDiff : DifferentiableAt ℝ G x := by
    exact (hGContDiff.contDiffAt : ContDiffAt ℝ 1 G x).differentiableAt (by norm_num)
  let A : E →L[ℝ] E := fderiv ℝ G x
  have hsecond :
      ∀ v : E, (fderiv ℝ (fun z : E => fderiv ℝ f z v) x) v = ⟪A v, v⟫ := by
    intro v
    -- The scalar directional derivative agrees with the inner product against the gradient.
    have hinner :
        HasFDerivAt (fun z : E => ⟪G z, v⟫)
          ((fderivInnerCLM ℝ (G x, v)).comp (A.prod 0)) x := by
      simpa [A] using hGDiff.hasFDerivAt.inner ℝ (hasFDerivAt_const v x)
    have hdir :
        HasFDerivAt (fun z : E => fderiv ℝ f z v)
          ((fderivInnerCLM ℝ (G x, v)).comp (A.prod 0)) x := by
      convert hinner using 1
      ext z
      simpa [G] using (inner_gradient_left (hfdiff z) (y := v)).symm
    have hlin := congrArg (fun L : E →L[ℝ] ℝ => L v) hdir.fderiv
    simpa [fderivInnerCLM_apply, ContinuousLinearMap.comp_apply, real_inner_comm] using hlin
  have hAinj : Function.Injective A := by
    intro v w hvw
    by_contra hne
    have hne0 : v - w ≠ 0 := sub_ne_zero.mpr hne
    have hA0 : A (v - w) = 0 := by
      simp [A, ContinuousLinearMap.map_sub, hvw]
    have hpos := hpd (v - w) hne0
    have hzero :
        (fderiv ℝ (fun z : E => fderiv ℝ f z (v - w)) x) (v - w) = 0 := by
      rw [hsecond (v - w)]
      simp [hA0]
    linarith
  let AequivLin : E ≃ₗ[ℝ] E := LinearEquiv.ofInjectiveEndo A.toLinearMap hAinj
  let Aequiv : E ≃L[ℝ] E := AequivLin.toContinuousLinearEquivOfContinuous A.continuous
  have hGAequiv : HasFDerivAt G (Aequiv : E →L[ℝ] E) x := by
    -- Route correction: package the invertible derivative through the finite-dimensional linear
    -- equivalence before invoking the inverse-function theorem.
    simpa [Aequiv, AequivLin, A, LinearEquiv.coe_ofInjectiveEndo] using hGDiff.hasFDerivAt
  let hGStrict := hGContDiff.contDiffAt.hasStrictFDerivAt' hGAequiv (by norm_num)
  let e : OpenPartialHomeomorph E E := hGStrict.toOpenPartialHomeomorph G
  let φ : E → E := e.symm
  let s : Set E := e.target
  have hsOpen : IsOpen s := e.open_target
  have hyMem : y ∈ s := by
    rw [hyG]
    simpa [e, s] using hGStrict.image_mem_toOpenPartialHomeomorph_target
  have hxMem : x ∈ e.source := by
    simpa [e] using hGStrict.mem_toOpenPartialHomeomorph_source
  have hyφ : φ y = x := by
    change e.symm y = x
    rw [hyG]
    exact e.left_inv hxMem
  have hφright : ∀ y' : E, y' ∈ s → G (φ y') = y' := by
    intro y' hy'
    change e (e.symm y') = y'
    exact e.right_inv hy'
  have hφstrict : HasStrictFDerivAt φ (Aequiv.symm : E →L[ℝ] E) y := by
    -- Route correction: differentiate the inverse through the strict inverse theorem API.
    simpa [φ, hyG, hGStrict.localInverse_def (f := G) (f' := Aequiv) (a := x)] using
      (hGStrict.to_localInverse (f := G) (f' := Aequiv) (a := x))
  have hsupport :
      ∀ p w : E, HasGradientAt f p w →
        ∀ z : E, (⟪p, z⟫ : ℝ) - f z ≤ ⟪p, w⟫ - f w := by
    intro p w hpw z
    let γ : ℝ →ᵃ[ℝ] E := AffineMap.lineMap w z
    let h : ℝ → ℝ := fun t => f (γ t) - ⟪p, γ t⟫
    -- Restrict to the affine line through `w` and `z` to use the 1D convex derivative bound.
    have hconvF : ConvexOn ℝ (Set.univ : Set ℝ) (fun t : ℝ => f (γ t)) := by
      simpa [γ] using (hf.1.comp_affineMap γ)
    have hlinConc : ConcaveOn ℝ (Set.univ : Set E) (fun u : E => ⟪p, u⟫) := by
      simpa using
        ((concaveOn_id (𝕜 := ℝ) (s := (Set.univ : Set ℝ)) convex_univ).comp_linearMap
          (((InnerProductSpace.toDual ℝ E) p).toLinearMap))
    have hconvH : ConvexOn ℝ (Set.univ : Set ℝ) h := by
      simpa [h, sub_eq_add_neg, γ] using hconvF.add (hlinConc.comp_affineMap γ).neg
    have hγ : HasDerivAt γ (z - w) 0 := by
      simpa [γ] using (AffineMap.hasDerivAt_lineMap (a := w) (b := z) (x := (0 : ℝ)))
    have hcomp :
        HasDerivAt (fun t : ℝ => f (γ t)) (((InnerProductSpace.toDual ℝ E) p) (z - w)) 0 := by
      have hpw' : HasFDerivAt f ((InnerProductSpace.toDual ℝ E) p) w := hpw.hasFDerivAt
      have := HasFDerivAt.comp_hasDerivAt_of_eq
        (x := (0 : ℝ)) (y := w) (f := γ) hpw' hγ (by simp [γ])
      simpa [γ, AffineMap.lineMap_apply_zero] using this
    have hlin :
        HasDerivAt (fun t : ℝ => ⟪p, γ t⟫) (((InnerProductSpace.toDual ℝ E) p) (z - w)) 0 := by
      have := HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) (f := γ)
        (((InnerProductSpace.toDual ℝ E) p).hasFDerivAt) hγ
      simpa [γ] using this
    have hhderiv : HasDerivAt h 0 0 := by
      have hpdir : ((InnerProductSpace.toDual ℝ E) p) (z - w) = fderiv ℝ f w (z - w) := by
        simpa using (hpw.fderiv_apply (y := z - w)).symm
      have := hcomp.sub hlin
      simpa [h, hpdir] using this
    have hslope : (0 : ℝ) ≤ slope h 0 1 := by
      exact hconvH.le_slope_of_hasDerivAt (by simp) (by simp) zero_lt_one hhderiv
    have h01 : h 0 ≤ h 1 := by
      have hslope' : 0 ≤ h 1 - h 0 := by
        simpa [slope, h] using hslope
      linarith
    have h01' : f w - ⟪p, w⟫ ≤ f z - ⟪p, z⟫ := by
      simpa [h, γ, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using h01
    have : (⟪p, z⟫ : ℝ) - f z ≤ ⟪p, w⟫ - f w := by
      linarith
    exact this
  refine ⟨s, hsOpen, hyMem, ?_⟩
  refine ⟨fun y' => ⟪y', φ y'⟫ - f (φ y'), ?_, ?_⟩
  · intro y' hy'
    let w := φ y'
    have hwGrad : HasGradientAt f y' w := by
      have hbase : HasGradientAt f (G w) w := (hfdiff w).hasGradientAt
      simpa [w, hφright y' hy'] using hbase
    have hsup :
        ∀ z : E, (⟪y', z⟫ : ℝ) - f z ≤ ⟪y', w⟫ - f w :=
      hsupport y' w hwGrad
    have hub :
        convexConjugate (fun z : E => (f z : EReal)) y' ≤
          ((⟪y', w⟫ - f w : ℝ) : EReal) := by
      unfold convexConjugate
      apply sSup_le
      rintro _ ⟨z, rfl⟩
      have hz : (⟪y', z⟫ : ℝ) - f z ≤ ⟪y', w⟫ - f w := hsup z
      change ((⟪y', z⟫ : EReal) - (f z : EReal)) ≤ (((⟪y', w⟫ - f w : ℝ) : EReal))
      exact_mod_cast hz
    have hlb :
        (((⟪y', w⟫ - f w : ℝ) : EReal)) ≤
          convexConjugate (fun z : E => (f z : EReal)) y' := by
      unfold convexConjugate
      apply le_sSup
      refine ⟨w, ?_⟩
      simp
    refine le_antisymm hub ?_
    simpa [w] using hlb
  · -- Differentiate the explicit local formula and cancel the inverse-map contribution.
    have hId : HasFDerivAt (fun y' : E => y') (1 : E →L[ℝ] E) y := by
      simpa using (hasFDerivAt_id y)
    have hInner :
        HasFDerivAt (fun y' : E => ⟪y', φ y'⟫)
          ((fderivInnerCLM ℝ (y, x)).comp ((1 : E →L[ℝ] E).prod (Aequiv.symm))) y := by
      simpa [hyφ] using hId.inner ℝ hφstrict.hasFDerivAt
    have hyGrad : HasGradientAt f y x := by
      rw [hyG]
      exact (hfdiff x).hasGradientAt
    have hComp :
        HasFDerivAt (fun y' : E => f (φ y'))
          (((InnerProductSpace.toDual ℝ E) y).comp (Aequiv.symm : E →L[ℝ] E)) y := by
      have hyGrad' : HasFDerivAt f ((InnerProductSpace.toDual ℝ E) y) (φ y) := by
        rw [hyφ]
        exact hyGrad.hasFDerivAt
      exact hyGrad'.comp y hφstrict.hasFDerivAt
    have hModel :
        HasFDerivAt (fun y' : E => ⟪y', φ y'⟫ - f (φ y'))
          (((fderivInnerCLM ℝ (y, x)).comp ((1 : E →L[ℝ] E).prod (Aequiv.symm))) -
            (((InnerProductSpace.toDual ℝ E) y).comp (Aequiv.symm : E →L[ℝ] E))) y := by
      simpa [hyφ] using hInner.sub hComp
    have hCancel :
        ((fderivInnerCLM ℝ (y, x)).comp ((1 : E →L[ℝ] E).prod (Aequiv.symm))) -
            (((InnerProductSpace.toDual ℝ E) y).comp (Aequiv.symm : E →L[ℝ] E)) =
          (InnerProductSpace.toDual ℝ E) x := by
      ext u
      simpa [fderivInnerCLM_apply, ContinuousLinearMap.comp_apply, sub_eq_add_neg] using
        (real_inner_comm x u)
    have hFinal :
        HasFDerivAt (fun y' : E => ⟪y', φ y'⟫ - f (φ y'))
          ((InnerProductSpace.toDual ℝ E) x) y := by
      simpa [hCancel] using hModel
    simpa [IsDifferentiableAtWithGradient, φ] using hFinal


end «problem-25»
