import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-44»
/-
Let f: ℝ^n → ℝ be a twice continuously differentiable convex function. Assume that ∇^2 f(x) succ 0
for every x ∈ ℝ^n. For x ∈ ℝ^n, define λ(x)^2 = ∇ f(x)ᵀbig(∇^2 f(x)big)^{- 1}∇ f(x). Suppose there
exists a constant c > 0 such that λ(x)^2 ≤ c for all x ∈ ℝ^n. Show that the function g(x) =
exp(- (f(x))/(c)) is concave on ℝ^n.
-/
open scoped BigOperators Matrix
theorem exp_neg_div_convex_is_concave
    {n : ℕ} (hn : 0 < n) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf₂ : ContDiff ℝ 2 f)
    (hconv : ConvexOn ℝ Set.univ f)
    (hpd :
      ∀ x : EuclideanSpace ℝ (Fin n),
        ∃ hess_inv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
          (∀ v w : EuclideanSpace ℝ (Fin n),
            ((fderiv ℝ (fun y => fderiv ℝ f y) x) v) (hess_inv w) = inner ℝ v w) ∧
          (∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 →
            0 < ((fderiv ℝ (fun y => fderiv ℝ f y) x) v) v))
    (c : ℝ) (hc : 0 < c)
    (hlambda :
      ∀ x : EuclideanSpace ℝ (Fin n),
        ∃ hess_inv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
          (∀ v w : EuclideanSpace ℝ (Fin n),
            ((fderiv ℝ (fun y => fderiv ℝ f y) x) v) (hess_inv w) = inner ℝ v w) ∧
          let gradx :=
            (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f x)
          inner ℝ gradx (hess_inv gradx) ≤ c)
    : ConcaveOn ℝ Set.univ (fun x => Real.exp (-f x / c)) := by
  let _ : 0 < n := hn
  let _ : ConvexOn ℝ Set.univ f := hconv
  -- Route correction: instead of attempting a global multivariate concavity proof directly,
  -- restrict to each affine line and use the one-dimensional second-derivative criterion.
  have hdir :
      ∀ z d : EuclideanSpace ℝ (Fin n),
        (fderiv ℝ f z d) ^ 2 ≤ c * ((fderiv ℝ (fun y => fderiv ℝ f y) z) d) d := by
    intro z d
    let H : LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin n)) :=
      { toFun := fun v =>
          { toFun := fun w => ((fderiv ℝ (fun y => fderiv ℝ f y) z) v) w
            map_add' := by
              intro w₁ w₂
              exact map_add ((fderiv ℝ (fun y => fderiv ℝ f y) z) v) w₁ w₂
            map_smul' := by
              intro a w
              exact map_smul ((fderiv ℝ (fun y => fderiv ℝ f y) z) v) a w }
        map_add' := by
          intro v₁ v₂
          ext w
          exact congrArg (fun T => T w) (map_add (fderiv ℝ (fun y => fderiv ℝ f y) z) v₁ v₂)
        map_smul' := by
          intro a v
          ext w
          exact congrArg (fun T => T w) (map_smul (fderiv ℝ (fun y => fderiv ℝ f y) z) a v) }
    -- The Hessian is symmetric because `f` is `C²`.
    have hHsymm : LinearMap.IsSymm H := by
      refine ⟨fun v w => ?_⟩
      simpa [H] using
        (hf₂.contDiffAt (x := z)).isSymmSndFDerivAt
          (by norm_num : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞)) v w
    rcases hpd z with ⟨_, _, hpd_pos⟩
    -- Positive definiteness gives the nonnegativity needed for Cauchy-Schwarz.
    have hHnonneg : ∀ v : EuclideanSpace ℝ (Fin n), 0 ≤ H v v := by
      intro v
      by_cases hv : v = 0
      · simp [H, hv]
      · exact le_of_lt (hpd_pos v hv)
    rcases hlambda z with ⟨hess_inv, hess_inv_spec, h_lambda⟩
    let gradz :=
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f z)
    have hgrad_eval : inner ℝ gradz d = fderiv ℝ f z d := by
      change
        inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f z)) d =
          fderiv ℝ f z d
      exact
        (InnerProductSpace.toDual_symm_apply
          (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n))
          (x := d) (y := fderiv ℝ f z))
    have hpair :
        H d (hess_inv gradz) = fderiv ℝ f z d := by
      calc
        H d (hess_inv gradz) = inner ℝ d gradz := hess_inv_spec d gradz
        _ = inner ℝ gradz d := by rw [real_inner_comm]
        _ = fderiv ℝ f z d := hgrad_eval
    have hbound :
        H (hess_inv gradz) (hess_inv gradz) ≤ c := by
      calc
        H (hess_inv gradz) (hess_inv gradz) = inner ℝ (hess_inv gradz) gradz := by
          simpa [H] using hess_inv_spec (hess_inv gradz) gradz
        _ = inner ℝ gradz (hess_inv gradz) := by rw [real_inner_comm]
        _ ≤ c := by simpa [gradz] using h_lambda
    -- Apply bilinear-form Cauchy-Schwarz with the inverse-Hessian image of the gradient.
    have hcs := H.apply_sq_le_of_symm hHnonneg hHsymm d (hess_inv gradz)
    have hcs' :
        (fderiv ℝ f z d) ^ 2 ≤ H d d * H (hess_inv gradz) (hess_inv gradz) := by
      simpa [hpair] using hcs
    have hmul :
        H d d * H (hess_inv gradz) (hess_inv gradz) ≤ H d d * c :=
      mul_le_mul_of_nonneg_left hbound (hHnonneg d)
    exact le_trans hcs' (by simpa [H, mul_comm, mul_left_comm, mul_assoc] using hmul)
  rw [concaveOn_iff_pairwise_pos]
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ _ a b ha hb hab
  let γ : ℝ → EuclideanSpace ℝ (Fin n) := AffineMap.lineMap x y
  let d : EuclideanSpace ℝ (Fin n) := y - x
  let u : ℝ → ℝ := fun t => f (γ t)
  let u' : ℝ → ℝ := fun t => fderiv ℝ f (γ t) d
  let u'' : ℝ → ℝ := fun t => ((fderiv ℝ (fun z => fderiv ℝ f z d) (γ t)) d)
  let ψ : ℝ → ℝ := fun t => Real.exp (-u t / c)
  let ψ' : ℝ → ℝ := fun t => (-u' t / c) * ψ t
  let ψ'' : ℝ → ℝ := fun t => ((-u'' t / c) + (-u' t / c) ^ 2) * ψ t
  have hγ : ∀ t : ℝ, HasDerivAt γ d t := by
    intro t
    simpa [γ, d] using (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t))
  have hfderiv_apply :
      ContDiff ℝ 1 (fun z : EuclideanSpace ℝ (Fin n) => fderiv ℝ f z d) := by
    -- The directional derivative of a `C²` function is `C¹`.
    exact (hf₂.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hu : ∀ t : ℝ, HasDerivAt u (u' t) t := by
    intro t
    -- Differentiate the line restriction by the chain rule.
    exact
      ((((hf₂.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffAt (x := γ t)).differentiableAt_one).hasFDerivAt).comp_hasDerivAt
        t (hγ t)
  have hu' : ∀ t : ℝ, HasDerivAt u' (u'' t) t := by
    intro t
    -- Differentiate the directional derivative along the same line once more.
    have hout :
        HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => fderiv ℝ f z d)
          (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => fderiv ℝ f z d) (γ t)) (γ t) :=
      (((hfderiv_apply.contDiffAt (x := γ t)).differentiableAt_one).hasFDerivAt)
    exact hout.comp_hasDerivAt t (hγ t)
  have hψ : ∀ t : ℝ, HasDerivAt ψ (ψ' t) t := by
    intro t
    -- The exponential transform inherits its first derivative from the chain rule.
    simpa [ψ, ψ', u, mul_comm] using ((hu t).neg.div_const c).exp
  have hψ' : ∀ t : ℝ, HasDerivAt ψ' (ψ'' t) t := by
    intro t
    -- Differentiate the explicit first derivative and simplify the product-rule expansion.
    have hleft : HasDerivAt (fun s => -u' s / c) (-u'' t / c) t := (hu' t).neg.div_const c
    have hright : HasDerivAt ψ (((-u' t / c) * ψ t)) t := hψ t
    refine HasDerivAt.congr_deriv (hleft.mul hright) ?_
    ring
  have hψ''_nonpos : ∀ t : ℝ, ψ'' t ≤ 0 := by
    intro t
    have hdir_t : (u' t) ^ 2 ≤ c * ((fderiv ℝ (fun y => fderiv ℝ f y) (γ t)) d) d := by
      simpa [u', γ, d] using hdir (γ t) d
    have hu''_rewrite :
        u'' t = ((fderiv ℝ (fun y => fderiv ℝ f y) (γ t)) d) d := by
      -- Applying the derivative of `fderiv f` to a fixed vector is evaluation on that vector.
      have h_eval :
          fderiv ℝ (fun z => fderiv ℝ f z d) (γ t) =
            (fderiv ℝ (fun z => fderiv ℝ f z) (γ t)).flip d := by
        simpa using
          fderiv_clm_apply
            (c := fun z : EuclideanSpace ℝ (Fin n) => fderiv ℝ f z)
            (u := fun _ : EuclideanSpace ℝ (Fin n) => d)
            ((((hf₂.fderiv_right (m := 1) (by norm_num)).contDiffAt (x := γ t)).differentiableAt_one))
            (differentiableAt_const d)
      calc
        u'' t = (fderiv ℝ (fun z => fderiv ℝ f z d) (γ t)) d := rfl
        _ = ((fderiv ℝ (fun z => fderiv ℝ f z) (γ t)).flip d) d := by rw [h_eval]
        _ = ((fderiv ℝ (fun z => fderiv ℝ f z) (γ t)) d) d := by
          simp [ContinuousLinearMap.flip_apply]
    have hcoeff :
        (-u'' t / c) + (-u' t / c) ^ 2 ≤ 0 := by
      rw [hu''_rewrite]
      have hnum : (u' t) ^ 2 - c * ((fderiv ℝ (fun y => fderiv ℝ f y) (γ t)) d) d ≤ 0 := by
        nlinarith [hdir_t]
      have hcoeff_eq :
          (-((fderiv ℝ (fun y => fderiv ℝ f y) (γ t)) d) d / c) + (-u' t / c) ^ 2 =
            ((u' t) ^ 2 - c * ((fderiv ℝ (fun y => fderiv ℝ f y) (γ t)) d) d) / c ^ 2 := by
        field_simp [hc.ne']
        ring
      rw [hcoeff_eq]
      exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
    have hψ_nonneg : 0 ≤ ψ t := by
      positivity
    exact mul_nonpos_of_nonpos_of_nonneg hcoeff hψ_nonneg
  have hconc_line : ConcaveOn ℝ Set.univ ψ := by
    -- The line restriction is concave because its second derivative is nonpositive everywhere.
    refine concaveOn_of_hasDerivWithinAt2_nonpos (f' := ψ') (f'' := ψ'') convex_univ ?_ ?_ ?_ ?_
    · intro t _
      exact (hψ t).continuousAt.continuousWithinAt
    · intro t _
      exact (hψ t).hasDerivWithinAt
    · intro t _
      exact (hψ' t).hasDerivWithinAt
    · intro t _
      exact hψ''_nonpos t
  have hline := hconc_line.2 (x := 0) (by simp) (y := 1) (by simp) ha.le hb.le (by simp [hab])
  -- Evaluate the concavity inequality on the endpoints `0` and `1` of the line segment.
  have h_one_sub : 1 - b = a := by linarith
  simpa [ψ, u, γ, AffineMap.lineMap_apply_module, h_one_sub, smul_eq_mul, mul_comm, mul_left_comm,
    mul_assoc] using hline

end «problem-44»
