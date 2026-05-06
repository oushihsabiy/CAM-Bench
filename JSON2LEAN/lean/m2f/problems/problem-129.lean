import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-129»
/-
Let D ⊆ ℝ^n be a convex set, and let g: D → ℝ be twice continuously differentiable. Define f: D → ℝ
by f(x) = - exp(- g(x)) (x ∈ D). Assume that for every x ∈ D, [ ∇^2 g(x) & ∇ g(x); ∇ g(x)ᵀ & 1 ]
succeq 0. Prove that f is convex on D.
-/
open scoped RealInnerProductSpace

theorem neg_exp_neg_convexOn_of_posSemidef_hessian_block
    {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hD : Convex ℝ D)
    (hD_open : IsOpen D)
    (hg : ContDiffOn ℝ 2 g D)
    (hblock :
      ∀ x ∈ D, ∀ v : (EuclideanSpace ℝ (Fin n)) × ℝ,
        0 ≤
          let xv : EuclideanSpace ℝ (Fin n) := v.1
          let t : ℝ := v.2
          ⟪fderiv ℝ (fun y => gradient g y) x xv, xv⟫ +
            2 * t * ⟪gradient g x, xv⟫ + t ^ 2)
    :
    ConvexOn ℝ D
      (fun x => -Real.exp (-(g x))) := by
  refine ⟨hD, ?_⟩
  intro x hx y hy a b ha hb hab
  let d : EuclideanSpace ℝ (Fin n) := y - x
  let z : ℝ → EuclideanSpace ℝ (Fin n) := AffineMap.lineMap x y
  let ψ : ℝ → ℝ := fun t => -Real.exp (-(g (z t)))
  let ψ' : ℝ → ℝ := fun t => Real.exp (-(g (z t))) * ⟪gradient g (z t), d⟫
  let ψ'' : ℝ → ℝ :=
    fun t =>
      Real.exp (-(g (z t))) *
        (⟪fderiv ℝ (fun u => gradient g u) (z t) d, d⟫ - ⟪gradient g (z t), d⟫ ^ 2)
  have hz_mem : Set.MapsTo z (Set.Icc (0 : ℝ) 1) D := by
    intro t ht
    exact hD.lineMap_mem hx hy ht
  have hψ_convex : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) ψ := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (D := Set.Icc (0 : ℝ) 1)
      (f := ψ) (f' := ψ') (f'' := ψ'') (convex_Icc (0 : ℝ) 1) ?_ ?_ ?_ ?_
    · -- The segment restriction is continuous because `g` is `C²` on the open domain `D`.
      have hz_cont : Continuous z := by
        simpa [z] using (continuous_const.lineMap continuous_const continuous_id)
      simpa [ψ] using (hg.continuousOn.comp hz_cont.continuousOn hz_mem).neg.rexp.neg
    · intro t ht
      have hzD : z t ∈ D := hz_mem (interior_subset ht)
      have hz_nhds : D ∈ 𝓝 (z t) := hD_open.mem_nhds hzD
      have hC2 : ContDiffAt ℝ 2 g (z t) := hg.contDiffAt hz_nhds
      have hz_deriv : HasDerivAt z d t := by
        simpa [z, d] using
          (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t))
      have hg_diff : DifferentiableAt ℝ g (z t) := hC2.differentiableAt two_ne_zero
      have hgz : HasDerivAt (fun s => g (z s)) ⟪gradient g (z t), d⟫ t := by
        simpa [inner_gradient_left hg_diff, z, d] using
          (hg_diff.hasFDerivAt.comp t hz_deriv.hasFDerivAt).hasDerivAt
      -- Route correction: differentiate the segment restriction directly, rather than trying
      -- to invoke a nonexistent global Hessian convexity theorem.
      simpa [ψ, ψ', mul_comm, mul_left_comm, mul_assoc] using (hgz.neg.exp.neg).hasDerivWithinAt
    · intro t ht
      have hzD : z t ∈ D := hz_mem (interior_subset ht)
      have hz_nhds : D ∈ 𝓝 (z t) := hD_open.mem_nhds hzD
      have hC2 : ContDiffAt ℝ 2 g (z t) := hg.contDiffAt hz_nhds
      have hz_deriv : HasDerivAt z d t := by
        simpa [z, d] using
          (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t))
      have hg_diff : DifferentiableAt ℝ g (z t) := hC2.differentiableAt two_ne_zero
      have hgz : HasDerivAt (fun s => g (z s)) ⟪gradient g (z t), d⟫ t := by
        simpa [inner_gradient_left hg_diff, z, d] using
          (hg_diff.hasFDerivAt.comp t hz_deriv.hasFDerivAt).hasDerivAt
      let e :
          StrongDual ℝ (EuclideanSpace ℝ (Fin n)) →L[ℝ]
            EuclideanSpace ℝ (Fin n) :=
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearMap
      have hfderiv_field :
          HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) (z t)) (z t) := by
        exact (hC2.fderiv_right_succ.differentiableAt one_ne_zero).hasFDerivAt
      have hgrad_field :
          HasFDerivAt (fun u => gradient g u)
            (e.comp (fderiv ℝ (fderiv ℝ g) (z t))) (z t) := by
        simpa [gradient, e] using (e.hasFDerivAt.comp (z t) hfderiv_field)
      have hgrad_line :
          HasDerivAt (fun s => gradient g (z s))
            (fderiv ℝ (fun u => gradient g u) (z t) d) t := by
        simpa [hgrad_field.fderiv] using (hgrad_field.comp t hz_deriv.hasFDerivAt).hasDerivAt
      have hinner :
          HasDerivAt (fun s => ⟪gradient g (z s), d⟫)
            ⟪fderiv ℝ (fun u => gradient g u) (z t) d, d⟫ t := by
        simpa using HasDerivAt.inner (𝕜 := ℝ) hgrad_line (hasDerivAt_const t d)
      have hexp :
          HasDerivAt (fun s => Real.exp (-(g (z s))))
            (-Real.exp (-(g (z t))) * ⟪gradient g (z t), d⟫) t := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hgz.neg.exp
      -- The product rule produces the block expression that will be controlled by `hblock`.
      have hprod :
          HasDerivWithinAt
            (fun s => Real.exp (-(g (z s))) * ⟪gradient g (z s), d⟫)
            ((-Real.exp (-(g (z t))) * ⟪gradient g (z t), d⟫) * ⟪gradient g (z t), d⟫ +
              Real.exp (-(g (z t))) * ⟪fderiv ℝ (fun u => gradient g u) (z t) d, d⟫)
            (Set.Ioo 0 1) t := by
        simpa using (hexp.mul hinner).hasDerivWithinAt
      convert hprod using 1
      · dsimp [ψ'']
        ring_nf
      · simp [interior_Icc]
    · intro t ht
      have hzD : z t ∈ D := hz_mem (interior_subset ht)
      have hblock' := hblock (z t) hzD (d, -⟪gradient g (z t), d⟫)
      have hnonneg :
          0 ≤
            ⟪fderiv ℝ (fun u => gradient g u) (z t) d, d⟫ -
              ⟪gradient g (z t), d⟫ ^ 2 := by
        nlinarith [hblock']
      exact mul_nonneg (Real.exp_nonneg _) hnonneg
  have hz_ab : z b = a • x + b • y := by
    change AffineMap.lineMap x y b = a • x + b • y
    rw [AffineMap.lineMap_apply_module]
    rw [show 1 - b = a by linarith]
  have hcomb : a • (0 : ℝ) + b • (1 : ℝ) = b := by simp
  simpa [ψ, hcomb, hz_ab, z] using
    hψ_convex.2
      (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by exact ⟨by norm_num, by norm_num⟩)
      (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by exact ⟨by norm_num, by norm_num⟩)
      ha hb hab

end «problem-129»
