import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-101»
/-
Let D subseteq ℝ^n be a convex set, and let g: D → ℝ be twice continuously differentiable. Define f:
D → ℝ by f(x) = - exp(- g(x)). Assume that for every x in D, the block matrix [[nabla^2 g(x), nabla
g(x)], [nabla g(x)ᵀ, 1]] is positive semidefinite. Prove that f is convex on D.
-/
open scoped RealInnerProductSpace

/-- Specializing the block positivity inequality at the scalar that cancels the linear term yields
the nonnegative Hessian-gradient combination needed for `-exp (-g)`. -/
lemma block_quadratic_specialization_nonneg
    {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {hess : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hblock :
      ∀ x ∈ D, ∀ (u : EuclideanSpace ℝ (Fin n)) (s : ℝ),
        0 ≤ ⟪hess x u, u⟫ + 2 * s * ⟪G x, u⟫ + s ^ 2)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ D) (u : EuclideanSpace ℝ (Fin n)) :
    0 ≤ ⟪hess z u, u⟫ - ⟪G z, u⟫ ^ 2 := by
  -- Choose the scalar that removes the mixed term from the quadratic form.
  have hquad := hblock z hz u (-⟪G z, u⟫)
  -- Simplifying that specialization gives the desired lower bound.
  nlinarith

/-- Restricting `g` to an affine line turns the derivative into the gradient paired with the line
direction. -/
lemma hasDerivAt_line_restriction_g
    {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))}
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hgrad : ∀ x ∈ D, HasGradientAt g (G x) x)
    {x y : EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hz : AffineMap.lineMap x y t ∈ D) :
    HasDerivAt (fun τ : ℝ => g (AffineMap.lineMap x y τ))
      ⟪G (AffineMap.lineMap x y t), y - x⟫ t := by
  -- Differentiate the affine line first.
  have hline : HasDerivAt (AffineMap.lineMap x y) (y - x) t := by
    simpa using AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t)
  -- Then compose with the ambient gradient formula at the current point.
  have hgradz : HasGradientAt g (G (AffineMap.lineMap x y t)) (AffineMap.lineMap x y t) :=
    hgrad _ hz
  simpa using
    HasFDerivAt.comp_hasDerivAt (x := t) (f := AffineMap.lineMap x y) hgradz.hasFDerivAt hline

/-- Restricting the gradient field to an affine line and pairing with the fixed line direction
produces the Hessian quadratic form. -/
lemma hasDerivAt_line_restriction_inner_gradient
    {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {hess : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hhess : ∀ x ∈ D, HasFDerivAt G (hess x) x)
    {x y : EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hz : AffineMap.lineMap x y t ∈ D) :
    HasDerivAt (fun τ : ℝ => ⟪G (AffineMap.lineMap x y τ), y - x⟫)
      ⟪hess (AffineMap.lineMap x y t) (y - x), y - x⟫ t := by
  -- Differentiate the vector-valued gradient field along the affine line.
  have hline : HasDerivAt (AffineMap.lineMap x y) (y - x) t := by
    simpa using AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t)
  have hGline :
      HasDerivAt (fun τ : ℝ => G (AffineMap.lineMap x y τ))
        (hess (AffineMap.lineMap x y t) (y - x)) t := by
    simpa using
      HasFDerivAt.comp_hasDerivAt (x := t) (f := AffineMap.lineMap x y) (hhess _ hz) hline
  -- Pairing with the constant direction vector extracts the scalar quadratic form.
  simpa using HasDerivAt.inner (𝕜 := ℝ) hGline (hasDerivAt_const t (y - x))

theorem convexOn_neg_exp_neg_of_hessian_gradient_block_pos
    {n : ℕ}
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hess : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hD : Convex ℝ D)
    (hg : ContDiffOn ℝ 2 g D)
    (hgrad : ∀ x ∈ D, HasGradientAt g (G x) x)
    (hhess : ∀ x ∈ D, HasFDerivAt G (hess x) x)
    (hblock :
      ∀ x ∈ D, ∀ (u : EuclideanSpace ℝ (Fin n)) (s : ℝ),
        0 ≤ ⟪hess x u, u⟫ + 2 * s * ⟪G x, u⟫ + s ^ 2) :
    ConvexOn ℝ D (fun x => -Real.exp (-g x)) := by
  -- Restrict the multivariable problem to each affine segment inside `D`.
  refine convexOn_iff_forall_pos.mpr ?_
  refine ⟨hD, ?_⟩
  intro x hx y hy a b ha hb hab
  let d : EuclideanSpace ℝ (Fin n) := y - x
  let z : ℝ → EuclideanSpace ℝ (Fin n) := AffineMap.lineMap x y
  let ψ : ℝ → ℝ := fun t => -Real.exp (-(g (z t)))
  let ψ' : ℝ → ℝ := fun t => Real.exp (-(g (z t))) * ⟪G (z t), d⟫
  let ψ'' : ℝ → ℝ :=
    fun t => Real.exp (-(g (z t))) * (⟪hess (z t) d, d⟫ - ⟪G (z t), d⟫ ^ 2)
  have hz_mem : Set.MapsTo z (Set.Icc (0 : ℝ) 1) D := by
    intro t ht
    exact hD.lineMap_mem hx hy ht
  have hψ_convex : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) ψ := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (D := Set.Icc (0 : ℝ) 1)
      (f := ψ) (f' := ψ') (f'' := ψ'') (convex_Icc (0 : ℝ) 1) ?_ ?_ ?_ ?_
    · -- The segment restriction is continuous because `g` is continuous on `D`.
      have hz_cont : Continuous z := by
        simpa [z] using (continuous_const.lineMap continuous_const continuous_id)
      simpa [ψ] using (hg.continuousOn.comp hz_cont.continuousOn hz_mem).neg.rexp.neg
    · intro t ht
      have hzD : z t ∈ D := hz_mem (interior_subset ht)
      have hgz : HasDerivAt (fun s : ℝ => g (z s)) ⟪G (z t), d⟫ t := by
        simpa [z, d] using
          hasDerivAt_line_restriction_g (D := D) (g := g) (G := G) hgrad
            (x := x) (y := y) (t := t) hzD
      -- Differentiate `-exp (-g)` along the segment once.
      simpa [ψ, ψ', z, d, mul_comm, mul_left_comm, mul_assoc] using
        (hgz.neg.exp.neg).hasDerivWithinAt
    · intro t ht
      have hzD : z t ∈ D := hz_mem (interior_subset ht)
      have hgz : HasDerivAt (fun s : ℝ => g (z s)) ⟪G (z t), d⟫ t := by
        simpa [z, d] using
          hasDerivAt_line_restriction_g (D := D) (g := g) (G := G) hgrad
            (x := x) (y := y) (t := t) hzD
      have hinner :
          HasDerivAt (fun s : ℝ => ⟪G (z s), d⟫) ⟪hess (z t) d, d⟫ t := by
        simpa [z, d] using
          hasDerivAt_line_restriction_inner_gradient (D := D) (G := G) (hess := hess) hhess
            (x := x) (y := y) (t := t) hzD
      have hexp :
          HasDerivAt (fun s : ℝ => Real.exp (-(g (z s))))
            (-Real.exp (-(g (z t))) * ⟪G (z t), d⟫) t := by
        simpa [z, d, mul_comm, mul_left_comm, mul_assoc] using hgz.neg.exp
      -- The product rule produces the Hessian-gradient expression along the segment.
      have hprod :
          HasDerivWithinAt
            (fun s : ℝ => Real.exp (-(g (z s))) * ⟪G (z s), d⟫)
            ((-Real.exp (-(g (z t))) * ⟪G (z t), d⟫) * ⟪G (z t), d⟫ +
              Real.exp (-(g (z t))) * ⟪hess (z t) d, d⟫)
            (Set.Ioo 0 1) t := by
        simpa using (hexp.mul hinner).hasDerivWithinAt
      convert hprod using 1
      · dsimp [ψ'']
        ring_nf
      · simp [interior_Icc]
    · intro t ht
      have hzD : z t ∈ D := hz_mem (interior_subset ht)
      have hnonneg :
          0 ≤ ⟪hess (z t) d, d⟫ - ⟪G (z t), d⟫ ^ 2 := by
        simpa [z, d] using
          block_quadratic_specialization_nonneg (G := G) (hess := hess) hblock hzD d
      exact mul_nonneg (Real.exp_nonneg _) hnonneg
  have hz_ab : z b = a • x + b • y := by
    change AffineMap.lineMap x y b = a • x + b • y
    rw [AffineMap.lineMap_apply_module]
    rw [show 1 - b = a by linarith]
  have hcomb : a • (0 : ℝ) + b • (1 : ℝ) = b := by
    simp
  -- Evaluate the one-dimensional convexity inequality at the segment endpoints.
  simpa [ψ, z, hcomb, hz_ab] using
    hψ_convex.2
      (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by exact ⟨by norm_num, by norm_num⟩)
      (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by exact ⟨by norm_num, by norm_num⟩)
      ha.le hb.le hab

end «problem-101»
