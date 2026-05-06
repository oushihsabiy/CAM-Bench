import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-26»

/-- A fixed-`z` slice of a `C²` function on `A ×ˢ B` is still `C²` on `A`. -/
lemma contDiffOn_leftSlice
    {n m : ℕ}
    {A : Set (EuclideanSpace ℝ (Fin n))}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → ℝ}
    (h2 : ContDiffOn ℝ 2
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) => f p.1 p.2) (A ×ˢ B))
    {z : EuclideanSpace ℝ (Fin m)} (hz : z ∈ B) :
    ContDiffOn ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) => f x z) A := by
  -- Compose the product-domain regularity with the smooth embedding `x ↦ (x, z)`.
  refine h2.comp (contDiff_prodMk_left z).contDiffOn ?_
  intro x hx
  exact ⟨hx, hz⟩

/-- A fixed-`x` slice of a `C²` function on `A ×ˢ B` is still `C²` on `B`. -/
lemma contDiffOn_rightSlice
    {n m : ℕ}
    {A : Set (EuclideanSpace ℝ (Fin n))}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → ℝ}
    (h2 : ContDiffOn ℝ 2
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) => f p.1 p.2) (A ×ˢ B))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ A) :
    ContDiffOn ℝ 2 (fun z : EuclideanSpace ℝ (Fin m) => f x z) B := by
  -- Compose the product-domain regularity with the smooth embedding `z ↦ (x, z)`.
  refine h2.comp (contDiff_prodMk_right x).contDiffOn ?_
  intro z hz
  exact ⟨hx, hz⟩

/-- Differentiating a scalar function restricted to an affine line gives the ambient directional
derivative in the line direction. -/
lemma hasDerivAt_lineMap_apply_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x y : E} {t : ℝ}
    (hg : DifferentiableAt ℝ g (AffineMap.lineMap x y t)) :
    HasDerivAt (fun s : ℝ => g (AffineMap.lineMap x y s))
      (fderiv ℝ g (AffineMap.lineMap x y t) (y - x)) t := by
  -- Differentiate the line map first, then apply the chain rule for `g`.
  have hz :
      HasDerivAt (AffineMap.lineMap x y) (y - x) t := by
    simpa using AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t)
  simpa using (hg.hasFDerivAt.comp t hz.hasFDerivAt).hasDerivAt

/-- Differentiating the directional derivative along the same affine line yields the diagonal value
of the second Fréchet derivative. -/
lemma hasDerivAt_lineMap_apply_iteratedFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x y : E} {t : ℝ}
    (hg : ContDiffAt ℝ 2 g (AffineMap.lineMap x y t)) :
    HasDerivAt
      (fun s : ℝ => fderiv ℝ g (AffineMap.lineMap x y s) (y - x))
      (iteratedFDeriv ℝ 2 g (AffineMap.lineMap x y t) ![y - x, y - x]) t := by
  let d : E := y - x
  let z : ℝ → E := AffineMap.lineMap x y
  let evald : (E →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ d
  -- First differentiate the field `x ↦ fderiv g x`, then evaluate at the fixed direction `d`.
  have hz :
      HasDerivAt z d t := by
    simpa [z, d] using AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t)
  have hfderiv :
      HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) (z t)) (z t) := by
    exact hg.fderiv_right_succ.differentiableAt_one.hasFDerivAt
  have hline :
      HasFDerivAt (fun s : ℝ => fderiv ℝ g (z s))
        ((fderiv ℝ (fderiv ℝ g) (z t)).comp (ContinuousLinearMap.toSpanSingleton ℝ d)) t := by
    simpa [z, d] using (hfderiv.comp t hz.hasFDerivAt)
  have hscalar :
      HasDerivAt
        (fun s : ℝ => fderiv ℝ g (z s) d)
        ((((evald.comp ((fderiv ℝ (fderiv ℝ g) (z t)).comp
            (ContinuousLinearMap.toSpanSingleton ℝ d))) : ℝ →L[ℝ] ℝ) 1)) t := by
    exact (evald.hasFDerivAt.comp t hline).hasDerivAt
  -- Route correction: evaluate the derivative field via the continuous linear evaluation map,
  -- then identify the resulting scalar with `iteratedFDeriv` using the `n = 2` API.
  convert hscalar using 1
  simp [iteratedFDeriv_two_apply, z, d, evald, ContinuousLinearMap.toSpanSingleton_apply]
  ring

/-- On an open convex set, a convex `C²` function has nonnegative diagonal second derivatives in
every direction. -/
lemma directionalSecond_nonneg_of_convexOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : Set E} {g : E → ℝ}
    (hQ_open : IsOpen Q)
    (hg2 : ContDiffOn ℝ 2 g Q)
    (hconv : ConvexOn ℝ Q g) :
    ∀ x ∈ Q, ∀ u : E, 0 ≤ iteratedFDeriv ℝ 2 g x ![u, u] := by
  intro x hx u
  let y : E := x + u
  let z : ℝ → E := AffineMap.lineMap x y
  let D : Set ℝ := z ⁻¹' Q
  let ψ : ℝ → ℝ := fun t => g (z t)
  let ψ' : ℝ → ℝ := fun t => fderiv ℝ g (z t) u
  -- Restrict the convex function to the affine line through `x` in direction `u`.
  have hψ_conv : ConvexOn ℝ D ψ := by
    simpa [ψ, D, z, y, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (hconv.comp_affineMap (AffineMap.lineMap x y))
  have hD_open : IsOpen D := by
    simpa [D, z] using hQ_open.preimage AffineMap.lineMap_continuous
  have h0D : (0 : ℝ) ∈ D := by
    simpa [D, z, ψ, y] using hx
  have hψ_deriv :
      Set.EqOn (deriv ψ) ψ' D := by
    intro t ht
    have hCt : ContDiffAt ℝ 2 g (z t) := hg2.contDiffAt (hQ_open.mem_nhds ht)
    have hC1 : ContDiffAt ℝ 1 g (z t) := hCt.of_le (by norm_num)
    have hdiff : DifferentiableAt ℝ g (z t) := hC1.differentiableAt_one
    -- The explicit line-derivative formula identifies `deriv ψ`.
    simpa [ψ', z, y, sub_eq_add_neg] using
      (hasDerivAt_lineMap_apply_fderiv (x := x) (y := y) (t := t) hdiff).deriv
  have hmono : MonotoneOn (deriv ψ) D := by
    -- Convexity of the restriction makes its derivative monotone on the feasible line domain.
    refine hψ_conv.monotoneOn_deriv ?_
    intro t ht
    have hCt : ContDiffAt ℝ 2 g (z t) := hg2.contDiffAt (hQ_open.mem_nhds ht)
    have hC1 : ContDiffAt ℝ 1 g (z t) := hCt.of_le (by norm_num)
    exact (hasDerivAt_lineMap_apply_fderiv (x := x) (y := y) (t := t)
      hC1.differentiableAt_one).differentiableAt
  have hψ'0 :
      HasDerivWithinAt ψ'
        (iteratedFDeriv ℝ 2 g x ![u, u]) D 0 := by
    have hCx : ContDiffAt ℝ 2 g x := hg2.contDiffAt (hQ_open.mem_nhds hx)
    -- The second line derivative at `0` is exactly the diagonal second derivative at `x`.
    simpa [ψ', z, y, AffineMap.lineMap_apply_zero, sub_eq_add_neg] using
      (hasDerivAt_lineMap_apply_iteratedFDeriv
        (x := x) (y := y) (t := (0 : ℝ)) (by simpa [z] using hCx)).hasDerivWithinAt
  have hderiv_within :
      DifferentiableWithinAt ℝ (deriv ψ) D 0 := by
    -- Replace `deriv ψ` by the explicit formula `ψ'` on the domain `D`.
    refine (hψ'0.congr (fun t ht => hψ_deriv ht) ?_).differentiableWithinAt
    simpa using hψ_deriv h0D
  have hnonneg : 0 ≤ derivWithin (deriv ψ) D 0 := by
    simpa using (hmono.derivWithin_nonneg (x := (0 : ℝ)))
  have hrewrite :
      derivWithin (deriv ψ) D 0 = iteratedFDeriv ℝ 2 g x ![u, u] := by
    rw [derivWithin_congr (fun t ht => hψ_deriv ht) (hψ_deriv h0D)]
    exact hψ'0.derivWithin (hD_open.uniqueDiffWithinAt h0D)
  simpa [hrewrite] using hnonneg

/-- On an open convex set, nonnegative diagonal second derivatives in every direction force
convexity. -/
lemma convexOn_of_directionalSecond_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : Set E} {g : E → ℝ}
    (hQ_conv : Convex ℝ Q)
    (hQ_open : IsOpen Q)
    (hg2 : ContDiffOn ℝ 2 g Q)
    (hdiag : ∀ x ∈ Q, ∀ u : E, 0 ≤ iteratedFDeriv ℝ 2 g x ![u, u]) :
    ConvexOn ℝ Q g := by
  refine ⟨hQ_conv, ?_⟩
  intro x hx y hy a b ha hb hab
  let d : E := y - x
  let z : ℝ → E := AffineMap.lineMap x y
  let ψ : ℝ → ℝ := fun t => g (z t)
  let ψ' : ℝ → ℝ := fun t => fderiv ℝ g (z t) d
  let ψ'' : ℝ → ℝ := fun t => iteratedFDeriv ℝ 2 g (z t) ![d, d]
  have hz_mem : Set.MapsTo z (Set.Icc (0 : ℝ) 1) Q := by
    intro t ht
    exact hQ_conv.lineMap_mem hx hy ht
  have hψ_conv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) ψ := by
    refine convexOn_of_hasDerivWithinAt2_nonneg
      (D := Set.Icc (0 : ℝ) 1) (f := ψ) (f' := ψ') (f'' := ψ'') (convex_Icc _ _) ?_ ?_ ?_ ?_
    · -- The segment restriction stays continuous on the compact interval.
      simpa [ψ, z] using
        (hg2.continuousOn.comp AffineMap.lineMap_continuous.continuousOn hz_mem)
    · intro t ht
      have hzQ : z t ∈ Q := hz_mem (interior_subset ht)
      have hCt : ContDiffAt ℝ 2 g (z t) := hg2.contDiffAt (hQ_open.mem_nhds hzQ)
      have hC1 : ContDiffAt ℝ 1 g (z t) := hCt.of_le (by norm_num)
      -- The first derivative along the segment is the directional derivative in direction `d`.
      simpa [ψ', z, d] using
        (hasDerivAt_lineMap_apply_fderiv (x := x) (y := y) (t := t)
          hC1.differentiableAt_one).hasDerivWithinAt
    · intro t ht
      have hzQ : z t ∈ Q := hz_mem (interior_subset ht)
      have hCt : ContDiffAt ℝ 2 g (z t) := hg2.contDiffAt (hQ_open.mem_nhds hzQ)
      -- The second derivative along the segment is exactly the diagonal second derivative.
      simpa [ψ', ψ'', z, d, map_sub] using
        (hasDerivAt_lineMap_apply_iteratedFDeriv (x := x) (y := y) (t := t) hCt).hasDerivWithinAt
    · intro t ht
      exact hdiag (z t) (hz_mem (interior_subset ht)) d
  have hz_ab : z b = a • x + b • y := by
    change AffineMap.lineMap x y b = a • x + b • y
    rw [AffineMap.lineMap_apply_module]
    rw [show 1 - b = a by linarith]
  have hcomb : a • (0 : ℝ) + b • (1 : ℝ) = b := by simp
  -- Evaluate the convex line restriction at the interpolation parameter `b`.
  simpa [ψ, z, hcomb, hz_ab] using
    hψ_conv.2
      (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by exact ⟨by norm_num, by norm_num⟩)
      (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by exact ⟨by norm_num, by norm_num⟩)
      ha hb hab

/-- On an open convex set, a concave `C²` function has nonpositive diagonal second derivatives in
every direction. -/
lemma directionalSecond_nonpos_of_concaveOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : Set E} {g : E → ℝ}
    (hQ_open : IsOpen Q)
    (hg2 : ContDiffOn ℝ 2 g Q)
    (hconc : ConcaveOn ℝ Q g) :
    ∀ x ∈ Q, ∀ u : E, iteratedFDeriv ℝ 2 g x ![u, u] ≤ 0 := by
  intro x hx u
  -- Route correction: reduce the concave case to the convex theorem for `-g`.
  have hneg :
      0 ≤ iteratedFDeriv ℝ 2 (-g) x ![u, u] := by
    simpa [iteratedFDeriv_neg_apply] using
      directionalSecond_nonneg_of_convexOn hQ_open
        (by simpa using hg2.neg)
        (neg_convexOn_iff.mpr hconc) x hx u
  simpa [iteratedFDeriv_neg_apply] using hneg

/-- On an open convex set, nonpositive diagonal second derivatives in every direction force
concavity. -/
lemma concaveOn_of_directionalSecond_nonpos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : Set E} {g : E → ℝ}
    (hQ_conv : Convex ℝ Q)
    (hQ_open : IsOpen Q)
    (hg2 : ContDiffOn ℝ 2 g Q)
    (hdiag : ∀ x ∈ Q, ∀ u : E, iteratedFDeriv ℝ 2 g x ![u, u] ≤ 0) :
    ConcaveOn ℝ Q g := by
  have hneg :
      ConvexOn ℝ Q (-g) := by
    refine convexOn_of_directionalSecond_nonneg hQ_conv hQ_open ?_ ?_
    · simpa using hg2.neg
    · intro x hx u
      simpa [iteratedFDeriv_neg_apply] using neg_nonneg.mpr (hdiag x hx u)
  simpa using (neg_convexOn_iff.mp hneg)

/- 
A function f: A × B → ℝ is convex - concave if, for each fixed z ∈ B, the map x mapsto f(x, z) is
convex on A, and for each fixed x ∈ A, the map z mapsto f(x, z) is concave on B.
-/
theorem isConvexConcave_iff_hessian_blocks_semidefinite
    {n m : ℕ}
    (A : Set (EuclideanSpace ℝ (Fin n)))
    (B : Set (EuclideanSpace ℝ (Fin m)))
    (hA_open : IsOpen A)
    (hB_open : IsOpen B)
    (hA : Convex ℝ A)
    (hB : Convex ℝ B)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → ℝ)
    (h2 : ContDiffOn ℝ 2
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) => f p.1 p.2) (A ×ˢ B)) :
    ((∀ z ∈ B, ConvexOn ℝ A (fun x => f x z)) ∧
      (∀ x ∈ A, ConcaveOn ℝ B (fun z => f x z))) ↔
      (∀ x ∈ A, ∀ z ∈ B,
        (∀ u : EuclideanSpace ℝ (Fin n),
          0 ≤
            iteratedFDeriv ℝ 2 (fun x' => f x' z) x ![u, u]) ∧
        (∀ v : EuclideanSpace ℝ (Fin m),
          iteratedFDeriv ℝ 2 (fun z' => f x z') z ![v, v] ≤ 0)) := by
  constructor
  · rintro ⟨hx_conv, hz_conc⟩ x hx z hz
    constructor
    · intro u
      -- Fix `z` and apply the generic convex slice criterion on `A`.
      exact directionalSecond_nonneg_of_convexOn hA_open
        (contDiffOn_leftSlice h2 hz) (hx_conv z hz) x hx u
    · intro v
      -- Fix `x` and apply the generic concave slice criterion on `B`.
      exact directionalSecond_nonpos_of_concaveOn hB_open
        (contDiffOn_rightSlice h2 hx) (hz_conc x hx) z hz v
  · intro hdiag
    constructor
    · intro z hz
      -- For a fixed `z`, convexity follows from nonnegative directional second derivatives.
      refine convexOn_of_directionalSecond_nonneg hA hA_open (contDiffOn_leftSlice h2 hz) ?_
      intro x hx u
      exact (hdiag x hx z hz).1 u
    · intro x hx
      -- For a fixed `x`, concavity follows from nonpositive directional second derivatives.
      refine concaveOn_of_directionalSecond_nonpos hB hB_open (contDiffOn_rightSlice h2 hx) ?_
      intro z hz v
      exact (hdiag x hx z hz).2 v

end «problem-26»
