import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-103»
/-
Let A ⊆ ℝ^n and B ⊆ ℝ^m be convex. Let f: ℝ^n × ℝ^m → ℝ be differentiable, convex in x for each
fixed z, and concave in z for each fixed x. If (x̃, z̃) ∈ A × B satisfies ∇f(x̃, z̃) = 0, prove that
for all x ∈ A and z ∈ B, f(x̃, z) ≤ f(x̃, z̃) ≤ f(x, z̃).
-/


theorem saddle_inequalities_of_gradient_zero
    {n m : ℕ}
    {A : Set (EuclideanSpace ℝ (Fin n))}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → ℝ}
    {xtilde : EuclideanSpace ℝ (Fin n)}
    {ztilde : EuclideanSpace ℝ (Fin m)}
    (hA : Convex ℝ A)
    (hB : Convex ℝ B)
    (hxz : xtilde ∈ A ∧ ztilde ∈ B)
    (hconvex : ∀ z ∈ B, ConvexOn ℝ A (fun x => f (x, z)))
    (hconcave : ∀ x ∈ A, ConvexOn ℝ B (fun z => -f (x, z)))
    (hinf_bddBelow :
      ∀ z ∈ B, BddBelow {s : ℝ | ∃ x ∈ A, s = f (x, z)})
    (hsup_bddAbove :
      ∀ x ∈ A, BddAbove {s : ℝ | ∃ z ∈ B, s = f (x, z)})
    (hleft_bddAbove :
      BddAbove {r : ℝ | ∃ z ∈ B, r = sInf {s : ℝ | ∃ x ∈ A, s = f (x, z)}})
    (hright_bddBelow :
      BddBelow {r : ℝ | ∃ x ∈ A, r = sSup {s : ℝ | ∃ z ∈ B, s = f (x, z)}})
    (hgrad_zero :
      HasFDerivAt f
        (0 :
          (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ)
        (xtilde, ztilde)) :
    ∀ x ∈ A, ∀ z ∈ B, f (xtilde, z) ≤ f (xtilde, ztilde) ∧ f (xtilde, ztilde) ≤ f (x, ztilde) := by
  intro x hx z hz
  rcases hxz with ⟨hxtilde, hztilde⟩
  -- Restrict `f` to the coordinate segments through `(xtilde, ztilde)`.
  let gx : ℝ → ℝ := fun t => f (AffineMap.lineMap xtilde x t, ztilde)
  let gz : ℝ → ℝ := fun t => f (xtilde, AffineMap.lineMap ztilde z t)
  -- Convexity in `x` descends to the segment `[xtilde, x]`, then to `Icc 0 1`.
  have hgx_convex_pre :
      ConvexOn ℝ ((AffineMap.lineMap xtilde x) ⁻¹' A) gx := by
    simpa [gx, Function.comp] using
      (hconvex ztilde hztilde).comp_affineMap (AffineMap.lineMap xtilde x)
  have hgx_convex : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) gx :=
    hgx_convex_pre.subset (hA.mapsTo_lineMap hxtilde hx) (convex_Icc (0 : ℝ) 1)
  -- Concavity in `z` is obtained by rewriting the given convexity of `-f`.
  have hgz_concave_base : ConcaveOn ℝ B (fun z' => f (xtilde, z')) := by
    simpa using (neg_convexOn_iff.mp (hconcave xtilde hxtilde))
  have hgz_concave_pre :
      ConcaveOn ℝ ((AffineMap.lineMap ztilde z) ⁻¹' B) gz := by
    simpa [gz, Function.comp] using
      hgz_concave_base.comp_affineMap (AffineMap.lineMap ztilde z)
  have hgz_concave : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) gz :=
    hgz_concave_pre.subset (hB.mapsTo_lineMap hztilde hz) (convex_Icc (0 : ℝ) 1)
  -- Compose the zero Fréchet derivative with the `x`-segment to get zero scalar derivative at `0`.
  let gammax : ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) :=
    fun t => (AffineMap.lineMap xtilde x t, ztilde)
  have hgammax : HasDerivAt gammax (x - xtilde, 0) 0 := by
    simpa [gammax] using
      (HasDerivAt.prodMk (𝕜 := ℝ)
        (AffineMap.hasDerivAt_lineMap (a := xtilde) (b := x) (x := (0 : ℝ)))
        (hasDerivAt_const (0 : ℝ) ztilde))
  have hgrad_zero_x :
      HasFDerivAt f
        (0 :
          (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ)
        (gammax 0) := by
    simpa [gammax] using hgrad_zero
  have hgx_deriv : HasDerivAt gx 0 0 := by
    simpa [gx, gammax, ContinuousLinearMap.zero_apply] using
      (HasFDerivAt.comp_hasDerivAt (f := gammax) (l := f) (x := (0 : ℝ)) hgrad_zero_x
        hgammax)
  -- The same composition argument gives zero derivative along the `z`-segment.
  let gammaz : ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) :=
    fun t => (xtilde, AffineMap.lineMap ztilde z t)
  have hgammaz : HasDerivAt gammaz (0, z - ztilde) 0 := by
    simpa [gammaz] using
      (HasDerivAt.prodMk (𝕜 := ℝ)
        (hasDerivAt_const (0 : ℝ) xtilde)
        (AffineMap.hasDerivAt_lineMap (a := ztilde) (b := z) (x := (0 : ℝ))))
  have hgrad_zero_z :
      HasFDerivAt f
        (0 :
          (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ)
        (gammaz 0) := by
    simpa [gammaz] using hgrad_zero
  have hgz_deriv : HasDerivAt gz 0 0 := by
    simpa [gz, gammaz, ContinuousLinearMap.zero_apply] using
      (HasFDerivAt.comp_hasDerivAt (f := gammaz) (l := f) (x := (0 : ℝ)) hgrad_zero_z
        hgammaz)
  -- The convex slice has nonnegative secant slope from `0` to `1`, giving the right inequality.
  have hxineq_slope : 0 ≤ slope gx 0 1 :=
    hgx_convex.le_slope_of_hasDerivAt (by simp) (by simp) zero_lt_one hgx_deriv
  have hxineq : f (xtilde, ztilde) ≤ f (x, ztilde) := by
    simpa [gx, slope_def_field] using hxineq_slope
  -- The concave slice has secant slope at most the derivative `0`, giving the left inequality.
  have hzineq_slope : slope gz 0 1 ≤ 0 :=
    hgz_concave.slope_le_of_hasDerivAt (by simp) (by simp) zero_lt_one hgz_deriv
  have hzineq : f (xtilde, z) ≤ f (xtilde, ztilde) := by
    simpa [gz, slope_def_field] using hzineq_slope
  exact ⟨hzineq, hxineq⟩

/-
Under the same assumptions, prove sup_{z∈B} \inf_{x∈A} f(x, z) = \inf_{x∈A} sup_{z∈B} f(x, z), and
that the common value equals f(x̃, z̃).
-/
theorem minimax_eq_of_gradient_zero
    {n m : ℕ}
    {A : Set (EuclideanSpace ℝ (Fin n))}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → ℝ}
    {xtilde : EuclideanSpace ℝ (Fin n)}
    {ztilde : EuclideanSpace ℝ (Fin m)}
    (hA : Convex ℝ A)
    (hB : Convex ℝ B)
    (hxz : xtilde ∈ A ∧ ztilde ∈ B)
    (hconvex : ∀ z ∈ B, ConvexOn ℝ A (fun x => f (x, z)))
    (hconcave : ∀ x ∈ A, ConvexOn ℝ B (fun z => -f (x, z)))
    (hinf_bddBelow :
      ∀ z ∈ B, BddBelow {s : ℝ | ∃ x ∈ A, s = f (x, z)})
    (hsup_bddAbove :
      ∀ x ∈ A, BddAbove {s : ℝ | ∃ z ∈ B, s = f (x, z)})
    (hleft_bddAbove :
      BddAbove {r : ℝ | ∃ z ∈ B, r = sInf {s : ℝ | ∃ x ∈ A, s = f (x, z)}})
    (hright_bddBelow :
      BddBelow {r : ℝ | ∃ x ∈ A, r = sSup {s : ℝ | ∃ z ∈ B, s = f (x, z)}})
    (hgrad_zero :
      HasFDerivAt f
        (0 :
          (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ)
        (xtilde, ztilde)) :
    sSup {r : ℝ | ∃ z ∈ B, r = sInf {s : ℝ | ∃ x ∈ A, s = f (x, z)}} =
      sInf {r : ℝ | ∃ x ∈ A, r = sSup {s : ℝ | ∃ z ∈ B, s = f (x, z)}} ∧
    sSup {r : ℝ | ∃ z ∈ B, r = sInf {s : ℝ | ∃ x ∈ A, s = f (x, z)}} =
      f (xtilde, ztilde) := by
  rcases hxz with ⟨hxtilde, hztilde⟩
  let leftSet : Set ℝ :=
    {r : ℝ | ∃ z ∈ B, r = sInf {s : ℝ | ∃ x ∈ A, s = f (x, z)}}
  let rightSet : Set ℝ :=
    {r : ℝ | ∃ x ∈ A, r = sSup {s : ℝ | ∃ z ∈ B, s = f (x, z)}}
  -- Reuse the previously proved saddle-point inequalities at `(xtilde, ztilde)`.
  have hsaddle :
      ∀ x ∈ A, ∀ z ∈ B, f (xtilde, z) ≤ f (xtilde, ztilde) ∧ f (xtilde, ztilde) ≤ f (x, ztilde) :=
    saddle_inequalities_of_gradient_zero hA hB ⟨hxtilde, hztilde⟩ hconvex hconcave
      hinf_bddBelow hsup_bddAbove hleft_bddAbove hright_bddBelow hgrad_zero
  have hleft_nonempty : leftSet.Nonempty := by
    -- The `ztilde`-slice witnesses that the outer supremum is taken over a nonempty set.
    refine ⟨sInf {s : ℝ | ∃ x ∈ A, s = f (x, ztilde)}, ?_⟩
    exact ⟨ztilde, hztilde, rfl⟩
  have hright_nonempty : rightSet.Nonempty := by
    -- The `xtilde`-slice witnesses that the outer infimum is taken over a nonempty set.
    refine ⟨sSup {s : ℝ | ∃ z ∈ B, s = f (xtilde, z)}, ?_⟩
    exact ⟨xtilde, hxtilde, rfl⟩
  have hleft_eq : sSup leftSet = f (xtilde, ztilde) := by
    apply le_antisymm
    · -- Every inner infimum is bounded above by the saddle value, so the outer supremum is too.
      apply csSup_le hleft_nonempty
      intro r hr
      rcases hr with ⟨z, hz, rfl⟩
      have hinner_le : sInf {s : ℝ | ∃ x ∈ A, s = f (x, z)} ≤ f (xtilde, z) :=
        csInf_le (hinf_bddBelow z hz) ⟨xtilde, hxtilde, rfl⟩
      exact le_trans hinner_le (hsaddle xtilde hxtilde z hz).1
    · -- The `ztilde`-slice already has value at least the saddle value, so the outer supremum reaches it.
      have hinner_nonempty : ({s : ℝ | ∃ x ∈ A, s = f (x, ztilde)} : Set ℝ).Nonempty := by
        exact ⟨f (xtilde, ztilde), ⟨xtilde, hxtilde, rfl⟩⟩
      have hbase_le :
          f (xtilde, ztilde) ≤ sInf {s : ℝ | ∃ x ∈ A, s = f (x, ztilde)} := by
        apply le_csInf hinner_nonempty
        intro s hs
        rcases hs with ⟨x, hx, rfl⟩
        exact (hsaddle x hx ztilde hztilde).2
      exact le_trans hbase_le (le_csSup hleft_bddAbove ⟨ztilde, hztilde, rfl⟩)
  have hright_eq : sInf rightSet = f (xtilde, ztilde) := by
    apply le_antisymm
    · -- The `xtilde`-slice has supremum at most the saddle value, so the outer infimum is also at most it.
      have hinner_nonempty : ({s : ℝ | ∃ z ∈ B, s = f (xtilde, z)} : Set ℝ).Nonempty := by
        exact ⟨f (xtilde, ztilde), ⟨ztilde, hztilde, rfl⟩⟩
      have hsup_le :
          sSup {s : ℝ | ∃ z ∈ B, s = f (xtilde, z)} ≤ f (xtilde, ztilde) := by
        apply csSup_le hinner_nonempty
        intro s hs
        rcases hs with ⟨z, hz, rfl⟩
        exact (hsaddle xtilde hxtilde z hz).1
      exact le_trans (csInf_le hright_bddBelow ⟨xtilde, hxtilde, rfl⟩) hsup_le
    · -- Any outer witness dominates the saddle value because its inner supremum contains `f (x, ztilde)`.
      apply le_csInf hright_nonempty
      intro r hr
      rcases hr with ⟨x, hx, rfl⟩
      have hmem :
          f (x, ztilde) ∈ {s : ℝ | ∃ z ∈ B, s = f (x, z)} := by
        exact ⟨ztilde, hztilde, rfl⟩
      have hle_sup : f (x, ztilde) ≤ sSup {s : ℝ | ∃ z ∈ B, s = f (x, z)} :=
        le_csSup (hsup_bddAbove x hx) hmem
      exact le_trans (hsaddle x hx ztilde hztilde).2 hle_sup
  -- Both outer extrema equal the same saddle value, so they equal each other as well.
  constructor
  · rw [hleft_eq, hright_eq]
  · exact hleft_eq

end «problem-103»
