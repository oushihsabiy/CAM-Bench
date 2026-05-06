import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-27»

/-- Fixing the second argument of a `C²` map preserves the `C²` regularity of the `x`-slice. -/
lemma contDiff_xSlice
    {n m : ℕ}
    {f : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → ℝ}
    (hf : ContDiff ℝ 2 f) (z : EuclideanSpace ℝ (Fin m)) :
    ContDiff ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) => f (x, z)) := by
  -- Fixing `z` turns `f` into a composition with the smooth map `x ↦ (x, z)`.
  simpa using hf.comp (contDiff_prodMk_left z)

/-- Fixing the first argument of a `C²` map preserves the `C²` regularity of the `z`-slice. -/
lemma contDiff_zSlice
    {n m : ℕ}
    {f : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → ℝ}
    (hf : ContDiff ℝ 2 f) (x : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ 2 (fun z : EuclideanSpace ℝ (Fin m) => f (x, z)) := by
  -- Fixing `x` turns `f` into a composition with the smooth map `z ↦ (x, z)`.
  simpa using hf.comp (contDiff_prodMk_right x)

/-- The second derivative of an `x`-line restriction is the `x`-block second directional
derivative along the same line. -/
lemma xLine_secondDeriv
    {n m : ℕ}
    {f : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → ℝ}
    (hf : ContDiff ℝ 2 f)
    (x y : EuclideanSpace ℝ (Fin n))
    (z : EuclideanSpace ℝ (Fin m))
    (t : ℝ) :
    deriv^[2] (fun s : ℝ => f (AffineMap.lineMap x y s, z)) t =
      (fderiv ℝ
        (fun x0 : EuclideanSpace ℝ (Fin n) =>
          (fderiv ℝ (fun x1 : EuclideanSpace ℝ (Fin n) => f (x1, z)) x0) (y - x))
        (AffineMap.lineMap x y t)) (y - x) := by
  let h : EuclideanSpace ℝ (Fin n) → ℝ := fun x' => f (x', z)
  have hone : (1 : WithTop ℕ∞) ≤ 2 := by
    norm_num
  have h12 : (1 : WithTop ℕ∞) + 1 ≤ 2 := by
    norm_num
  have h_slice : ContDiff ℝ 2 h := by
    -- Restricting to a fixed `z` keeps the slice `C²`.
    simpa [h] using contDiff_xSlice (hf := hf) z
  have h_slice_one : ContDiff ℝ 1 h := by
    exact h_slice.of_le hone
  have h_first :
      ∀ s : ℝ,
        deriv (fun u : ℝ => h (AffineMap.lineMap x y u)) s =
          (fderiv ℝ h (AffineMap.lineMap x y s)) (y - x) := by
    intro s
    -- The first derivative of the line restriction is the slice derivative in direction `y - x`.
    have h_diff_h : DifferentiableAt ℝ h (AffineMap.lineMap x y s) := by
      exact h_slice_one.differentiable_one (AffineMap.lineMap x y s)
    simpa [h] using
      (fderiv_comp_deriv (x := s) (l := h) (f := AffineMap.lineMap x y)
        h_diff_h (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := s)).differentiableAt)
  have h_bundle :
      ContDiff ℝ 1
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          (fderiv ℝ h p.1 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) p.2) := by
    -- A `C²` slice has a `C¹` bundled derivative.
    exact h_slice.contDiff_fderiv_apply (m := 1) h12
  have h_outer :
      ContDiff ℝ 1
        (fun x0 : EuclideanSpace ℝ (Fin n) =>
          (fderiv ℝ h x0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (y - x)) := by
    -- Evaluating the bundled derivative at a fixed vector keeps the map `C¹`.
    have h_dir : ContDiff ℝ 1 (fun _ : EuclideanSpace ℝ (Fin n) => y - x) := by
      simpa using (contDiff_const : ContDiff ℝ 1 (fun _ : EuclideanSpace ℝ (Fin n) => y - x))
    convert h_bundle.comp (contDiff_id.prodMk h_dir) using 1
  -- Differentiate the first-derivative formula once more along the same affine line.
  change deriv (fun s => deriv (fun u : ℝ => h (AffineMap.lineMap x y u)) s) t = _
  have h_diff_outer :
      DifferentiableAt ℝ
        (fun x0 : EuclideanSpace ℝ (Fin n) =>
          (fderiv ℝ h x0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (y - x))
        (AffineMap.lineMap x y t) := by
    exact h_outer.differentiable_one (AffineMap.lineMap x y t)
  simpa [h_first, h] using
    (fderiv_comp_deriv (x := t)
      (l := fun x0 : EuclideanSpace ℝ (Fin n) =>
        (fderiv ℝ h x0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (y - x))
      (f := AffineMap.lineMap x y)
      h_diff_outer
      (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t)).differentiableAt)

/-- The second derivative of a `z`-line restriction is the `z`-block second directional
derivative along the same line. -/
lemma zLine_secondDeriv
    {n m : ℕ}
    {f : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → ℝ}
    (hf : ContDiff ℝ 2 f)
    (x : EuclideanSpace ℝ (Fin n))
    (z₁ z₂ : EuclideanSpace ℝ (Fin m))
    (t : ℝ) :
    deriv^[2] (fun s : ℝ => f (x, AffineMap.lineMap z₁ z₂ s)) t =
      (fderiv ℝ
        (fun z0 : EuclideanSpace ℝ (Fin m) =>
          (fderiv ℝ (fun z1 : EuclideanSpace ℝ (Fin m) => f (x, z1)) z0) (z₂ - z₁))
        (AffineMap.lineMap z₁ z₂ t)) (z₂ - z₁) := by
  let h : EuclideanSpace ℝ (Fin m) → ℝ := fun z' => f (x, z')
  have hone : (1 : WithTop ℕ∞) ≤ 2 := by
    norm_num
  have h12 : (1 : WithTop ℕ∞) + 1 ≤ 2 := by
    norm_num
  have h_slice : ContDiff ℝ 2 h := by
    -- Restricting to a fixed `x` keeps the slice `C²`.
    simpa [h] using contDiff_zSlice (hf := hf) x
  have h_slice_one : ContDiff ℝ 1 h := by
    exact h_slice.of_le hone
  have h_first :
      ∀ s : ℝ,
        deriv (fun u : ℝ => h (AffineMap.lineMap z₁ z₂ u)) s =
          (fderiv ℝ h (AffineMap.lineMap z₁ z₂ s)) (z₂ - z₁) := by
    intro s
    -- The first derivative of the line restriction is the slice derivative in direction `z₂ - z₁`.
    have h_diff_h : DifferentiableAt ℝ h (AffineMap.lineMap z₁ z₂ s) := by
      exact h_slice_one.differentiable_one (AffineMap.lineMap z₁ z₂ s)
    simpa [h] using
      (fderiv_comp_deriv (x := s) (l := h) (f := AffineMap.lineMap z₁ z₂)
        h_diff_h (AffineMap.hasDerivAt_lineMap (a := z₁) (b := z₂) (x := s)).differentiableAt)
  have h_bundle :
      ContDiff ℝ 1
        (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) =>
          (fderiv ℝ h p.1 : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) p.2) := by
    -- A `C²` slice has a `C¹` bundled derivative.
    exact h_slice.contDiff_fderiv_apply (m := 1) h12
  have h_outer :
      ContDiff ℝ 1
        (fun z0 : EuclideanSpace ℝ (Fin m) =>
          (fderiv ℝ h z0 : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (z₂ - z₁)) := by
    -- Evaluating the bundled derivative at a fixed vector keeps the map `C¹`.
    have h_dir : ContDiff ℝ 1 (fun _ : EuclideanSpace ℝ (Fin m) => z₂ - z₁) := by
      simpa using (contDiff_const : ContDiff ℝ 1 (fun _ : EuclideanSpace ℝ (Fin m) => z₂ - z₁))
    convert h_bundle.comp (contDiff_id.prodMk h_dir) using 1
  -- Differentiate the first-derivative formula once more along the same affine line.
  change deriv (fun s => deriv (fun u : ℝ => h (AffineMap.lineMap z₁ z₂ u)) s) t = _
  have h_diff_outer :
      DifferentiableAt ℝ
        (fun z0 : EuclideanSpace ℝ (Fin m) =>
          (fderiv ℝ h z0 : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (z₂ - z₁))
        (AffineMap.lineMap z₁ z₂ t) := by
    exact h_outer.differentiable_one (AffineMap.lineMap z₁ z₂ t)
  simpa [h_first, h] using
    (fderiv_comp_deriv (x := t)
      (l := fun z0 : EuclideanSpace ℝ (Fin m) =>
        (fderiv ℝ h z0 : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (z₂ - z₁))
      (f := AffineMap.lineMap z₁ z₂)
      h_diff_outer
      (AffineMap.hasDerivAt_lineMap (a := z₁) (b := z₂) (x := t)).differentiableAt)

/-- A fixed-`z` slice is convex once every second directional derivative in the `x`-variable is
nonnegative. -/
lemma convex_xSlice_of_secondDirectional_nonneg
    {n m : ℕ}
    {f : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → ℝ}
    (hf : ContDiff ℝ 2 f)
    (z : EuclideanSpace ℝ (Fin m))
    (hxx :
      ∀ x v : EuclideanSpace ℝ (Fin n),
        0 ≤
          (fderiv ℝ
            (fun x0 : EuclideanSpace ℝ (Fin n) =>
              (fderiv ℝ (fun x1 : EuclideanSpace ℝ (Fin n) => f (x1, z)) x0) v)
            x) v) :
    ConvexOn ℝ Set.univ (fun x : EuclideanSpace ℝ (Fin n) => f (x, z)) := by
  rw [convexOn_iff_div]
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  let g : ℝ → ℝ := fun t => f (AffineMap.lineMap x y t, z)
  have hone : (1 : WithTop ℕ∞) ≤ 2 := by
    norm_num
  have h_g_smooth : ContDiff ℝ 2 g := by
    -- The affine-line restriction of a `C²` slice is still `C²`.
    have h_slice : ContDiff ℝ 2 (fun x0 : EuclideanSpace ℝ (Fin n) => f (x0, z)) := by
      exact contDiff_xSlice (hf := hf) z
    have h_line : ContDiff ℝ 2 (fun t : ℝ => AffineMap.lineMap x y t) := by
      simpa [ContinuousAffineMap.coe_lineMap_eq] using
        (ContinuousAffineMap.lineMap (R := ℝ) x y).contDiff (n := (2 : WithTop ℕ∞))
    simpa [g] using h_slice.comp h_line
  have h_g_c1 : ContDiff ℝ 1 g := by
    exact h_g_smooth.of_le hone
  have h_g_second_nonneg : ∀ t : ℝ, 0 ≤ deriv^[2] g t := by
    intro t
    -- The assumed block sign condition gives the second derivative of every line restriction.
    rw [xLine_secondDeriv (hf := hf) (x := x) (y := y) (z := z) (t := t)]
    exact hxx (AffineMap.lineMap x y t) (y - x)
  have h_g_conv : ConvexOn ℝ Set.univ g := by
    -- A `C²` one-variable function with nonnegative second derivative is convex.
    exact convexOn_univ_of_deriv2_nonneg
      h_g_c1.differentiable_one
      h_g_smooth.differentiable_deriv_two
      h_g_second_nonneg
  have h0 : (0 : ℝ) ∈ Set.univ := by
    simp
  have h1 : (1 : ℝ) ∈ Set.univ := by
    simp
  have hcoeff : 1 - b / (a + b) = a / (a + b) := by
    field_simp [hab.ne']
    ring
  have h_line := ((convexOn_iff_div).1 h_g_conv).2 h0 h1 ha hb hab
  -- Evaluating the convex line inequality at `0`, `1`, and `b / (a + b)` yields the slice inequality.
  simpa [g, hcoeff, AffineMap.lineMap_apply_module, smul_eq_mul] using h_line

/-- A fixed-`x` slice is concave once every second directional derivative in the `z`-variable is
nonpositive. -/
lemma concave_zSlice_of_secondDirectional_nonpos
    {n m : ℕ}
    {f : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → ℝ}
    (hf : ContDiff ℝ 2 f)
    (x : EuclideanSpace ℝ (Fin n))
    (hzz :
      ∀ z w : EuclideanSpace ℝ (Fin m),
        (fderiv ℝ
          (fun z0 : EuclideanSpace ℝ (Fin m) =>
            (fderiv ℝ (fun z1 : EuclideanSpace ℝ (Fin m) => f (x, z1)) z0) w)
          z) w ≤ 0) :
    ConcaveOn ℝ Set.univ (fun z : EuclideanSpace ℝ (Fin m) => f (x, z)) := by
  rw [concaveOn_iff_div]
  refine ⟨convex_univ, ?_⟩
  intro z₁ hz₁ z₂ hz₂ a b ha hb hab
  let g : ℝ → ℝ := fun t => f (x, AffineMap.lineMap z₁ z₂ t)
  have hone : (1 : WithTop ℕ∞) ≤ 2 := by
    norm_num
  have h_g_smooth : ContDiff ℝ 2 g := by
    -- The affine-line restriction of a `C²` slice is still `C²`.
    have h_slice : ContDiff ℝ 2 (fun z0 : EuclideanSpace ℝ (Fin m) => f (x, z0)) := by
      exact contDiff_zSlice (hf := hf) x
    have h_line : ContDiff ℝ 2 (fun t : ℝ => AffineMap.lineMap z₁ z₂ t) := by
      simpa [ContinuousAffineMap.coe_lineMap_eq] using
        (ContinuousAffineMap.lineMap (R := ℝ) z₁ z₂).contDiff (n := (2 : WithTop ℕ∞))
    simpa [g] using h_slice.comp h_line
  have h_g_c1 : ContDiff ℝ 1 g := by
    exact h_g_smooth.of_le hone
  have h_g_second_nonpos : ∀ t : ℝ, deriv^[2] g t ≤ 0 := by
    intro t
    -- The assumed block sign condition gives the second derivative of every line restriction.
    rw [zLine_secondDeriv (hf := hf) (x := x) (z₁ := z₁) (z₂ := z₂) (t := t)]
    exact hzz (AffineMap.lineMap z₁ z₂ t) (z₂ - z₁)
  have h_g_conc : ConcaveOn ℝ Set.univ g := by
    -- A `C²` one-variable function with nonpositive second derivative is concave.
    exact concaveOn_univ_of_deriv2_nonpos
      h_g_c1.differentiable_one
      h_g_smooth.differentiable_deriv_two
      h_g_second_nonpos
  have h0 : (0 : ℝ) ∈ Set.univ := by
    simp
  have h1 : (1 : ℝ) ∈ Set.univ := by
    simp
  have hcoeff : 1 - b / (a + b) = a / (a + b) := by
    field_simp [hab.ne']
    ring
  have h_line := ((concaveOn_iff_div).1 h_g_conc).2 h0 h1 ha hb hab
  -- Evaluating the concave line inequality at `0`, `1`, and `b / (a + b)` yields the slice inequality.
  simpa [g, hcoeff, AffineMap.lineMap_apply_module, smul_eq_mul] using h_line

/- 
Let f: ℝ^n \times ℝ^m o ℝ and f ∈ C^2. Define: if for every fixed z ∈ ℝ^m, the function x mapsto
f(x,
z) is convex on ℝ^n; and for every fixed x ∈ ℝ^n, the function z mapsto f(x, z) is concave on ℝ^m,
then f is called a convex - - concave function with respect to (x, z). Prove the following
equivalence:
f is a convex - - concave function with respect to (x, z) if and only if for every (x, z) ∈ ℝ^n
\times
ℝ^m, one has abla_{xx}^2 f(x, z) succeq 0, abla_{zz}^2 f(x, z) preceq 0. Here, abla_{xx}^2 f(x, z)
succeq 0 means that the Hessian matrix with respect to x is positive semidefinite, and abla_{zz}^2
f(x, z) preceq 0 means that the Hessian matrix with respect to z is negative semidefinite.
-/
theorem convexConcave_iff_hessian_blocks_semidefinite
    {n m : ℕ}
    {f : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → ℝ}
    (hf : ContDiff ℝ 2 f) :
    ((
      ∀ z : EuclideanSpace ℝ (Fin m),
        ConvexOn ℝ Set.univ (fun x : EuclideanSpace ℝ (Fin n) => f (x, z))) ∧
      (∀ x : EuclideanSpace ℝ (Fin n),
        ConcaveOn ℝ Set.univ (fun z : EuclideanSpace ℝ (Fin m) => f (x, z)))
    ) ↔
    (∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m),
      (∀ v : EuclideanSpace ℝ (Fin n),
        0 ≤
          (fderiv ℝ
            (fun x : EuclideanSpace ℝ (Fin n) =>
              (fderiv ℝ (fun x' : EuclideanSpace ℝ (Fin n) => f (x', p.2)) x) v)
            p.1) v) ∧
      (∀ w : EuclideanSpace ℝ (Fin m),
        (fderiv ℝ
          (fun z : EuclideanSpace ℝ (Fin m) =>
            (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin m) => f (p.1, z')) z) w)
          p.2) w ≤ 0)) := by
  constructor
  · intro h_convexConcave
    rcases h_convexConcave with ⟨hx_conv, hz_conc⟩
    intro p
    constructor
    · intro v
      let g : ℝ → ℝ := fun t => f (AffineMap.lineMap p.1 (p.1 + v) t, p.2)
      have hone : (1 : WithTop ℕ∞) ≤ 2 := by
        norm_num
      have h_g_smooth : ContDiff ℝ 2 g := by
        -- Restricting the fixed-`z` slice to an affine line preserves `C²` regularity.
        have h_slice : ContDiff ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) => f (x, p.2)) := by
          exact contDiff_xSlice (hf := hf) p.2
        have h_line : ContDiff ℝ 2 (fun t : ℝ => AffineMap.lineMap p.1 (p.1 + v) t) := by
          simpa [ContinuousAffineMap.coe_lineMap_eq] using
            (ContinuousAffineMap.lineMap (R := ℝ) p.1 (p.1 + v)).contDiff
              (n := (2 : WithTop ℕ∞))
        simpa [g] using h_slice.comp h_line
      have h_g_c1 : ContDiff ℝ 1 g := by
        exact h_g_smooth.of_le hone
      have h_g_conv : ConvexOn ℝ Set.univ g := by
        -- Convexity of the fixed-`z` slice transfers to every affine line.
        simpa [g] using
          (hx_conv p.2).comp_affineMap (AffineMap.lineMap p.1 (p.1 + v))
      have h_diff : ∀ t ∈ Set.univ, DifferentiableAt ℝ g t := by
        intro t ht
        exact h_g_c1.differentiable_one t
      have h_mono : Monotone (deriv g) := by
        -- A convex one-variable `C¹` function has monotone derivative.
        exact monotoneOn_univ.mp (h_g_conv.monotoneOn_deriv h_diff)
      have h_second_nonneg : 0 ≤ deriv^[2] g 0 := by
        -- The derivative of a monotone function is nonnegative.
        change 0 ≤ deriv (deriv g) 0
        exact h_mono.deriv_nonneg
      -- Route correction: instead of converting to `iteratedFDeriv`, differentiate the line
      -- restriction twice and rewrite it directly as the nested `fderiv` expression from the goal.
      rw [xLine_secondDeriv (hf := hf) (x := p.1) (y := p.1 + v) (z := p.2) (t := 0)] at h_second_nonneg
      simpa [AffineMap.lineMap_apply_zero] using h_second_nonneg
    · intro w
      let g : ℝ → ℝ := fun t => f (p.1, AffineMap.lineMap p.2 (p.2 + w) t)
      have hone : (1 : WithTop ℕ∞) ≤ 2 := by
        norm_num
      have h_g_smooth : ContDiff ℝ 2 g := by
        -- Restricting the fixed-`x` slice to an affine line preserves `C²` regularity.
        have h_slice : ContDiff ℝ 2 (fun z : EuclideanSpace ℝ (Fin m) => f (p.1, z)) := by
          exact contDiff_zSlice (hf := hf) p.1
        have h_line : ContDiff ℝ 2 (fun t : ℝ => AffineMap.lineMap p.2 (p.2 + w) t) := by
          simpa [ContinuousAffineMap.coe_lineMap_eq] using
            (ContinuousAffineMap.lineMap (R := ℝ) p.2 (p.2 + w)).contDiff
              (n := (2 : WithTop ℕ∞))
        simpa [g] using h_slice.comp h_line
      have h_g_c1 : ContDiff ℝ 1 g := by
        exact h_g_smooth.of_le hone
      have h_g_conc : ConcaveOn ℝ Set.univ g := by
        -- Concavity of the fixed-`x` slice transfers to every affine line.
        simpa [g] using
          (hz_conc p.1).comp_affineMap (AffineMap.lineMap p.2 (p.2 + w))
      have h_diff : ∀ t ∈ Set.univ, DifferentiableAt ℝ g t := by
        intro t ht
        exact h_g_c1.differentiable_one t
      have h_anti : Antitone (deriv g) := by
        -- A concave one-variable `C¹` function has antitone derivative.
        exact antitoneOn_univ.mp (h_g_conc.antitoneOn_deriv h_diff)
      have h_second_nonpos : deriv^[2] g 0 ≤ 0 := by
        -- The derivative of an antitone function is nonpositive.
        change deriv (deriv g) 0 ≤ 0
        exact h_anti.deriv_nonpos
      -- Route correction: instead of converting to `iteratedFDeriv`, differentiate the line
      -- restriction twice and rewrite it directly as the nested `fderiv` expression from the goal.
      rw [zLine_secondDeriv (hf := hf) (x := p.1) (z₁ := p.2) (z₂ := p.2 + w) (t := 0)] at h_second_nonpos
      simpa [AffineMap.lineMap_apply_zero] using h_second_nonpos
  · intro h_blocks
    constructor
    · intro z
      -- The x-slice is convex because every line restriction has nonnegative second derivative.
      refine convex_xSlice_of_secondDirectional_nonneg (hf := hf) (z := z) ?_
      intro x v
      exact (h_blocks (x, z)).1 v
    · intro x
      -- The z-slice is concave because every line restriction has nonpositive second derivative.
      refine concave_zSlice_of_secondDirectional_nonpos (hf := hf) (x := x) ?_
      intro z w
      exact (h_blocks (x, z)).2 w

end «problem-27»
