import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-71»

-- Exercise_3_8

/- [BLOCK Exercise 3.8 | 1 | thm]
Let C⊆ ℝ^n and let f:C→ ℝ be twice differentiable. For a symmetric matrix A, Asucceq 0 means that zᵀ
A z≥ 0 for all z∈ℝ^n. Prove that f is convex on C if and only if C is convex and ∇^2 f(x)succeq 0
for all x∈ C.
-/
open scoped BigOperators

/-- Restricting a differentiable function to an affine line differentiates in the line direction. -/
lemma hasDerivAt_lineMap_apply_fderiv
    {n : ℕ} {g : (Fin n → ℝ) → ℝ} {x y : Fin n → ℝ} {t : ℝ}
    (hg : DifferentiableAt ℝ g (AffineMap.lineMap x y t)) :
    HasDerivAt (fun s => g (AffineMap.lineMap x y s))
      (fderiv ℝ g (AffineMap.lineMap x y t) (y - x)) t := by
  -- Compose the derivative of `g` with the standard derivative of the affine line map.
  exact hg.hasFDerivAt.comp_hasDerivAt t (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t))

/-- Applying the derivative map to a constant vector recovers the corresponding entry of the
second Fréchet derivative. -/
lemma fderiv_apply_const_eq_fderiv_fderiv
    {n : ℕ} {g : (Fin n → ℝ) → ℝ} {x v w : Fin n → ℝ}
    (hg2 : ContDiffAt ℝ 2 g x) :
    (fderiv ℝ (fun y => (fderiv ℝ g y) w) x) v = fderiv ℝ (fderiv ℝ g) x v w := by
  -- Differentiate the CLM-valued map `fderiv g` and then evaluate it at the fixed vector `w`.
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ g) x := (hg2.fderiv_right_succ).differentiableAt_one
  have hclm :
      fderiv ℝ (fun y => (fderiv ℝ g y) w) x =
        (fderiv ℝ (fderiv ℝ g) x).flip w := by
    simpa using
      fderiv_clm_apply (c := fderiv ℝ g) (u := fun _ : Fin n → ℝ => w) (x := x) hfdiff
        (differentiableAt_const w)
  simpa using congrArg (fun A => A v) hclm

/-- The second derivative of a line restriction is the Hessian evaluated twice on the line
direction. -/
lemma hasDerivAt_lineMap_apply_iteratedFDeriv
    {n : ℕ} {g : (Fin n → ℝ) → ℝ} {x y : Fin n → ℝ} {t : ℝ}
    (hg2 : ContDiffAt ℝ 2 g (AffineMap.lineMap x y t)) :
    HasDerivAt (fun s => (fderiv ℝ g (AffineMap.lineMap x y s)) (y - x))
      (iteratedFDeriv ℝ 2 g (AffineMap.lineMap x y t) ![y - x, y - x]) t := by
  -- Differentiate the scalar directional-derivative function along the same affine line.
  have hdiff :
      DifferentiableAt ℝ (fun z => (fderiv ℝ g z) (y - x)) (AffineMap.lineMap x y t) := by
    exact ((hg2.fderiv_right_succ).clm_apply contDiffAt_const).differentiableAt_one
  convert
      hasDerivAt_lineMap_apply_fderiv
        (g := fun z => (fderiv ℝ g z) (y - x)) (x := x) (y := y) (t := t) hdiff using 1
  rw [fderiv_apply_const_eq_fderiv_fderiv (g := g) (x := AffineMap.lineMap x y t) (v := y - x)
      (w := y - x) hg2]
  simp [iteratedFDeriv_two_apply]

/-- The coordinate quadratic form in the statement is the diagonal evaluation of the second
Fréchet derivative. -/
lemma coordinateQuadraticForm_eq_iteratedFDeriv_diag
    {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x z : Fin n → ℝ}
    (hf2 : ContDiffAt ℝ 2 f x) :
    ∑ i : Fin n, z i *
      ∑ j : Fin n, z j *
        ((fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) x)
          (Pi.single i (1 : ℝ))) =
      iteratedFDeriv ℝ 2 f x ![z, z] := by
  -- Expand the bilinear second derivative in the standard basis of `ℝ^n`.
  have hentry (i j : Fin n) :
      (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) x) (Pi.single i (1 : ℝ)) =
        ((fderiv ℝ (fderiv ℝ f) x) (Pi.single i (1 : ℝ))) (Pi.single j (1 : ℝ)) := by
    simpa using
      fderiv_apply_const_eq_fderiv_fderiv (g := f) (x := x) (v := Pi.single i (1 : ℝ))
        (w := Pi.single j (1 : ℝ)) hf2
  calc
    ∑ i : Fin n, z i *
      ∑ j : Fin n, z j *
        ((fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) x)
          (Pi.single i (1 : ℝ))) =
      bilinearIteratedFDerivTwo ℝ f x z z := by
        simpa [dotProduct, Matrix.mulVec, bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
          iteratedFDeriv_two_apply, hentry,
          mul_assoc, mul_left_comm, mul_comm] using
          (apply_eq_dotProduct_toMatrix₂_mulVec (b₁ := Pi.basisFun ℝ (Fin n))
            (b₂ := Pi.basisFun ℝ (Fin n)) (B := bilinearIteratedFDerivTwo ℝ f x) z z).symm
    _ = iteratedFDeriv ℝ 2 f x ![z, z] := by
      rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv]

/-- Convexity on an open set forces every directional second derivative to be nonnegative. -/
lemma directionalSecond_nonneg_of_convexOn
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hCopen : IsOpen C)
    (hC2 : ∀ x ∈ C, ContDiffAt ℝ 2 f x)
    (hf : ConvexOn ℝ C f) :
    ∀ x ∈ C, ∀ u : Fin n → ℝ, 0 ≤ iteratedFDeriv ℝ 2 f x ![u, u] := by
  intro x hx u
  let L : ℝ →ᵃ[ℝ] (Fin n → ℝ) := AffineMap.lineMap x (x + u)
  let D : Set ℝ := L ⁻¹' C
  let g : ℝ → ℝ := f ∘ L
  have hLcont : Continuous L := by
    fun_prop
  have hDopen : IsOpen D := hCopen.preimage hLcont
  have hzero : 0 ∈ D := by
    -- The base point of the line restriction is exactly `x`.
    simpa [D, L] using hx
  have hderivEq : D.EqOn (deriv g) (fun t => (fderiv ℝ f (L t)) u) := by
    -- The derivative of the line restriction is the ambient derivative applied to `u`.
    refine deriv_eqOn hDopen ?_
    intro t ht
    have ht1 : ContDiffAt ℝ 1 f (L t) := (hC2 (L t) ht).of_le (by norm_num)
    simpa [g, L] using
      (hasDerivAt_lineMap_apply_fderiv (g := f) (x := x) (y := x + u) (t := t)
        ht1.differentiableAt_one).hasDerivWithinAt
  have hconv : ConvexOn ℝ D g := hf.comp_affineMap L
  have hmono : MonotoneOn (deriv g) D := by
    -- Convexity of the line restriction makes its derivative monotone on the preimage domain.
    refine hconv.monotoneOn_deriv ?_
    intro t ht
    exact (hasDerivAt_lineMap_apply_fderiv (g := f) (x := x) (y := x + u) (t := t)
      ((hC2 (L t) ht).of_le (by norm_num)).differentiableAt_one).differentiableAt
  have hsecondWithin :
      HasDerivWithinAt (deriv g) (iteratedFDeriv ℝ 2 f x ![u, u]) D 0 := by
    -- At the base point, the derivative of `deriv g` is the diagonal Hessian value.
    have hraw :
        HasDerivAt (fun s => (fderiv ℝ f (L s)) u) (iteratedFDeriv ℝ 2 f x ![u, u]) 0 := by
      simpa [L] using
        hasDerivAt_lineMap_apply_iteratedFDeriv (g := f) (x := x) (y := x + u) (t := 0)
          (by simpa [L] using hC2 x hx)
    exact hraw.hasDerivWithinAt.congr_of_mem (fun s hs => hderivEq hs) hzero
  -- A monotone derivative has nonnegative derivative at interior points of the open preimage.
  simpa [hsecondWithin.derivWithin (hDopen.uniqueDiffWithinAt hzero)] using
    (hmono.derivWithin_nonneg (x := 0))

/-- Nonnegativity of all directional second derivatives on an open convex set implies convexity. -/
lemma convexOn_of_directionalSecond_nonneg
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hCconv : Convex ℝ C)
    (hCopen : IsOpen C)
    (hC2 : ∀ x ∈ C, ContDiffAt ℝ 2 f x)
    (hdir : ∀ x ∈ C, ∀ u : Fin n → ℝ, 0 ≤ iteratedFDeriv ℝ 2 f x ![u, u]) :
    ConvexOn ℝ C f := by
  rw [convexOn_iff_forall_pos]
  refine ⟨hCconv, ?_⟩
  intro x hx y hy a b ha hb hab
  let L : ℝ →ᵃ[ℝ] (Fin n → ℝ) := AffineMap.lineMap x y
  let D : Set ℝ := L ⁻¹' C
  let g : ℝ → ℝ := f ∘ L
  let g' : ℝ → ℝ := fun t => (fderiv ℝ f (L t)) (y - x)
  let g'' : ℝ → ℝ := fun t => iteratedFDeriv ℝ 2 f (L t) ![y - x, y - x]
  have hDconv : Convex ℝ D := hCconv.affine_preimage L
  have hLcont : Continuous L := by
    fun_prop
  have hDopen : IsOpen D := hCopen.preimage hLcont
  have hzero : 0 ∈ D := by
    -- The endpoints of the segment map back to the original points.
    simpa [D, L] using hx
  have hone : 1 ∈ D := by
    simpa [D, L] using hy
  have hcont : ContinuousOn g D := by
    -- Along the affine line, pointwise `C²` regularity gives continuity of the restriction.
    intro t ht
    exact ((hC2 (L t) ht).continuousAt.comp hLcont.continuousAt).continuousWithinAt
  have hg' : ∀ t ∈ D, HasDerivWithinAt g (g' t) D t := by
    -- The first derivative of the line restriction is the ambient directional derivative.
    intro t ht
    have ht1 : ContDiffAt ℝ 1 f (L t) := (hC2 (L t) ht).of_le (by norm_num)
    simpa [g, g', L] using
      (hasDerivAt_lineMap_apply_fderiv (g := f) (x := x) (y := y) (t := t)
        ht1.differentiableAt_one).hasDerivWithinAt
  have hg'' : ∀ t ∈ D, HasDerivWithinAt g' (g'' t) D t := by
    -- The second derivative of the line restriction is the diagonal Hessian value.
    intro t ht
    simpa [g', g'', L] using
      (hasDerivAt_lineMap_apply_iteratedFDeriv (g := f) (x := x) (y := y) (t := t)
        (hC2 (L t) ht)).hasDerivWithinAt
  have hnonneg : ∀ t ∈ D, 0 ≤ g'' t := by
    -- The assumed directional nonnegativity applies to the segment direction `y - x`.
    intro t ht
    simpa [g'', L] using hdir (L t) ht (y - x)
  have hconvg : ConvexOn ℝ D g := by
    -- Apply the one-dimensional second-derivative criterion on the open preimage domain.
    refine convexOn_of_hasDerivWithinAt2_nonneg (D := D) (f := g) (f' := g') (f'' := g'') hDconv
      hcont ?_ ?_ ?_
    · intro t ht
      simpa [hDopen.interior_eq] using hg' t (by simpa [hDopen.interior_eq] using ht)
    · intro t ht
      simpa [hDopen.interior_eq] using hg'' t (by simpa [hDopen.interior_eq] using ht)
    · intro t ht
      simpa [hDopen.interior_eq] using hnonneg t (by simpa [hDopen.interior_eq] using ht)
  have ha' : 1 - b = a := by
    linarith
  -- Evaluate the convexity inequality for the line restriction at `0` and `1`.
  simpa [g, L, AffineMap.lineMap_apply_module, ha', hab] using hconvg.2 hzero hone ha.le hb.le hab

theorem convexOn_iff_convex_and_hessian_posSemidef
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hCconv : Convex ℝ C)
    (hCopen : IsOpen C)
    (_hC2 : ∀ x ∈ C, ContDiffAt ℝ 2 f x) :
    ConvexOn ℝ C f ↔
      ∀ x ∈ C, ∀ z : Fin n → ℝ,
        0 ≤
          ∑ i : Fin n, z i *
            ∑ j : Fin n,
              z j *
                ((fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) x)
                  (Pi.single i (1 : ℝ))) := by
  constructor
  · -- Convexity gives nonnegative diagonal Hessian values, then the coordinate formula rewrites.
    intro hf x hx z
    simpa [coordinateQuadraticForm_eq_iteratedFDeriv_diag (f := f) (x := x) (z := z) (_hC2 x hx)]
      using directionalSecond_nonneg_of_convexOn hCopen _hC2 hf x hx z
  · intro hquad
    -- Rewrite the coordinate assumption as directional Hessian nonnegativity and apply the
    -- one-dimensional line-restriction criterion on every affine line.
    have hdir : ∀ x ∈ C, ∀ u : Fin n → ℝ, 0 ≤ iteratedFDeriv ℝ 2 f x ![u, u] := by
      intro x hx u
      simpa [coordinateQuadraticForm_eq_iteratedFDeriv_diag (f := f) (x := x) (z := u) (_hC2 x hx)]
        using hquad x hx u
    exact convexOn_of_directionalSecond_nonneg hCconv hCopen _hC2 hdir

end «problem-71»
