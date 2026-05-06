import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-134»
/-
Let f: ℝ^n o ℝ be twice differentiable, and assume that dom f ⊆ ℝ^n is convex. Let F ∈ ℝ^{n \times
m}
and x ∈ ℝ^n. Define ilde f: ℝ^m o ℝ by ilde f(z) = f(Fz + x), dom ilde f = {z∈ℝ^m| Fz + x∈dom f}.
For a
symmetric matrix M, write Msucceq 0 if uᵀ M u ≥ 0 for all u∈ℝ^m. Prove that ilde f is convex on dom
ilde f if and only if for every z∈dom ilde f, Fᵀ abla^2 f(Fz + x)Fsucceq 0.
-/
open scoped Matrix

/-- Restricting a differentiable function to an affine line differentiates in the line direction. -/
lemma hasDerivAt_lineMap_apply_fderiv
    {ι : Type*} [Fintype ι] [DecidableEq ι] {g : (ι → ℝ) → ℝ} {x y : ι → ℝ} {t : ℝ}
    (hg : DifferentiableAt ℝ g (AffineMap.lineMap x y t)) :
    HasDerivAt (fun s => g (AffineMap.lineMap x y s))
      (fderiv ℝ g (AffineMap.lineMap x y t) (y - x)) t := by
  -- Compose the derivative of `g` with the standard derivative of the affine line map.
  exact hg.hasFDerivAt.comp_hasDerivAt t (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t))

/-- Applying the derivative map to a constant vector recovers the corresponding entry of the
second Fréchet derivative. -/
lemma fderiv_apply_const_eq_fderiv_fderiv
    {ι : Type*} [Fintype ι] [DecidableEq ι] {g : (ι → ℝ) → ℝ} {x v w : ι → ℝ}
    (hg2 : ContDiffAt ℝ 2 g x) :
    (fderiv ℝ (fun y => (fderiv ℝ g y) w) x) v = fderiv ℝ (fderiv ℝ g) x v w := by
  -- Differentiate the CLM-valued map `fderiv g` and then evaluate it at the fixed vector `w`.
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ g) x := (hg2.fderiv_right_succ).differentiableAt_one
  have hclm :
      fderiv ℝ (fun y => (fderiv ℝ g y) w) x =
        (fderiv ℝ (fderiv ℝ g) x).flip w := by
    simpa using
      fderiv_clm_apply (c := fderiv ℝ g) (u := fun _ : ι → ℝ => w) (x := x) hfdiff
        (differentiableAt_const w)
  -- Evaluate the resulting continuous linear map at the ambient direction `v`.
  simpa using congrArg (fun A => A v) hclm

/-- The second derivative of a line restriction is the Hessian evaluated twice on the line
direction. -/
lemma hasDerivAt_lineMap_apply_iteratedFDeriv
    {ι : Type*} [Fintype ι] [DecidableEq ι] {g : (ι → ℝ) → ℝ} {x y : ι → ℝ} {t : ℝ}
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
  -- Rewrite the derivative of the directional derivative as the diagonal iterated derivative.
  rw [fderiv_apply_const_eq_fderiv_fderiv (g := g) (x := AffineMap.lineMap x y t) (v := y - x)
      (w := y - x) hg2]
  simp [iteratedFDeriv_two_apply]

/-- The coordinate quadratic form in the Hessian coordinates is the diagonal evaluation of the
second Fréchet derivative. -/
lemma coordinateQuadraticForm_eq_iteratedFDeriv_diag
    {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℝ} {x z : ι → ℝ}
    (hf2 : ContDiffAt ℝ 2 f x) :
    ∑ i : ι, z i *
      ∑ j : ι, z j *
        ((fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) x)
          (Pi.single i (1 : ℝ))) =
      iteratedFDeriv ℝ 2 f x ![z, z] := by
  -- Expand the bilinear second derivative in the standard basis of the finite-dimensional space.
  have hentry (i j : ι) :
      (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) x) (Pi.single i (1 : ℝ)) =
        ((fderiv ℝ (fderiv ℝ f) x) (Pi.single i (1 : ℝ))) (Pi.single j (1 : ℝ)) := by
    simpa using
      fderiv_apply_const_eq_fderiv_fderiv (g := f) (x := x) (v := Pi.single i (1 : ℝ))
        (w := Pi.single j (1 : ℝ)) hf2
  calc
    ∑ i : ι, z i *
      ∑ j : ι, z j *
        ((fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) x)
          (Pi.single i (1 : ℝ))) =
      bilinearIteratedFDerivTwo ℝ f x z z := by
        simpa [dotProduct, Matrix.mulVec, bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
          iteratedFDeriv_two_apply, hentry,
          mul_assoc, mul_left_comm, mul_comm] using
          (apply_eq_dotProduct_toMatrix₂_mulVec (b₁ := Pi.basisFun ℝ ι)
            (b₂ := Pi.basisFun ℝ ι) (B := bilinearIteratedFDerivTwo ℝ f x) z z).symm
    _ = iteratedFDeriv ℝ 2 f x ![z, z] := by
      rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv]

/-- Convexity on an open set forces every directional second derivative to be nonnegative. -/
lemma directionalSecond_nonneg_of_convexOn
    {ι : Type*} [Fintype ι] [DecidableEq ι] {C : Set (ι → ℝ)} {f : (ι → ℝ) → ℝ}
    (hCopen : IsOpen C)
    (hC2 : ∀ x ∈ C, ContDiffAt ℝ 2 f x)
    (hf : ConvexOn ℝ C f) :
    ∀ x ∈ C, ∀ u : ι → ℝ, 0 ≤ iteratedFDeriv ℝ 2 f x ![u, u] := by
  intro x hx u
  let L : ℝ →ᵃ[ℝ] (ι → ℝ) := AffineMap.lineMap x (x + u)
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
    {ι : Type*} [Fintype ι] [DecidableEq ι] {C : Set (ι → ℝ)} {f : (ι → ℝ) → ℝ}
    (hCconv : Convex ℝ C)
    (hCopen : IsOpen C)
    (hC2 : ∀ x ∈ C, ContDiffAt ℝ 2 f x)
    (hdir : ∀ x ∈ C, ∀ u : ι → ℝ, 0 ≤ iteratedFDeriv ℝ 2 f x ![u, u]) :
    ConvexOn ℝ C f := by
  rw [convexOn_iff_forall_pos]
  refine ⟨hCconv, ?_⟩
  intro x hx y hy a b ha hb hab
  let L : ℝ →ᵃ[ℝ] (ι → ℝ) := AffineMap.lineMap x y
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

/-- On an open convex finite-dimensional domain, convexity is equivalent to nonnegativity of the
Hessian quadratic form in coordinates. -/
lemma convexOn_iff_hessian_quadratic_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι] {C : Set (ι → ℝ)} {f : (ι → ℝ) → ℝ}
    (hCconv : Convex ℝ C)
    (hCopen : IsOpen C)
    (hC2 : ∀ x ∈ C, ContDiffAt ℝ 2 f x) :
    ConvexOn ℝ C f ↔
      ∀ x ∈ C, ∀ z : ι → ℝ,
        0 ≤
          ∑ i : ι, z i *
            ∑ j : ι,
              z j *
                ((fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) x)
                  (Pi.single i (1 : ℝ))) := by
  constructor
  · -- Convexity gives nonnegative directional second derivatives, then the coordinate formula rewrites.
    intro hf x hx z
    simpa [coordinateQuadraticForm_eq_iteratedFDeriv_diag (f := f) (x := x) (z := z) (hC2 x hx)]
      using directionalSecond_nonneg_of_convexOn hCopen hC2 hf x hx z
  · intro hquad
    -- Rewrite the coordinate assumption as directional Hessian nonnegativity and apply the
    -- one-dimensional line-restriction criterion on every affine line.
    have hdir : ∀ x ∈ C, ∀ u : ι → ℝ, 0 ≤ iteratedFDeriv ℝ 2 f x ![u, u] := by
      intro x hx u
      simpa [coordinateQuadraticForm_eq_iteratedFDeriv_diag (f := f) (x := x) (z := u) (hC2 x hx)]
        using hquad x hx u
    exact convexOn_of_directionalSecond_nonneg hCconv hCopen hC2 hdir

/-- The diagonal second derivative of the affine pullback is the quadratic form associated to the
pulled-back Hessian matrix. -/
lemma affine_precomp_iteratedFDeriv_diag_eq_pullback_quadratic
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (f : (n → ℝ) → ℝ) (F : Matrix n m ℝ) (xhat : n → ℝ) (z u : m → ℝ)
    (hf2 : ContDiffAt ℝ 2 f (fun i => (∑ j, F i j * z j) + xhat i)) :
    iteratedFDeriv ℝ 2 (fun w : m → ℝ => f (fun i => (∑ j, F i j * w j) + xhat i)) z ![u, u] =
      ∑ i : m, u i *
        ∑ j : m,
          ((F.transpose *
              Matrix.of (fun i j : n =>
                fderiv ℝ
                  (fun y : n → ℝ => (fderiv ℝ f y) (Pi.single j (1 : ℝ)))
                  (fun k => (∑ l, F k l * z l) + xhat k)
                  (Pi.single i (1 : ℝ))) * F) i j) * u j := by
  let L : (m → ℝ) →L[ℝ] (n → ℝ) := (Matrix.toLin' F).toContinuousLinearMap
  let fshift : (n → ℝ) → ℝ := fun y => f (y + xhat)
  let hess : Matrix n n ℝ :=
    Matrix.of (fun i j : n =>
      fderiv ℝ
        (fun y : n → ℝ => (fderiv ℝ f y) (Pi.single j (1 : ℝ)))
        (fun k => (∑ l, F k l * z l) + xhat k)
        (Pi.single i (1 : ℝ)))
  have hfshift : ContDiffAt ℝ 2 fshift (L z) := by
    -- Shift the base point by `xhat` before using the ambient `C²` hypothesis on `f`.
    have htrans : ContDiffAt ℝ 2 (fun y : n → ℝ => y + xhat) (L z) := by
      fun_prop
    simpa [fshift, Matrix.toLin'_apply, add_comm, add_left_comm, add_assoc] using
      hf2.comp (L z) htrans
  have hcomp :
      iteratedFDeriv ℝ 2 (fshift ∘ L) z =
        (iteratedFDeriv ℝ 2 fshift (L z)).compContinuousLinearMap (fun _ : Fin 2 => L) := by
    -- Route correction: use a local `ContDiffOn` neighborhood and the within-version composition
    -- formula, since the global `iteratedFDeriv_comp_right` theorem requires global smoothness.
    rcases hfshift.contDiffOn (m := (2 : WithTop ℕ∞)) le_rfl (by intro h; simpa using h) with
      ⟨s, hsnhds, hfs⟩
    rcases mem_nhds_iff.mp hsnhds with ⟨o, hos, ho_open, hzo⟩
    have hfo : ContDiffOn ℝ 2 fshift o := hfs.mono hos
    have hzpre : z ∈ L ⁻¹' o := by
      simpa [L] using hzo
    have hwithin :
        iteratedFDerivWithin ℝ 2 (fshift ∘ L) (L ⁻¹' o) z =
          (iteratedFDerivWithin ℝ 2 fshift o (L z)).compContinuousLinearMap (fun _ : Fin 2 => L) :=
      L.iteratedFDerivWithin_comp_right (f := fshift) (s := o) hfo ho_open.uniqueDiffOn
        ((ho_open.preimage L.continuous).uniqueDiffOn) hzo (hi := le_rfl)
    have hleft :
        iteratedFDerivWithin ℝ 2 (fshift ∘ L) (L ⁻¹' o) z =
          iteratedFDeriv ℝ 2 (fshift ∘ L) z := by
      apply iteratedFDerivWithin_eq_iteratedFDeriv ((ho_open.preimage L.continuous).uniqueDiffOn)
      have hL : ContDiffAt ℝ 2 L z := by
        simpa using (L.contDiff.contDiffAt : ContDiffAt ℝ 2 L z)
      simpa [Function.comp, L] using hfshift.comp z hL
      exact hzpre
    have hright :
        iteratedFDerivWithin ℝ 2 fshift o (L z) = iteratedFDeriv ℝ 2 fshift (L z) := by
      apply iteratedFDerivWithin_eq_iteratedFDeriv ho_open.uniqueDiffOn hfshift
      exact hzo
    exact hleft.symm.trans (hwithin.trans (by rw [hright]))
  have hshift :
      iteratedFDeriv ℝ 2 fshift (L z) =
        iteratedFDeriv ℝ 2 f (fun i => (∑ j, F i j * z j) + xhat i) := by
    -- Translation does not change iterated derivatives beyond shifting the base point.
    simpa [fshift, L, Matrix.toLin'_apply, add_comm, add_left_comm, add_assoc] using
      (iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f) 2 xhat (L z))
  have hmatrix :
      Matrix.toLinearMap₂' ℝ (F.transpose * hess * F) u u =
        Matrix.toLinearMap₂' ℝ hess ((Matrix.toLin' F) u) ((Matrix.toLin' F) u) := by
    -- Compose the Hessian bilinear form with the matrix linear map on both slots.
    simpa [LinearMap.compl₁₂, Matrix.toLin'_apply] using
      (congrArg (fun B => B u u)
        (Matrix.toLinearMap₂'_comp (R := ℝ) (M := hess) (P := F) (Q := F))).symm
  have hpullbackFun :
      (fun w : m → ℝ => f (fun i => (∑ j, F i j * w j) + xhat i)) = fshift ∘ L := by
    -- The affine pullback is the translated linear map `L` followed by `f`.
    funext w
    have hw : (fun i => (∑ j, F i j * w j) + xhat i) = F *ᵥ w + xhat := by
      ext i
      simp [Matrix.mulVec, dotProduct, add_comm, add_left_comm, add_assoc]
    simpa [Function.comp_apply, fshift, L, Matrix.toLin'_apply, add_comm] using congrArg f hw
  calc
    iteratedFDeriv ℝ 2 (fun w : m → ℝ => f (fun i => (∑ j, F i j * w j) + xhat i)) z ![u, u] =
        iteratedFDeriv ℝ 2 (fshift ∘ L) z ![u, u] := by
          rw [hpullbackFun]
    _ = (iteratedFDeriv ℝ 2 fshift (L z)).compContinuousLinearMap (fun _ : Fin 2 => L) ![u, u] := by
          rw [hcomp]
    _ = iteratedFDeriv ℝ 2 fshift (L z) ![(L u), (L u)] := by
          simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
          congr
          ext i
          fin_cases i <;> rfl
    _ = iteratedFDeriv ℝ 2 f (fun i => (∑ j, F i j * z j) + xhat i) ![((Matrix.toLin' F) u),
          ((Matrix.toLin' F) u)] := by
          simpa [L, Matrix.toLin'_apply] using congrArg (fun B => B ![(L u), (L u)]) hshift
    _ = ∑ i : n, ((Matrix.toLin' F) u) i *
          ∑ j : n, ((Matrix.toLin' F) u) j * hess i j := by
          symm
          simpa [hess] using
            coordinateQuadraticForm_eq_iteratedFDeriv_diag
              (f := f) (x := fun i => (∑ j, F i j * z j) + xhat i)
              (z := (Matrix.toLin' F) u) hf2
    _ = Matrix.toLinearMap₂' ℝ hess ((Matrix.toLin' F) u) ((Matrix.toLin' F) u) := by
          simp [Matrix.toLinearMap₂'_apply, Finset.mul_sum, mul_left_comm, mul_comm, hess]
    _ = Matrix.toLinearMap₂' ℝ (F.transpose * hess * F) u u := by
          rw [hmatrix]
    _ = ∑ i : m, u i * ∑ j : m, ((F.transpose * hess * F) i j) * u j := by
          simp [Matrix.toLinearMap₂'_apply, Finset.mul_sum, mul_left_comm, mul_comm, hess]

theorem affine_precomp_convexOn_iff_hessian_pullback_psd
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (domf : Set (n → ℝ)) (f : (n → ℝ) → ℝ) (F : Matrix n m ℝ) (xhat : n → ℝ)
    (hconvex : Convex ℝ domf)
    (hdomf_open : IsOpen domf)
    (hC2 : ∀ x : n → ℝ, x ∈ domf → ContDiffAt ℝ 2 f x) :
    (let dom_tilde : Set (m → ℝ) := {z : m → ℝ | (fun i => (∑ j, F i j * z j) + xhat i) ∈ domf}
     let tilde_f : {z : m → ℝ // z ∈ dom_tilde} → ℝ :=
       fun z => f (fun i => (∑ j, F i j * z.1 j) + xhat i)
     ConvexOn ℝ dom_tilde
       (fun z => f (fun i => (∑ j, F i j * z j) + xhat i)))
      ↔
    (let dom_tilde : Set (m → ℝ) := {z : m → ℝ | (fun i => (∑ j, F i j * z j) + xhat i) ∈ domf}
     let hess : (m → ℝ) → Matrix n n ℝ :=
       fun z =>
         Matrix.of (fun i j : n =>
           fderiv ℝ
             (fun y : n → ℝ => (fderiv ℝ f y) (Pi.single j (1 : ℝ)))
             (fun k => (∑ l, F k l * z l) + xhat k)
             (Pi.single i (1 : ℝ)))
     ∀ z : m → ℝ,
       z ∈ dom_tilde →
       ∀ u : m → ℝ, 0 ≤ ∑ i, u i * ∑ j, ((F.transpose * hess z * F) i j) * u j) := by
  -- Unfold the affine pullback data so the statement becomes a theorem about one explicit function.
  dsimp only
  let A : (m → ℝ) → (n → ℝ) := fun z i => (∑ j, F i j * z j) + xhat i
  let dom_tilde : Set (m → ℝ) := {z : m → ℝ | A z ∈ domf}
  let g : (m → ℝ) → ℝ := fun z => f (A z)
  let hess : (m → ℝ) → Matrix n n ℝ := fun z =>
    Matrix.of (fun i j : n =>
      fderiv ℝ
        (fun y : n → ℝ => (fderiv ℝ f y) (Pi.single j (1 : ℝ)))
        (A z)
        (Pi.single i (1 : ℝ)))
  have hdom_conv : Convex ℝ dom_tilde := by
    -- The pullback domain is the affine preimage of the original convex domain.
    let Aaff : (m → ℝ) →ᵃ[ℝ] (n → ℝ) :=
      (Matrix.toLin' F).toAffineMap +ᵥ AffineMap.const ℝ (m → ℝ) xhat
    simpa [dom_tilde, A, Aaff, Matrix.toLin'_apply, add_comm, add_left_comm, add_assoc] using
      hconvex.affine_preimage Aaff
  have hdom_open : IsOpen dom_tilde := by
    -- Openness is preserved by preimage under the affine map `A`.
    have hAcont : Continuous A := by
      fun_prop
    simpa [dom_tilde, A] using hdomf_open.preimage hAcont
  have hgC2 : ∀ z ∈ dom_tilde, ContDiffAt ℝ 2 g z := by
    intro z hz
    -- The affine pullback inherits the ambient `C²` regularity of `f`.
    have hA2 : ContDiffAt ℝ 2 A z := by
      fun_prop
    simpa [g, A] using (hC2 (A z) hz).comp z hA2
  have hcoord_eq :
      ∀ z ∈ dom_tilde, ∀ u : m → ℝ,
        ∑ i : m, u i *
          ∑ j : m,
            u j *
              ((fderiv ℝ (fun y => (fderiv ℝ g y) (Pi.single j (1 : ℝ))) z)
                (Pi.single i (1 : ℝ))) =
          ∑ i : m, u i * ∑ j : m, ((F.transpose * hess z * F) i j) * u j := by
    intro z hz u
    -- Both coordinate expressions are equal to the same diagonal iterated derivative of `g`.
    calc
      ∑ i : m, u i *
        ∑ j : m,
          u j *
            ((fderiv ℝ (fun y => (fderiv ℝ g y) (Pi.single j (1 : ℝ))) z)
              (Pi.single i (1 : ℝ))) =
          iteratedFDeriv ℝ 2 g z ![u, u] := by
            simpa using coordinateQuadraticForm_eq_iteratedFDeriv_diag
              (f := g) (x := z) (z := u) (hgC2 z hz)
      _ = ∑ i : m, u i * ∑ j : m, ((F.transpose * hess z * F) i j) * u j := by
            simpa [g, hess, A] using
              affine_precomp_iteratedFDeriv_diag_eq_pullback_quadratic f F xhat z u (hC2 (A z) hz)
  constructor
  · intro hgconv z hz u
    -- Apply the generic open-convex Hessian criterion to the pullback function `g`.
    have hquad :=
      (convexOn_iff_hessian_quadratic_nonneg hdom_conv hdom_open hgC2).1 hgconv z hz u
    simpa [hcoord_eq z hz u, mul_left_comm, mul_comm] using hquad
  · intro hpsd
    -- Rewrite the pulled-back Hessian assumption as the coordinate Hessian criterion for `g`.
    refine (convexOn_iff_hessian_quadratic_nonneg hdom_conv hdom_open hgC2).2 ?_
    intro z hz u
    have hquad : 0 ≤ ∑ i : m, u i * ∑ j : m, ((F.transpose * hess z * F) i j) * u j := hpsd z hz u
    simpa [hcoord_eq z hz u, mul_left_comm, mul_comm] using hquad

end «problem-134»
