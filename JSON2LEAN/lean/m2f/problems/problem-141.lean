import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-141»

/- [BLOCK Exercise 11.16-(d) | 39 | defn]
A cone K ⊆ ℝ^n is called proper if it is convex, closed, has nonempty interior, and is pointed,
i.e., K cap (-K) = {0}.
-/
def IsProperCone {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  (∀ ⦃x : Fin n → ℝ⦄, x ∈ K → ∀ ⦃a : ℝ⦄, 0 ≤ a → a • x ∈ K) ∧
  Convex ℝ K ∧
  IsClosed K ∧
  (Set.Nonempty (interior K)) ∧
  K ∩ (-K) = ({0} : Set (Fin n → ℝ))

/- [BLOCK Exercise 11.16-(d) | 40 | defn]
Let K ⊆ ℝ^n be a proper cone. A function psi : int K → ℝ is called a generalized logarithm for
K of degree θ if psi ∈ C^2(int K), ∇^2 psi(y) is invertible for every y ∈ int K, and
psi(ty)=psi(y)+θ log t for all y ∈ int K and all t>0.
-/
def IsGeneralizedLogarithmOfDegree
    {n : ℕ}
    (K : Set (Fin n → ℝ))
    (ψ : interior K → ℝ)
    (θ : ℝ) : Prop :=
  IsProperCone K ∧
  (∃ ψext : (Fin n → ℝ) → ℝ,
    ContDiffOn ℝ 2 ψext (interior K) ∧
    (∀ y : interior K, ψ y = ψext y) ∧
    (∀ y : interior K,
      IsUnit
        ((Matrix.of fun i j : Fin n =>
            (fderiv ℝ
                (fun x : Fin n → ℝ =>
                  (fderiv ℝ ψext x) (Pi.single j (1 : ℝ)))
                (y : Fin n → ℝ))
              (Pi.single i (1 : ℝ))).det)) ∧
    (∀ (y : interior K) {t : ℝ}, 0 < t →
      ∃ hy' : t • (y : Fin n → ℝ) ∈ interior K,
        ψ ⟨t • (y : Fin n → ℝ), hy'⟩ = ψ y + θ * Real.log t))

/- [BLOCK Exercise 11.16-(d) | 41 | defn]
For a generalized logarithm psi : int K → ℝ, the degree is the scalar θ ∈ ℝ such that
psi(ty)=psi(y)+θ log t for all y ∈ int K and all t>0.
-/
def GeneralizedLogarithmDegree
    {n : ℕ}
    (K : Set (Fin n → ℝ))
    (ψ : interior K → ℝ)
    (θ : ℝ) : Prop :=
  ∀ (y : interior K) {t : ℝ}, 0 < t →
    ∃ hy' : t • (y : Fin n → ℝ) ∈ interior K,
      ψ ⟨t • (y : Fin n → ℝ), hy'⟩ = ψ y + θ * Real.log t

/- [BLOCK Exercise 11.16-(d) | 42 | thm]
Let K ⊆ ℝ^n be a proper cone, and write y succ_K 0 for y ∈ int K. Let psi : int K → ℝ be a
generalized logarithm for K of degree θ, meaning that psi is twice continuously differentiable on
int K, ∇^2 psi(y) is invertible for every y ∈ int K, and
psi(ty)=psi(y)+θ log t for all y ∈ int K,\ t>0.
Prove that for every y succ_K 0,
∇ psi(y)ᵀ (∇^2 psi(y))^{-1} ∇ psi(y) = -θ.
-/
theorem generalizedLogarithm_gradient_hessian_inverse_quadratic_form_eq_neg_degree
    {n : ℕ}
    {K : Set (Fin n → ℝ)}
    {ψ : interior K → ℝ}
    {θ : ℝ}
    (hψ : IsGeneralizedLogarithmOfDegree K ψ θ) :
    ∀ y : interior K,
      let ψext : (Fin n → ℝ) → ℝ := Classical.choose hψ.2
      let g : Fin n → ℝ := fun i =>
        (fderiv ℝ ψext (y : Fin n → ℝ)) (Pi.single i (1 : ℝ))
      let H : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j : Fin n =>
        (fderiv ℝ
            (fun x : Fin n → ℝ =>
              (fderiv ℝ ψext x) (Pi.single j (1 : ℝ)))
            (y : Fin n → ℝ))
          (Pi.single i (1 : ℝ))
      dotProduct g (H⁻¹.mulVec g) = -θ := by
  intro y
  classical
  dsimp
  set ψext : (Fin n → ℝ) → ℝ := Classical.choose hψ.2 with hψext_def
  set g : Fin n → ℝ := fun i =>
    (fderiv ℝ ψext (y : Fin n → ℝ)) (Pi.single i (1 : ℝ)) with hg_def
  set H : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j : Fin n =>
    (fderiv ℝ
        (fun x : Fin n → ℝ =>
          (fderiv ℝ ψext x) (Pi.single j (1 : ℝ)))
        (y : Fin n → ℝ))
      (Pi.single i (1 : ℝ)) with hH_def
  have hψext_spec :
      ContDiffOn ℝ 2 ψext (interior K) ∧
      (∀ y : interior K, ψ y = ψext y) ∧
      (∀ y : interior K,
        IsUnit
          ((Matrix.of fun i j : Fin n =>
              (fderiv ℝ
                  (fun x : Fin n → ℝ =>
                    (fderiv ℝ ψext x) (Pi.single j (1 : ℝ)))
                  (y : Fin n → ℝ))
                (Pi.single i (1 : ℝ))).det)) ∧
      (∀ (y : interior K) {t : ℝ}, 0 < t →
        ∃ hy' : t • (y : Fin n → ℝ) ∈ interior K,
          ψ ⟨t • (y : Fin n → ℝ), hy'⟩ = ψ y + θ * Real.log t) := by
    simpa only [hψext_def] using Classical.choose_spec hψ.2
  rcases hψext_spec with ⟨hψ_smooth, hrestrict, hH_unit, hscaleψ⟩
  let s : Set (Fin n → ℝ) := interior K
  let e : Fin n → (Fin n → ℝ) := fun j => Pi.single j (1 : ℝ)
  let c : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] ℝ) := fun z => fderivWithin ℝ ψext s z
  let F : (Fin n → ℝ) → ℝ := fun z => c z z
  have hsOpen : IsOpen s := by
    change IsOpen (interior K)
    simp
  have hsUnique : UniqueDiffOn ℝ s := hsOpen.uniqueDiffOn
  have hy_mem : (y : Fin n → ℝ) ∈ s := by
    simp [s]
  have hsUniqueAt : UniqueDiffWithinAt ℝ s (y : Fin n → ℝ) := hsUnique _ hy_mem
  have hscale_mem : ∀ (w : s) {t : ℝ}, 0 < t → t • (w : Fin n → ℝ) ∈ s := by
    intro w t ht
    rcases hscaleψ w ht with ⟨hw', _⟩
    simpa [s] using hw'
  have hscale_ext :
      ∀ (w : s) {t : ℝ}, 0 < t →
        ψext (t • (w : Fin n → ℝ)) = ψext (w : Fin n → ℝ) + θ * Real.log t := by
    intro w t ht
    rcases hscaleψ w ht with ⟨hw', hw_scaleψ⟩
    have hw_eq : ψ w = ψext (w : Fin n → ℝ) := hrestrict w
    have hw'_eq : ψ ⟨t • (w : Fin n → ℝ), hw'⟩ = ψext (t • (w : Fin n → ℝ)) :=
      hrestrict ⟨t • (w : Fin n → ℝ), hw'⟩
    calc
      ψext (t • (w : Fin n → ℝ)) = ψ ⟨t • (w : Fin n → ℝ), hw'⟩ := by
        symm
        exact hw'_eq
      _ = ψ w + θ * Real.log t := hw_scaleψ
      _ = ψext (w : Fin n → ℝ) + θ * Real.log t := by
        rw [hw_eq]
  -- Differentiate the log-homogeneous ray identity to get the Euler relation `Dψ(w)[w] = θ`.
  have hray_self :
      ∀ w : s, (fderivWithin ℝ ψext s (w : Fin n → ℝ)) (w : Fin n → ℝ) = θ := by
    intro w
    let r : ℝ → (Fin n → ℝ) := fun t => t • (w : Fin n → ℝ)
    have hw_cd : ContDiffWithinAt ℝ 2 ψext s (w : Fin n → ℝ) := by
      simpa [s] using hψ_smooth.contDiffWithinAt w.2
    have hray : HasDerivWithinAt r (w : Fin n → ℝ) (Set.Ioi 0) 1 := by
      -- The derivative of `t ↦ t • w` at `t = 1` is the vector `w`.
      simpa [r] using
        (hasDerivWithinAt_id (x := (1 : ℝ)) (s := Set.Ioi 0)).smul_const (w : Fin n → ℝ)
    have hcomp :
        HasDerivWithinAt (fun t => ψext (r t))
          ((fderivWithin ℝ ψext s (w : Fin n → ℝ)) (w : Fin n → ℝ)) (Set.Ioi 0) 1 := by
      -- Compose the derivative of `ψext` with the derivative of the ray.
      refine
        ((hw_cd.differentiableWithinAt (by norm_num)).hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq
          (x := 1) hray ?_ ?_)
      · intro t ht
        simpa [r] using hscale_mem w ht
      · simp [r]
    have hmodel :
        HasDerivWithinAt (fun t : ℝ => ψext (w : Fin n → ℝ) + θ * Real.log t)
          θ (Set.Ioi 0) 1 := by
      -- The derivative of the model side is `θ` because `(log t)' = 1 / t` at `t = 1`.
      have hlog : HasDerivWithinAt Real.log 1 (Set.Ioi 0) 1 := by
        simpa using (Real.hasDerivAt_log one_ne_zero).hasDerivWithinAt
      simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
        (hlog.const_mul θ).const_add (ψext (w : Fin n → ℝ))
    have hcomp_model :
        HasDerivWithinAt (fun t : ℝ => ψext (w : Fin n → ℝ) + θ * Real.log t)
          ((fderivWithin ℝ ψext s (w : Fin n → ℝ)) (w : Fin n → ℝ)) (Set.Ioi 0) 1 := by
      -- Replace the composed function by the extension form of the scaling law on `Ioi 0`.
      refine hcomp.congr_of_mem ?_ (by norm_num)
      intro t ht
      simpa [r] using (hscale_ext w ht).symm
    have hleft :
        derivWithin (fun t : ℝ => ψext (w : Fin n → ℝ) + θ * Real.log t) (Set.Ioi 0) 1
          = (fderivWithin ℝ ψext s (w : Fin n → ℝ)) (w : Fin n → ℝ) := by
      simpa using hcomp_model.derivWithin (isOpen_Ioi.uniqueDiffWithinAt (by norm_num))
    have hright :
        derivWithin (fun t : ℝ => ψext (w : Fin n → ℝ) + θ * Real.log t) (Set.Ioi 0) 1 = θ := by
      simpa using hmodel.derivWithin (isOpen_Ioi.uniqueDiffWithinAt (by norm_num))
    exact hleft.symm.trans hright
  have hψ_cd : ContDiffWithinAt ℝ 2 ψext s (y : Fin n → ℝ) := by
    simpa [s] using hψ_smooth.contDiffWithinAt hy_mem
  have hc_cd : ContDiffWithinAt ℝ 1 c s (y : Fin n → ℝ) := by
    -- A `C²` map has a `C¹` first derivative on the open interior.
    simpa [c] using hψ_cd.fderivWithin_right hsUnique (by norm_num) hy_mem
  have hc_diff : DifferentiableWithinAt ℝ c s (y : Fin n → ℝ) :=
    hc_cd.differentiableWithinAt (by norm_num)
  have hF_eq_const : Set.EqOn F (fun _ => θ) s := by
    intro z hz
    -- The self-application `z ↦ Dψ(z)[z]` is constant with value `θ` on the interior.
    simpa [F, c, s] using hray_self ⟨z, hz⟩
  have hF_zero : ∀ i : Fin n, (fderivWithin ℝ F s (y : Fin n → ℝ)) (e i) = 0 := by
    intro i
    -- Differentiating the constant ray value gives zero in every coordinate direction.
    rw [fderivWithin_congr' (f₁ := F) (f := fun _ => θ) hF_eq_const hy_mem, fderivWithin_const_apply]
    simp
  have hy_expansion : (y : Fin n → ℝ) = ∑ j : Fin n, y.1 j • e j := by
    -- Expand `y` in the standard basis to convert linear maps into coordinate sums.
    calc
      (y : Fin n → ℝ) = ∑ j : Fin n, Pi.single j (y.1 j) := by
        simpa using (Finset.univ_sum_single (y : Fin n → ℝ)).symm
      _ = ∑ j : Fin n, y.1 j • e j := by
        ext k
        simp [e, Finset.sum_apply, Pi.single_apply]
  have hexpand :
      ∀ i : Fin n,
        (fderivWithin ℝ F s (y : Fin n → ℝ)) (e i)
          = (c (y : Fin n → ℝ)) (e i) +
              ((fderivWithin ℝ c s (y : Fin n → ℝ)).flip (y : Fin n → ℝ)) (e i) := by
    intro i
    -- Differentiate `F z = c z z` using the product rule for continuous linear map evaluation.
    simpa [F, c, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      fderivWithin_id hsUniqueAt] using
      congrArg (fun L => L (e i))
        (fderivWithin_clm_apply hsUniqueAt hc_diff differentiableWithinAt_id)
  have happly_const :
      ∀ i j : Fin n,
        ((fderivWithin ℝ c s (y : Fin n → ℝ)) (e i)) (e j)
          =
          (fderivWithin ℝ (fun z : Fin n → ℝ => c z (e j)) s (y : Fin n → ℝ)) (e i) := by
    intro i j
    -- Freeze the second slot to rewrite the derivative of `c` as a scalar derivative.
    simpa [ContinuousLinearMap.flip_apply, c, fderivWithin_const_apply] using
      (congrArg (fun L => L (e i))
        (fderivWithin_clm_apply hsUniqueAt hc_diff (differentiableWithinAt_const (e j)))).symm
  have hflip_sum :
      ∀ i : Fin n,
        ((fderivWithin ℝ c s (y : Fin n → ℝ)).flip (y : Fin n → ℝ)) (e i)
          =
          ∑ j : Fin n,
            ((fderivWithin ℝ (fun z : Fin n → ℝ => c z (e j)) s (y : Fin n → ℝ)) (e i)) *
              y.1 j := by
    intro i
    -- Expand the `y`-slot linearly and read the result in coordinates.
    calc
      ((fderivWithin ℝ c s (y : Fin n → ℝ)).flip (y : Fin n → ℝ)) (e i)
          = ((fderivWithin ℝ c s (y : Fin n → ℝ)) (e i)) (y : Fin n → ℝ) := by
              simp [ContinuousLinearMap.flip_apply]
      _ = ((fderivWithin ℝ c s (y : Fin n → ℝ)) (e i)) (∑ j : Fin n, y.1 j • e j) := by
            exact congrArg (((fderivWithin ℝ c s (y : Fin n → ℝ)) (e i))) hy_expansion
      _ = ∑ j : Fin n, ((fderivWithin ℝ c s (y : Fin n → ℝ)) (e i)) (y.1 j • e j) := by
            rw [map_sum]
      _ = ∑ j : Fin n, (((fderivWithin ℝ c s (y : Fin n → ℝ)) (e i)) (e j)) * y.1 j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [mul_comm]
      _ = ∑ j : Fin n,
            ((fderivWithin ℝ (fun z : Fin n → ℝ => c z (e j)) s (y : Fin n → ℝ)) (e i)) *
              y.1 j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [happly_const i j]
  have hgrad_coord :
      ∀ i : Fin n, g i = - ∑ j : Fin n, H i j * y.1 j := by
    intro i
    have hmain :
        0 =
          (c (y : Fin n → ℝ)) (e i) +
            ∑ j : Fin n,
              ((fderivWithin ℝ (fun z : Fin n → ℝ => c z (e j)) s (y : Fin n → ℝ)) (e i)) *
                y.1 j := by
      -- Differentiate the constant function `F` and expand the product rule at `y`.
      calc
        0 = (fderivWithin ℝ F s (y : Fin n → ℝ)) (e i) := by
          simpa using (hF_zero i).symm
        _ = (c (y : Fin n → ℝ)) (e i) +
              ((fderivWithin ℝ c s (y : Fin n → ℝ)).flip (y : Fin n → ℝ)) (e i) := hexpand i
        _ = (c (y : Fin n → ℝ)) (e i) +
              ∑ j : Fin n,
                ((fderivWithin ℝ (fun z : Fin n → ℝ => c z (e j)) s (y : Fin n → ℝ)) (e i)) *
                  y.1 j := by
              rw [hflip_sum i]
    have hg_coord : (c (y : Fin n → ℝ)) (e i) = g i := by
      -- On the open interior, `fderivWithin` agrees with the ordinary derivative.
      simp [c, g, e, s, fderivWithin_of_isOpen hsOpen hy_mem]
    have hH_coord :
        ∀ j : Fin n,
          ((fderivWithin ℝ (fun z : Fin n → ℝ => c z (e j)) s (y : Fin n → ℝ)) (e i)) = H i j := by
      intro j
      have hEqOn :
          Set.EqOn
            (fun z : Fin n → ℝ => c z (e j))
            (fun z : Fin n → ℝ => (fderiv ℝ ψext z) (e j)) s := by
        intro z hz
        simp [c, s, fderivWithin_of_isOpen hsOpen hz]
      have hderiv_eq :
          fderivWithin ℝ (fun z : Fin n → ℝ => c z (e j)) s (y : Fin n → ℝ)
            =
            fderivWithin ℝ (fun z : Fin n → ℝ => (fderiv ℝ ψext z) (e j)) s (y : Fin n → ℝ) :=
        fderivWithin_congr' hEqOn hy_mem
      calc
        ((fderivWithin ℝ (fun z : Fin n → ℝ => c z (e j)) s (y : Fin n → ℝ)) (e i))
            = ((fderivWithin ℝ (fun z : Fin n → ℝ => (fderiv ℝ ψext z) (e j)) s
                (y : Fin n → ℝ)) (e i)) := by
                  rw [hderiv_eq]
        _ = (fderiv ℝ (fun z : Fin n → ℝ => (fderiv ℝ ψext z) (e j)) (y : Fin n → ℝ)) (e i) := by
              rw [fderivWithin_of_isOpen hsOpen hy_mem]
        _ = H i j := by
              simp [H, e]
    have hsum :
        (∑ j : Fin n,
          ((fderivWithin ℝ (fun z : Fin n → ℝ => c z (e j)) s (y : Fin n → ℝ)) (e i)) * y.1 j)
          =
          ∑ j : Fin n, H i j * y.1 j := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [hH_coord j]
    have hmain' : 0 = g i + ∑ j : Fin n, H i j * y.1 j := by
      calc
        0 = (c (y : Fin n → ℝ)) (e i) +
              ∑ j : Fin n,
                ((fderivWithin ℝ (fun z : Fin n → ℝ => c z (e j)) s (y : Fin n → ℝ)) (e i)) *
                  y.1 j := hmain
        _ = g i +
              ∑ j : Fin n,
                ((fderivWithin ℝ (fun z : Fin n → ℝ => c z (e j)) s (y : Fin n → ℝ)) (e i)) *
                  y.1 j := by rw [hg_coord]
        _ = g i + ∑ j : Fin n, H i j * y.1 j := by rw [hsum]
    linarith
  have hmul : g = H.mulVec (-(y : Fin n → ℝ)) := by
    ext i
    -- The coordinate identity repackages as the matrix equation `g = H * (-y)`.
    calc
      g i = - ∑ j : Fin n, H i j * y.1 j := hgrad_coord i
      _ = (fun j : Fin n => H i j) ⬝ᵥ (-(y : Fin n → ℝ)) := by
            simp [dotProduct]
      _ = (H.mulVec (-(y : Fin n → ℝ))) i := by
            simp [Matrix.mulVec]
  have hdot : dotProduct g (y : Fin n → ℝ) = θ := by
    -- Re-express the Euler ray identity at `y` in the standard coordinate basis.
    calc
      dotProduct g (y : Fin n → ℝ) = ∑ j : Fin n, g j * y.1 j := by
        simp [dotProduct]
      _ = ∑ j : Fin n, ((fderiv ℝ ψext (y : Fin n → ℝ)) (e j)) * y.1 j := by
        simp [g, e]
      _ = (fderiv ℝ ψext (y : Fin n → ℝ)) (∑ j : Fin n, y.1 j • e j) := by
        symm
        calc
          (fderiv ℝ ψext (y : Fin n → ℝ)) (∑ j : Fin n, y.1 j • e j)
              = ∑ j : Fin n, (fderiv ℝ ψext (y : Fin n → ℝ)) (y.1 j • e j) := by
                  rw [map_sum]
          _ = ∑ j : Fin n, ((fderiv ℝ ψext (y : Fin n → ℝ)) (e j)) * y.1 j := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                simp [mul_comm]
      _ = (fderiv ℝ ψext (y : Fin n → ℝ)) (y : Fin n → ℝ) := by
            simpa using (congrArg (fderiv ℝ ψext (y : Fin n → ℝ)) hy_expansion).symm
      _ = θ := by
            simpa [c, s, e, fderivWithin_of_isOpen hsOpen hy_mem] using hray_self ⟨(y : Fin n → ℝ), hy_mem⟩
  have hH_unit_y : IsUnit H.det := by
    simpa [H, hH_def] using hH_unit y
  letI : Invertible H := Matrix.invertibleOfIsUnitDet (A := H) hH_unit_y
  have hinv : H⁻¹.mulVec g = -(y : Fin n → ℝ) := by
    -- Invert the Hessian equation using the determinant hypothesis.
    exact Matrix.inv_mulVec_eq_vec (A := H) (u := g) (v := -(y : Fin n → ℝ)) hmul
  -- Substitute the inverse-Hessian relation into the quadratic form and simplify.
  calc
    dotProduct g (H⁻¹.mulVec g) = dotProduct g (-(y : Fin n → ℝ)) := by
      rw [hinv]
    _ = -dotProduct g (y : Fin n → ℝ) := by
      simp [dotProduct]
    _ = -θ := by
      rw [hdot]

end «problem-141»
