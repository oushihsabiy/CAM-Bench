import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open scoped Pointwise
open Filter
open scoped BigOperators

namespace «problem-28»
/-
A cone K ⊆ ℝ^n is called proper if it is convex, closed, pointed, and has nonempty interior, where
pointed means K cap (- K) = {0}.
-/
def IsProperCone {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  (0 ∈ K ∧ ∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x : Fin n → ℝ⦄, x ∈ K → a • x ∈ K) ∧
  Convex ℝ K ∧
  IsClosed K ∧
  K ∩ {x | -x ∈ K} = {0} ∧
  Set.Nonempty (interior K)

/-
Given a cone K ⊆ ℝ^n, the cone order induced by K is defined by x preceq_K y if and only if y - x ∈
K;
the strict cone order is defined by x prec_K y if and only if y - x ∈ int K.
-/
def StrictConeOrder {n : ℕ} (K : Set (Fin n → ℝ)) (x y : Fin n → ℝ) : Prop :=
  y - x ∈ interior K

/-
Let K ⊆ ℝ^n be a proper cone, with dual cone K* = {z∈ ℝ^n | zᵀ x ≥ 0 for all x∈ K}. Define the cone
orders by x preceq_K y Longleftrightarrow y - x ∈ K, x prec_K y Longleftrightarrow y - x ∈ int K,
where
int K is the interior of K. Let psi: - int K → ℝ be differentiable and concave, and assume that for
all x ∈ - int K and all s > 0, psi(sx) = psi(x) + log s. Suppose y prec_K 0. Show that -∇ psi(y) ∈
K*.
-/
open scoped Topology

/-- Positive scalings preserve a cone because the inverse scaling stays nonnegative. -/
lemma smul_set_eq_self_of_pos {n : ℕ} {K : Set (Fin n → ℝ)}
    (hcone : 0 ∈ K ∧ ∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x : Fin n → ℝ⦄, x ∈ K → a • x ∈ K)
    {t : ℝ} (ht : 0 < t) : t • K = K := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hcone.2 ht.le hw
  · intro hz
    refine ⟨t⁻¹ • z, hcone.2 (by positivity) hz, ?_⟩
    simp [smul_smul, ht.ne']

/-- Positive scalings preserve the negative interior of a cone. -/
lemma smul_mem_negInterior_of_pos {n : ℕ} {K : Set (Fin n → ℝ)}
    (hcone : 0 ∈ K ∧ ∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x : Fin n → ℝ⦄, x ∈ K → a • x ∈ K)
    {u : Fin n → ℝ} (hu : u ∈ -interior K) {t : ℝ} (ht : 0 < t) :
    t • u ∈ -interior K := by
  -- Rewrite the negative-interior membership as an interior statement in `K`.
  have huK : -u ∈ interior K := by
    simpa using hu
  -- Transport interior points by the positive scaling homeomorphism.
  have htK : t • K = K := smul_set_eq_self_of_pos hcone ht
  have hscaled : -(t • u) ∈ interior K := by
    have : t • (-u) ∈ interior (t • K) := by
      rw [interior_smul₀ ht.ne' K]
      exact ⟨-u, huK, by simp⟩
    rw [htK] at this
    simpa [smul_neg] using this
  simpa using hscaled

/-- A differentiable concave function lies below its tangent hyperplane. -/
lemma ConcaveOn.le_tangent_of_differentiableAt
    {n : ℕ} {s : Set (Fin n → ℝ)} {psi : (Fin n → ℝ) → ℝ}
    (hConc : ConcaveOn ℝ s psi) {y z : Fin n → ℝ} (hy : y ∈ s) (hz : z ∈ s)
    (hDiff : DifferentiableAt ℝ psi y) :
    psi z ≤ psi y + (fderiv ℝ psi y) (z - y) := by
  let g : ℝ → ℝ := fun t => psi (AffineMap.lineMap y z t)
  -- Restrict the multivariable concavity statement to the segment from `y` to `z`.
  have hgConc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) g := by
    simpa [g] using
      (hConc.comp_affineMap (AffineMap.lineMap y z)).subset
        (hConc.1.mapsTo_lineMap hy hz) (convex_Icc (0 : ℝ) 1)
  -- Differentiate the line restriction at the left endpoint of the segment.
  have hgDeriv : HasDerivAt g ((fderiv ℝ psi y) (z - y)) 0 := by
    have hline : HasDerivAt (AffineMap.lineMap y z) (z - y) (0 : ℝ) :=
      AffineMap.hasDerivAt_lineMap (a := y) (b := z) (x := (0 : ℝ))
    simpa [g] using
      HasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ))
        (f := AffineMap.lineMap y z) (l := psi) hDiff.hasFDerivAt hline
        (by simp)
  have hslope :
      slope g 0 1 ≤ deriv g 0 :=
    hgConc.slope_le_deriv (by simp) (by simp) zero_lt_one hgDeriv.differentiableAt
  have hslope' : psi z - psi y ≤ deriv g 0 := by
    simpa [g, slope] using hslope
  calc
    psi z = psi y + (psi z - psi y) := by ring
    _ ≤ psi y + deriv g 0 := by gcongr
    _ = psi y + (fderiv ℝ psi y) (z - y) := by rw [hgDeriv.deriv]

/-- The log-homogeneous radial derivative at the basepoint is equal to `1`. -/
lemma fderiv_eq_one_on_basepoint_of_log_homogeneous
    {n : ℕ} {K : Set (Fin n → ℝ)} {psi : (Fin n → ℝ) → ℝ} {y : Fin n → ℝ}
    (hy : y ∈ -interior K)
    (hDiff : ∀ x : Fin n → ℝ, x ∈ -interior K → DifferentiableAt ℝ psi x)
    (hlog : ∀ x : Fin n → ℝ, x ∈ -interior K → ∀ s : ℝ, 0 < s →
      psi (s • x) = psi x + Real.log s) :
    (fderiv ℝ psi y) y = 1 := by
  let g : ℝ → ℝ := fun s => psi (s • y)
  -- Compute the derivative of the radial restriction by the chain rule.
  have hgDeriv : HasDerivAt g ((fderiv ℝ psi y) y) 1 := by
    have hline : HasDerivAt (AffineMap.lineMap (0 : Fin n → ℝ) y) y (1 : ℝ) := by
      simpa using AffineMap.hasDerivAt_lineMap (a := (0 : Fin n → ℝ)) (b := y) (x := (1 : ℝ))
    simpa [g, Function.comp_def, AffineMap.lineMap_apply_module] using
      HasFDerivAt.comp_hasDerivAt_of_eq (x := (1 : ℝ))
        (f := AffineMap.lineMap (0 : Fin n → ℝ) y) (l := psi) ((hDiff y hy).hasFDerivAt) hline
        (by simp)
  -- Near `1`, the radial restriction agrees with the explicit logarithmic formula.
  have hgLog : HasDerivAt g 1 1 := by
    have hlogNear : g =ᶠ[𝓝 (1 : ℝ)] fun s => psi y + Real.log s := by
      filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with s hs
      simpa [g] using hlog y hy s hs
    have hlogDeriv : HasDerivAt (fun s : ℝ => psi y + Real.log s) 1 1 := by
      simpa using (Real.hasDerivAt_log (show (1 : ℝ) ≠ 0 by norm_num)).const_add (psi y)
    exact hlogDeriv.congr_of_eventuallyEq hlogNear
  -- Compare the two derivatives of the same scalar function at `1`.
  have hgDerivEq : deriv g 1 = (fderiv ℝ psi y) y := hgDeriv.deriv
  have hgLogEq : deriv g 1 = 1 := hgLog.deriv
  exact hgDerivEq.symm.trans hgLogEq

/-- The derivative is nonnegative on the negative interior of the cone. -/
lemma fderiv_nonneg_on_negInterior_of_concave_log_homogeneous
    {n : ℕ} {K : Set (Fin n → ℝ)} {psi : (Fin n → ℝ) → ℝ} {y : Fin n → ℝ}
    (hcone : 0 ∈ K ∧ ∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x : Fin n → ℝ⦄, x ∈ K → a • x ∈ K)
    (hy : y ∈ -interior K)
    (hConc : ConcaveOn ℝ (-interior K) psi)
    (hDiff : ∀ x : Fin n → ℝ, x ∈ -interior K → DifferentiableAt ℝ psi x)
    (hlog : ∀ x : Fin n → ℝ, x ∈ -interior K → ∀ s : ℝ, 0 < s →
      psi (s • x) = psi x + Real.log s)
    {u : Fin n → ℝ} (hu : u ∈ -interior K) :
    0 ≤ (fderiv ℝ psi y) u := by
  let L := fderiv ℝ psi y
  have hLy : L y = 1 :=
    fderiv_eq_one_on_basepoint_of_log_homogeneous hy hDiff hlog
  by_contra hneg
  have hLu : L u < 0 := lt_of_not_ge hneg
  let c : ℝ := psi u - psi y + 1
  let r : ℝ := max 0 (-c) + 1
  have hrpos : 0 < r := by
    dsimp [r]
    linarith [le_max_left (0 : ℝ) (-c)]
  let T : ℝ := Real.exp r
  have hTpos : 0 < T := Real.exp_pos r
  have hTu : T • u ∈ -interior K :=
    smul_mem_negInterior_of_pos hcone hu hTpos
  -- Apply the tangent-line upper bound at `y` to the scaled point `T • u`.
  have hsupport :
      psi (T • u) ≤ psi y + L (T • u - y) :=
    ConcaveOn.le_tangent_of_differentiableAt hConc hy hTu (hDiff y hy)
  have hscaled :
      psi u + Real.log T ≤ psi y + (T * L u - L y) := by
    rw [hlog u hu T hTpos] at hsupport
    simpa [L, ContinuousLinearMap.map_sub, map_smul, smul_eq_mul, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
      using hsupport
  have hineq : (c + Real.log T) / T ≤ L u := by
    rw [hLy] at hscaled
    have htmp : c + Real.log T ≤ T * L u := by
      dsimp [c] at *
      linarith
    exact (div_le_iff₀ hTpos).2 <| by
      simpa [mul_comm, mul_left_comm, mul_assoc] using htmp
  have hnumPos : 0 < c + Real.log T := by
    have hlogExp : Real.log T = r := by
      simp [T]
    rw [hlogExp]
    dsimp [r]
    have hgt : -c < max 0 (-c) + 1 := by
      have hle : -c ≤ max 0 (-c) := le_max_right _ _
      linarith
    linarith
  have hleftPos : 0 < (c + Real.log T) / T := by
    exact div_pos hnumPos hTpos
  linarith

theorem neg_gradient_mem_dualCone_of_concave_log_homogeneous
    {n : ℕ} (K : Set (Fin n → ℝ)) (hK : IsProperCone K) :
    ∀ (psi : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ),
      y ∈ -interior K →
      StrictConeOrder K y 0 →
      ConcaveOn ℝ (-interior K) psi →
      (∀ x : Fin n → ℝ, x ∈ -interior K → DifferentiableAt ℝ psi x) →
      (∀ x : Fin n → ℝ, x ∈ -interior K → ∀ s : ℝ, 0 < s → psi (s • x) = psi x + Real.log s) →
      ∀ x : Fin n → ℝ, x ∈ K → ∑ i, (fderiv ℝ psi y) (Pi.single i (1 : ℝ)) * x i ≤ 0 := by
  intro psi y hy horder hConc hDiff hlog x hx
  let L := fderiv ℝ psi y
  have hcone : 0 ∈ K ∧ ∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x : Fin n → ℝ⦄, x ∈ K → a • x ∈ K := hK.1
  have hConv : Convex ℝ K := hK.2.1
  have hClosed : IsClosed K := hK.2.2.1
  have hInteriorNonempty : Set.Nonempty (interior K) := hK.2.2.2.2
  have hyK : -y ∈ interior K := by
    simpa [StrictConeOrder] using horder
  have hInterior :
      ∀ z : Fin n → ℝ, z ∈ interior K → L z ≤ 0 := by
    intro z hz
    -- Negating an interior point puts us in the domain where the derivative is nonnegative.
    have hzNeg : -z ∈ -interior K := by
      simpa using hz
    have hnonneg :
        0 ≤ L (-z) :=
      fderiv_nonneg_on_negInterior_of_concave_log_homogeneous
        hcone hy hConc hDiff hlog hzNeg
    simpa [L, map_neg] using hnonneg
  -- Extend the interior inequality to the whole closed cone by closure of the interior.
  have hClosedHalfspace : IsClosed {z : Fin n → ℝ | L z ≤ 0} :=
    isClosed_Iic.preimage L.continuous
  have hInteriorClosure :
      closure (interior K) = K := by
    rw [Convex.closure_interior_eq_closure_of_nonempty_interior hConv hInteriorNonempty,
      hClosed.closure_eq]
  have hxClosure : x ∈ closure (interior K) := by
    simpa [hInteriorClosure] using hx
  have hxLe : L x ≤ 0 := by
    refine hClosedHalfspace.closure_subset_iff.2 ?_ hxClosure
    intro z hz
    exact hInterior z hz
  -- Rewrite `L x` in the standard basis coordinates.
  have hxExpand :
      L x = ∑ i, L (Pi.single i (1 : ℝ)) * x i := by
    change L.toLinearMap x = ∑ i, L (Pi.single i (1 : ℝ)) * x i
    have hcoords :
        (LinearEquiv.piRing ℝ ℝ (Fin n) ℝ) L.toLinearMap =
          fun i => L (Pi.single i (1 : ℝ)) := by
      ext i
      simp
    calc
      L.toLinearMap x =
          ((LinearEquiv.piRing ℝ ℝ (Fin n) ℝ).symm
            ((LinearEquiv.piRing ℝ ℝ (Fin n) ℝ) L.toLinearMap)) x := by simp
      _ = ((LinearEquiv.piRing ℝ ℝ (Fin n) ℝ).symm
            (fun i => L (Pi.single i (1 : ℝ)))) x := by rw [hcoords]
      _ = ∑ i, x i • L (Pi.single i (1 : ℝ)) := by
        exact
          (LinearEquiv.piRing_symm_apply (R := ℝ) (M := ℝ) (ι := Fin n) (S := ℝ)
            (f := fun i => L (Pi.single i (1 : ℝ))) (g := x))
      _ = ∑ i, L (Pi.single i (1 : ℝ)) * x i := by
        simp_rw [smul_eq_mul, mul_comm]
  calc
    ∑ i, (fderiv ℝ psi y) (Pi.single i (1 : ℝ)) * x i = L x := by
      simpa [L] using hxExpand.symm
    _ ≤ 0 := hxLe

end «problem-28»
