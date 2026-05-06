import Mathlib
import problems.«problem-7»

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-118»

/-- The canonical identification `n = Fintype.card (Fin n)`. -/
lemma fin_card_eq (n : ℕ) : n = Fintype.card (Fin n) := by
  simp

/-- The `j`th index among the `k` smallest eigenvalues, viewed in the `eigenvalues₀` indexing type. -/
def smallestEigenvalueIndex (n k : ℕ) (hkn : k ≤ n) (j : Fin k) : Fin (Fintype.card (Fin n)) :=
  Fin.cast (fin_card_eq n) (Fin.natAdd_castLEEmb hkn j)

/-- The product of the `k` smallest eigenvalues of a Hermitian matrix. -/
def smallestEigenvalueProduct
    (n k : ℕ)
    (hkn : k ≤ n)
    (X : Matrix (Fin n) (Fin n) ℝ)
    (hH : X.IsHermitian) : ℝ :=
  ∏ j : Fin k, hH.eigenvalues₀ (smallestEigenvalueIndex n k hkn j)

/-- The geometric mean of the `k` smallest eigenvalues of a Hermitian matrix. -/
def smallestEigenvalueGeometricMean
    (n k : ℕ)
    (hkn : k ≤ n)
    (X : Matrix (Fin n) (Fin n) ℝ)
    (hH : X.IsHermitian) : ℝ :=
  Real.rpow (smallestEigenvalueProduct n k hkn X hH) (1 / (k : ℝ))

/-- The real symmetric positive-definite cone is convex. -/
lemma positiveDefiniteSymmetricCone_convex (n : ℕ) :
    Convex ℝ {X : Matrix (Fin n) (Fin n) ℝ | X.PosDef ∧ X.IsSymm} := by
  intro X hX Y hY a b ha hb hab
  rcases hX with ⟨hXpd, hXsymm⟩
  rcases hY with ⟨hYpd, hYsymm⟩
  refine ⟨?_, Matrix.IsSymm.add (Matrix.IsSymm.smul hXsymm a) (Matrix.IsSymm.smul hYsymm b)⟩
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by
      linarith
    simpa [ha0, hb1] using hYpd
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by
      linarith
    simpa [hb0, ha1] using hXpd
  have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
  have hb_pos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hb0)
  exact (hXpd.smul ha_pos).add (hYpd.smul hb_pos)

/-- The tail eigenvector frame from `problem-7` realizes the selected smallest-eigenvalue product. -/
lemma tailEigenvectorFrame_attains_smallestEigenvalueProduct
    (n k : ℕ)
    (hkn : k ≤ n)
    (X : Matrix (Fin n) (Fin n) ℝ)
    (hXHerm : X.IsHermitian) :
    let e : Fin k ↪ Fin n := Fin.natAdd_castLEEmb hkn
    let σ : Fin k ↪ Fin n := {
      toFun := fun j => (Fintype.equivOfCardEq (Fintype.card_fin _)) (Fin.cast (by simp) (e j))
      inj' := by
        intro i j hij
        apply e.injective
        have hcast :
            Fin.cast (Fintype.card_fin n).symm (e i) = Fin.cast (Fintype.card_fin n).symm (e j) := by
          simpa using (Fintype.equivOfCardEq (Fintype.card_fin _)).injective hij
        exact Fin.cast_injective (Fintype.card_fin n).symm hcast }
    let V : Matrix (Fin n) (Fin k) ℝ := fun i j => hXHerm.eigenvectorBasis (σ j) i
    V.transpose * V = 1 ∧
      (∏ i : Fin k, dotProduct (V · i) (X.mulVec (V · i))) =
        smallestEigenvalueProduct n k hkn X hXHerm := by
  have hXsymm : X.IsSymm := by
    -- Over `ℝ`, Hermitian and symmetric matrices coincide.
    simpa using hXHerm
  -- Reuse the exact tail-frame witness already packaged in `problem-7`.
  simpa [smallestEigenvalueProduct, smallestEigenvalueIndex] using
    «problem-7».tail_eigenvector_frame_attains_value n k hkn X hXsymm

/-- Every column of an orthonormal frame is nonzero. -/
lemma frameColumn_ne_zero_of_orthonormal
    {n k : ℕ}
    {V : Matrix (Fin n) (Fin k) ℝ}
    (hVorth : V.transpose * V = 1)
    (i : Fin k) :
    V · i ≠ 0 := by
  have hVinj : Function.Injective V.mulVec :=
    «problem-7».orthonormal_frame_mulVec_injective n k V hVorth
  have hsingle_ne : (Pi.single i (1 : ℝ) : Fin k → ℝ) ≠ 0 := by
    intro hzero
    have := congrFun hzero i
    simp at this
  -- Write the column as `V *ᵥ eᵢ` and use injectivity of the synthesis map.
  intro hcol
  apply hsingle_ne
  apply hVinj
  simpa [Matrix.mulVec_single_one] using hcol

/-- Positive definiteness makes each quadratic factor of an orthonormal frame strictly positive. -/
lemma orthonormalFrame_quadraticFactor_pos
    {n k : ℕ}
    {X : Matrix (Fin n) (Fin n) ℝ}
    {V : Matrix (Fin n) (Fin k) ℝ}
    (hXpd : X.PosDef)
    (hVorth : V.transpose * V = 1)
    (i : Fin k) :
    0 < dotProduct (V · i) (X.mulVec (V · i)) := by
  -- The `i`th column is nonzero, so the defining positive-definite inequality applies to it.
  exact hXpd.dotProduct_mulVec_pos (frameColumn_ne_zero_of_orthonormal hVorth i)

/-- The product of the quadratic factors of an orthonormal frame is strictly positive. -/
lemma orthonormalFrame_quadraticProduct_pos
    {n k : ℕ}
    {X : Matrix (Fin n) (Fin n) ℝ}
    {V : Matrix (Fin n) (Fin k) ℝ}
    (hXpd : X.PosDef)
    (hVorth : V.transpose * V = 1) :
    0 < ∏ i : Fin k, dotProduct (V · i) (X.mulVec (V · i)) := by
  -- Multiply the pointwise positive quadratic factors.
  refine Finset.prod_pos ?_
  intro i hi
  exact orthonormalFrame_quadraticFactor_pos hXpd hVorth i

/-- The selected smallest-eigenvalue product is positive on the positive-definite cone. -/
lemma smallestEigenvalueProduct_pos
    (n k : ℕ)
    (hkn : k ≤ n)
    {X : Matrix (Fin n) (Fin n) ℝ}
    (hXpd : X.PosDef)
    (hXHerm : X.IsHermitian) :
    0 < smallestEigenvalueProduct n k hkn X hXHerm := by
  let e : Fin k ↪ Fin n := Fin.natAdd_castLEEmb hkn
  let σ : Fin k ↪ Fin n := {
    toFun := fun j => (Fintype.equivOfCardEq (Fintype.card_fin _)) (Fin.cast (by simp) (e j))
    inj' := by
      intro i j hij
      apply e.injective
      have hcast :
          Fin.cast (Fintype.card_fin n).symm (e i) = Fin.cast (Fintype.card_fin n).symm (e j) := by
        simpa using (Fintype.equivOfCardEq (Fintype.card_fin _)).injective hij
      exact Fin.cast_injective (Fintype.card_fin n).symm hcast }
  let V : Matrix (Fin n) (Fin k) ℝ := fun i j => hXHerm.eigenvectorBasis (σ j) i
  have hFrame :
      V.transpose * V = 1 ∧
        (∏ i : Fin k, dotProduct (V · i) (X.mulVec (V · i))) =
          smallestEigenvalueProduct n k hkn X hXHerm := by
    -- The tail eigenvectors give an exact positive witness for the product.
    simpa [e, σ, V] using
      tailEigenvectorFrame_attains_smallestEigenvalueProduct n k hkn X hXHerm
  have hprod_pos :
      0 < ∏ i : Fin k, dotProduct (V · i) (X.mulVec (V · i)) :=
    orthonormalFrame_quadraticProduct_pos hXpd hFrame.1
  simpa [hFrame.2] using hprod_pos

/-- The variational formula from `problem-7` bounds the selected smallest-eigenvalue product by any
orthonormal-frame quadratic product. -/
lemma smallestEigenvalueProduct_le_frameQuadraticProduct
    (n k : ℕ)
    (hk1 : 1 ≤ k)
    (hkn : k ≤ n)
    {X : Matrix (Fin n) (Fin n) ℝ}
    (hXpd : X.PosDef)
    (hXHerm : X.IsHermitian)
    {V : Matrix (Fin n) (Fin k) ℝ}
    (hVorth : V.transpose * V = 1) :
    smallestEigenvalueProduct n k hkn X hXHerm ≤
      ∏ i : Fin k, dotProduct (V · i) (X.mulVec (V · i)) := by
  have hXsymm : X.IsSymm := by
    -- Convert to the symmetric formulation expected by `problem-7`.
    simpa using hXHerm
  let S : Set ℝ :=
    {r : ℝ |
      ∃ U : Matrix (Fin n) (Fin k) ℝ,
        U.transpose * U = 1 ∧
        r = ∏ i : Fin k, dotProduct (U · i) (X.mulVec (U · i))}
  have hvariational :
      smallestEigenvalueProduct n k hkn X hXHerm = sInf S := by
    -- Import the local variational theorem and rewrite its eigenvalue product into our wrapper.
    simpa [S, smallestEigenvalueProduct, smallestEigenvalueIndex] using
      «problem-7».inf_prod_quadratic_forms_eq_prod_smallest_eigenvalues n k hk1 hkn X hXsymm hXpd
  have hS_bddBelow : BddBelow S := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with ⟨U, hUorth, rfl⟩
    -- Every feasible frame contributes a nonnegative product of positive quadratic factors.
    exact (orthonormalFrame_quadraticProduct_pos hXpd hUorth).le
  have hmem :
      (∏ i : Fin k, dotProduct (V · i) (X.mulVec (V · i))) ∈ S := by
    exact ⟨V, hVorth, rfl⟩
  -- Evaluate the infimum at the chosen feasible frame.
  calc
    smallestEigenvalueProduct n k hkn X hXHerm = sInf S := hvariational
    _ ≤ ∏ i : Fin k, dotProduct (V · i) (X.mulVec (V · i)) := csInf_le hS_bddBelow hmem

/-- Any determinant-one weight vector supports the selected smallest-eigenvalue geometric mean by
the corresponding weighted average of frame quadratic factors. -/
lemma smallestEigenvalueGeometricMean_le_weightedFrameAverage
    (n k : ℕ)
    (hk1 : 1 ≤ k)
    (hkn : k ≤ n)
    {X : Matrix (Fin n) (Fin n) ℝ}
    (hXpd : X.PosDef)
    (hXHerm : X.IsHermitian)
    {V : Matrix (Fin n) (Fin k) ℝ}
    (hVorth : V.transpose * V = 1)
    (w : Fin k → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_prod : ∏ i : Fin k, w i = 1) :
    smallestEigenvalueGeometricMean n k hkn X hXHerm ≤
      (∑ i : Fin k, w i * dotProduct (V · i) (X.mulVec (V · i))) / k := by
  have hk_pos_nat : 0 < k := Nat.succ_le_iff.mp hk1
  have hk_pos : 0 < (k : ℝ) := by
    exact_mod_cast hk_pos_nat
  have hk_nonneg : 0 ≤ (1 / (k : ℝ)) := by positivity
  let z : Fin k → ℝ := fun i => w i * dotProduct (V · i) (X.mulVec (V · i))
  have hz_nonneg : ∀ i, 0 ≤ z i := by
    intro i
    -- Each weighted quadratic factor is nonnegative because both ingredients are.
    exact mul_nonneg (hw_nonneg i) (orthonormalFrame_quadraticFactor_pos hXpd hVorth i).le
  have hproduct_nonneg :
      0 ≤ smallestEigenvalueProduct n k hkn X hXHerm := by
    exact (smallestEigenvalueProduct_pos n k hkn hXpd hXHerm).le
  have hproduct_bound :
      smallestEigenvalueProduct n k hkn X hXHerm ≤
        ∏ i : Fin k, dotProduct (V · i) (X.mulVec (V · i)) :=
    smallestEigenvalueProduct_le_frameQuadraticProduct n k hk1 hkn hXpd hXHerm hVorth
  have hz_prod :
      ∏ i : Fin k, z i = ∏ i : Fin k, dotProduct (V · i) (X.mulVec (V · i)) := by
    -- The determinant-one normalization makes the weighted and unweighted products coincide.
    simp [z, Finset.prod_mul_distrib, hw_prod]
  have hamgm :=
    Real.geom_mean_le_arith_mean
      (s := Finset.univ)
      (w := fun _ : Fin k => (1 : ℝ))
      (z := z)
      (fun _ _ => by positivity)
      (by simpa using hk_pos)
      (fun i _ => hz_nonneg i)
  -- First compare with the frame product, then apply scalar AM-GM to the weighted factors.
  calc
    smallestEigenvalueGeometricMean n k hkn X hXHerm
      = Real.rpow (smallestEigenvalueProduct n k hkn X hXHerm) (1 / (k : ℝ)) := by
          rfl
    _ ≤ Real.rpow
          (∏ i : Fin k, dotProduct (V · i) (X.mulVec (V · i)))
          (1 / (k : ℝ)) := by
          exact Real.rpow_le_rpow hproduct_nonneg hproduct_bound hk_nonneg
    _ = Real.rpow (∏ i : Fin k, z i) (1 / (k : ℝ)) := by
          rw [hz_prod]
    _ ≤ (∑ i : Fin k, z i) / k := by
          simpa [z, one_div, div_eq_mul_inv] using hamgm
    _ = (∑ i : Fin k, w i * dotProduct (V · i) (X.mulVec (V · i))) / k := by
          rfl

theorem geometricMeanSmallestEigenvalues_concave
    (n k : ℕ)
    (hk1 : 1 ≤ k)
    (hkn : k ≤ n) :
    ConcaveOn ℝ
      {X : Matrix (Fin n) (Fin n) ℝ | X.PosDef ∧ X.IsSymm}
      (fun X =>
        by
          classical
          exact
            if hX : X.PosDef ∧ X.IsSymm then
              let hH : X.IsHermitian := by
                ext i j
                simpa using hX.2.apply i j
              Real.rpow
                (∏ j : Fin k, hH.eigenvalues₀
                  (Fin.cast (show n = Fintype.card (Fin n) by simp) ⟨n - k + j.1, by
                    have hj : j.1 < k := j.2
                    calc
                      n - k + j.1 < n - k + k := Nat.add_lt_add_left hj (n - k)
                      _ = n := Nat.sub_add_cancel hkn⟩))
                (1 / (k : ℝ))
            else
              0) := by
  classical
  refine ⟨positiveDefiniteSymmetricCone_convex n, ?_⟩
  intro X hX Y hY a b ha hb hab
  let Z : Matrix (Fin n) (Fin n) ℝ := a • X + b • Y
  have hHX : X.IsHermitian := by
    -- On the domain, the endpoint matrices are symmetric, hence Hermitian.
    simpa using hX.2
  have hHY : Y.IsHermitian := by
    -- The same conversion is used for the second endpoint.
    simpa using hY.2
  have hZ : Z.PosDef ∧ Z.IsSymm := by
    -- The Jensen point stays in the positive-definite symmetric cone.
    simpa [Z] using (positiveDefiniteSymmetricCone_convex n) hX hY ha hb hab
  have hHZ : Z.IsHermitian := by
    -- Convert the midpoint symmetry into the Hermitian formulation used by the spectral lemmas.
    simpa using hZ.2
  let fx : ℝ := smallestEigenvalueGeometricMean n k hkn X hHX
  let fy : ℝ := smallestEigenvalueGeometricMean n k hkn Y hHY
  let fz : ℝ := smallestEigenvalueGeometricMean n k hkn Z hHZ
  let e : Fin k ↪ Fin n := Fin.natAdd_castLEEmb hkn
  let σ : Fin k ↪ Fin n := {
    toFun := fun j => (Fintype.equivOfCardEq (Fintype.card_fin _)) (Fin.cast (by simp) (e j))
    inj' := by
      intro i j hij
      apply e.injective
      have hcast :
          Fin.cast (Fintype.card_fin n).symm (e i) = Fin.cast (Fintype.card_fin n).symm (e j) := by
        simpa using (Fintype.equivOfCardEq (Fintype.card_fin _)).injective hij
      exact Fin.cast_injective (Fintype.card_fin n).symm hcast }
  let V : Matrix (Fin n) (Fin k) ℝ := fun i j => hHZ.eigenvectorBasis (σ j) i
  have hFrame :
      V.transpose * V = 1 ∧
        (∏ i : Fin k, dotProduct (V · i) (Z.mulVec (V · i))) =
          smallestEigenvalueProduct n k hkn Z hHZ := by
    -- Route correction: instead of the abandoned normalization route, support `f` directly at the
    -- Jensen point with its tail eigenvector frame.
    simpa [e, σ, V] using
      tailEigenvectorFrame_attains_smallestEigenvalueProduct n k hkn Z hHZ
  let q : Matrix (Fin n) (Fin n) ℝ → Fin k → ℝ :=
    fun T i => dotProduct (V · i) (T.mulVec (V · i))
  have hk_pos_nat : 0 < k := Nat.succ_le_iff.mp hk1
  have hk_pos : 0 < (k : ℝ) := by
    exact_mod_cast hk_pos_nat
  have hk_ne : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk_pos_nat)
  have hqZ_pos : ∀ i : Fin k, 0 < q Z i := by
    intro i
    -- Each tail eigenvector gives a positive quadratic factor at the supporting point.
    exact orthonormalFrame_quadraticFactor_pos hZ.1 hFrame.1 i
  have hqZ_prod_pos : 0 < ∏ i : Fin k, q Z i :=
    orthonormalFrame_quadraticProduct_pos hZ.1 hFrame.1
  have hfz_eq :
      fz = Real.rpow (∏ i : Fin k, q Z i) (1 / (k : ℝ)) := by
    -- The support point value is the geometric mean of these exact quadratic factors.
    dsimp [fz]
    rw [← hFrame.2]
  have hfz_pos : 0 < fz := by
    -- The support value is positive because the supporting quadratic factors are positive.
    rw [hfz_eq]
    exact Real.rpow_pos_of_pos hqZ_prod_pos _
  let w : Fin k → ℝ := fun i => fz / q Z i
  have hw_nonneg : ∀ i : Fin k, 0 ≤ w i := by
    intro i
    -- The support weights are positive scalar normalizations of the supporting quadratic factors.
    exact (div_pos hfz_pos (hqZ_pos i)).le
  have hfz_pow :
      fz ^ k = ∏ i : Fin k, q Z i := by
    -- Raising the geometric mean back to the `k`th power recovers the supporting product.
    rw [hfz_eq, ← Real.rpow_natCast, Real.rpow_mul hqZ_prod_pos.le]
    have hk_inv : (1 / (k : ℝ)) * (k : ℝ) = 1 := by
      field_simp [hk_ne]
    rw [hk_inv, Real.rpow_one]
  have hw_prod : ∏ i : Fin k, w i = 1 := by
    have hqZ_prod_ne : (∏ i : Fin k, q Z i) ≠ 0 := hqZ_prod_pos.ne'
    -- The weight normalization is chosen so that the product of the weights is exactly one.
    calc
      ∏ i : Fin k, w i = (∏ i : Fin k, fz) / ∏ i : Fin k, q Z i := by
        simp [w, Finset.prod_div_distrib]
      _ = fz ^ k / ∏ i : Fin k, q Z i := by simp
      _ = (∏ i : Fin k, q Z i) / ∏ i : Fin k, q Z i := by rw [hfz_pow]
      _ = 1 := by field_simp [hqZ_prod_ne]
  have hsupportX :
      fx ≤ (∑ i : Fin k, w i * q X i) / k := by
    -- The variational characterization plus scalar AM-GM gives a linear support bound at `X`.
    exact
      smallestEigenvalueGeometricMean_le_weightedFrameAverage
        n k hk1 hkn hX.1 hHX hFrame.1 w hw_nonneg hw_prod
  have hsupportY :
      fy ≤ (∑ i : Fin k, w i * q Y i) / k := by
    -- The same supporting functional dominates the value at `Y`.
    exact
      smallestEigenvalueGeometricMean_le_weightedFrameAverage
        n k hk1 hkn hY.1 hHY hFrame.1 w hw_nonneg hw_prod
  have hsupportZ_eq :
      (∑ i : Fin k, w i * q Z i) / k = fz := by
    have hsum :
        ∑ i : Fin k, w i * q Z i = (k : ℝ) * fz := by
      -- At the support point, every weighted quadratic factor collapses to the same value `fz`.
      calc
        ∑ i : Fin k, w i * q Z i = ∑ i : Fin k, fz := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hqZ_ne : q Z i ≠ 0 := (hqZ_pos i).ne'
          dsimp [w]
          field_simp [hqZ_ne]
        _ = (k : ℝ) * fz := by simp
    rw [hsum]
    field_simp [hk_ne]
  have hq_linear :
      ∀ i : Fin k, q Z i = a * q X i + b * q Y i := by
    intro i
    -- Each quadratic factor is affine in the ambient matrix argument.
    dsimp [q, Z]
    simp [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul, mul_add,
      add_mul]
    ring
  have hsupport_linear :
      (∑ i : Fin k, w i * q Z i) / k =
        a * ((∑ i : Fin k, w i * q X i) / k) +
          b * ((∑ i : Fin k, w i * q Y i) / k) := by
    have hsum :
        ∑ i : Fin k, w i * q Z i =
          a * (∑ i : Fin k, w i * q X i) + b * (∑ i : Fin k, w i * q Y i) := by
      -- Expand the affine dependence termwise and regroup the finite sums.
      calc
        ∑ i : Fin k, w i * q Z i =
            ∑ i : Fin k, (a * (w i * q X i) + b * (w i * q Y i)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hq_linear i]
              ring
        _ = a * (∑ i : Fin k, w i * q X i) + b * (∑ i : Fin k, w i * q Y i) := by
              simp [Finset.mul_sum, Finset.sum_add_distrib, mul_assoc]
    rw [hsum]
    field_simp [hk_ne]
    ring
  have hconcave_core :
      a * fx + b * fy ≤ fz := by
    -- Compare the endpoint values with the support functional and then evaluate it at `Z`.
    have hax := mul_le_mul_of_nonneg_left hsupportX ha
    have hby := mul_le_mul_of_nonneg_left hsupportY hb
    calc
      a * fx + b * fy
          ≤ a * ((∑ i : Fin k, w i * q X i) / k) +
              b * ((∑ i : Fin k, w i * q Y i) / k) := by
                exact add_le_add hax hby
      _ = (∑ i : Fin k, w i * q Z i) / k := by
            symm
            exact hsupport_linear
      _ = fz := hsupportZ_eq
  -- Rewrite the piecewise-defined function on the cone and conclude the concavity inequality.
  simpa [X, Y, Z, fx, fy, fz, hX, hY, hZ, smallestEigenvalueGeometricMean,
    smallestEigenvalueProduct, smallestEigenvalueIndex] using hconcave_core

end «problem-118»
