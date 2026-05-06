import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-46»
/-
For a set C ⊆ ℝ^n and a point x₀ ∈ C, the normal cone of C at x₀ is defined by N_C(x₀): = {y ∈ ℝ^n |
yᵀ(x - x₀) ≤ 0 for all x ∈ C}.
-/
def normalCone (C : Set (Fin n → ℝ)) (x₀ : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {y | ∀ x, x ∈ C → dotProduct y (x - x₀) ≤ 0}

/-
For a system of inequality constraints a_iᵀ x ≤ bᵢ, the active set at a point x₀ is I(x₀): = {i |
a_iᵀ x₀ = bᵢ}, that is, the set of indices of the constraints active at x₀.
-/
def activeSet {m : ℕ} (a : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x₀ : Fin n → ℝ) : Set (Fin m) :=
  {i | dotProduct (a i) x₀ = b i}

/-
A polyhedron is a set of the form P = {x ∈ ℝ^n | Ax ≤ b}, for some matrix A ∈ ℝ^m× n and vector b ∈
ℝ^m, where the inequality is interpreted componentwise.
-/
def polyhedron {m : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, dotProduct (A i) x ≤ b i}

/-- Polyhedra are closed because they are intersections of finitely many closed half-spaces. -/
private lemma polyhedron_isClosed {m : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    IsClosed (polyhedron A b) := by
  -- Rewrite the polyhedron as an intersection of coordinatewise closed half-spaces.
  rw [show polyhedron A b = ⋂ i : Fin m, {x : Fin n → ℝ | dotProduct (A i) x ≤ b i} by
    ext x
    simp [polyhedron]]
  exact isClosed_iInter fun i : Fin m => isClosed_le (by fun_prop) continuous_const

/-- A nonnegative combination of active rows is a normal vector at the boundary point. -/
private lemma nonneg_active_combination_mem_normalCone {m : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x₀ : Fin n → ℝ) {y : Fin n → ℝ}
    (hy : ∃ μ : Fin m → ℝ,
      (∀ i, 0 ≤ μ i) ∧
      (∀ i, i ∉ activeSet A b x₀ → μ i = 0) ∧
      y = ∑ i, μ i • A i) :
    y ∈ normalCone (polyhedron A b) x₀ := by
  rcases hy with ⟨μ, hμ, hsupport, rfl⟩
  -- Unfold the normal-cone inequality and expand the dot product of the row combination.
  rw [normalCone]
  intro x hx
  rw [sum_dotProduct]
  refine Finset.sum_nonpos ?_
  intro i _
  by_cases hi : i ∈ activeSet A b x₀
  · -- Active rows compare `x` against the boundary equality at `x₀`.
    have hactive : dotProduct (A i) x₀ = b i := hi
    have hxle : dotProduct (A i) x ≤ b i := hx i
    have hdiff : dotProduct (A i) (x - x₀) ≤ 0 := by
      rw [dotProduct_sub]
      linarith
    have hterm : dotProduct (μ i • A i) (x - x₀) ≤ 0 := by
      rw [smul_dotProduct]
      simp only [smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (hμ i) hdiff
    simpa using hterm
  · -- Inactive rows carry zero coefficient by the support condition.
    have hmui : μ i = 0 := hsupport i hi
    simp [hmui]

/-- Any direction that decreases the active constraints stays feasible for a short forward segment.
-/
private lemma exists_polyhedron_segment_of_active_direction {m : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x₀ d : Fin n → ℝ)
    (hx₀ : x₀ ∈ polyhedron A b)
    (hdir : ∀ i, i ∈ activeSet A b x₀ → dotProduct (A i) d ≤ 0) :
    ∃ ε > 0, ∀ t : ℝ, 0 ≤ t → t ≤ ε → x₀ + t • d ∈ polyhedron A b := by
  classical
  let stepBound : Fin m → ℝ := fun i =>
    if hi : i ∈ activeSet A b x₀ then 1
    else if hnonpos : dotProduct (A i) d ≤ 0 then 1
    else min 1 ((b i - dotProduct (A i) x₀) / dotProduct (A i) d)
  let ε : ℝ := ∏ i, stepBound i
  have hstep_pos : ∀ i, 0 < stepBound i := by
    intro i
    -- Active or nonincreasing constraints accept unit step, and the remaining case uses the
    -- positive slack-to-slope ratio.
    dsimp [stepBound]
    by_cases hi : i ∈ activeSet A b x₀
    · simp [hi]
    · by_cases hnonpos : dotProduct (A i) d ≤ 0
      · simp [hi, hnonpos]
      · have hne : dotProduct (A i) x₀ ≠ b i := by
          simpa [activeSet] using hi
        have hslack : 0 < b i - dotProduct (A i) x₀ := by
          exact sub_pos.mpr <| lt_of_le_of_ne (hx₀ i) hne
        have hratio : 0 < (b i - dotProduct (A i) x₀) / dotProduct (A i) d := by
          exact div_pos hslack (lt_of_not_ge hnonpos)
        simp [hi, hnonpos, hratio, zero_lt_one]
  have hstep_nonneg : ∀ i, 0 ≤ stepBound i := fun i => (hstep_pos i).le
  have hstep_le_one : ∀ i, stepBound i ≤ 1 := by
    intro i
    -- The per-constraint bound is always at most `1`, which makes the product stay below each
    -- factor.
    dsimp [stepBound]
    by_cases hi : i ∈ activeSet A b x₀
    · simp [hi]
    · by_cases hnonpos : dotProduct (A i) d ≤ 0
      · simp [hi, hnonpos]
      · simp [hi, hnonpos]
  have hεpos : 0 < ε := by
    -- The common step size is positive because every individual bound is positive.
    dsimp [ε]
    exact Finset.prod_pos fun i _ => hstep_pos i
  have hε_le : ∀ i : Fin m, ε ≤ stepBound i := by
    intro i
    -- Factor the full product at `i` and bound the remaining product by `1`.
    have hrest_nonneg : 0 ≤ Finset.prod (Finset.univ.erase i) stepBound := by
      exact Finset.prod_nonneg fun j _ => hstep_nonneg j
    have hrest_le_one : Finset.prod (Finset.univ.erase i) stepBound ≤ 1 := by
      exact Finset.prod_le_one (fun j _ => hstep_nonneg j) fun j _ => hstep_le_one j
    calc
      ε = stepBound i * Finset.prod (Finset.univ.erase i) stepBound := by
        dsimp [ε]
        simpa [Finset.sdiff_singleton_eq_erase] using
          (Finset.prod_eq_mul_prod_diff_singleton (s := Finset.univ) (i := i) (by simp)
            (f := stepBound))
      _ ≤ stepBound i * 1 := by
        exact mul_le_mul_of_nonneg_left hrest_le_one (hstep_nonneg i)
      _ = stepBound i := by ring
  refine ⟨ε, hεpos, ?_⟩
  intro t ht0 htε
  -- Check each inequality separately using the common bound `ε`.
  simp [polyhedron]
  intro i
  have hti : t ≤ stepBound i := le_trans htε (hε_le i)
  by_cases hi : i ∈ activeSet A b x₀
  · -- Active constraints stay feasible because their directional derivative is nonpositive.
    have hactive : dotProduct (A i) x₀ = b i := by
      simpa [activeSet] using hi
    have hcalc : dotProduct (A i) (x₀ + t • d) = dotProduct (A i) x₀ + t * dotProduct (A i) d := by
      rw [dotProduct_add, dotProduct_smul]
      simp [smul_eq_mul]
    have htd : t * dotProduct (A i) d ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos ht0 (hdir i hi)
    linarith
  · by_cases hnonpos : dotProduct (A i) d ≤ 0
    · -- Inactive constraints with nonpositive derivative only get easier as `t` increases.
      have hcalc : dotProduct (A i) (x₀ + t • d) = dotProduct (A i) x₀ + t * dotProduct (A i) d := by
        rw [dotProduct_add, dotProduct_smul]
        simp [smul_eq_mul]
      have htd : t * dotProduct (A i) d ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos ht0 hnonpos
      linarith [hx₀ i]
    · -- If the derivative is positive, the product bound keeps the linearized inequality below
      -- the available slack.
      have hne : dotProduct (A i) x₀ ≠ b i := by
        simpa [activeSet] using hi
      have hslack : 0 < b i - dotProduct (A i) x₀ := by
        exact sub_pos.mpr <| lt_of_le_of_ne (hx₀ i) hne
      have hratio_pos : 0 < (b i - dotProduct (A i) x₀) / dotProduct (A i) d := by
        exact div_pos hslack (lt_of_not_ge hnonpos)
      have hratio_le :
          t ≤ (b i - dotProduct (A i) x₀) / dotProduct (A i) d := by
        have hti' : t ≤ min 1 ((b i - dotProduct (A i) x₀) / dotProduct (A i) d) := by
          simpa [stepBound, hi, hnonpos] using hti
        exact le_trans hti' (min_le_right _ _)
      have hmul : t * dotProduct (A i) d ≤ b i - dotProduct (A i) x₀ := by
        exact (le_div_iff₀ (lt_of_not_ge hnonpos)).mp hratio_le
      have hcalc : dotProduct (A i) (x₀ + t • d) = dotProduct (A i) x₀ + t * dotProduct (A i) d := by
        rw [dotProduct_add, dotProduct_smul]
        simp [smul_eq_mul]
      linarith [hmul]

/-- A normal vector is nonpositive on every direction that keeps all active inequalities
nonincreasing. -/
private lemma normalCone_nonpos_on_activeDirections {m : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x₀ : Fin n → ℝ) {y : Fin n → ℝ}
    (hx₀ : x₀ ∈ polyhedron A b) (hy : y ∈ normalCone (polyhedron A b) x₀) :
    ∀ d : Fin n → ℝ,
      (∀ i, i ∈ activeSet A b x₀ → dotProduct (A i) d ≤ 0) →
      dotProduct y d ≤ 0 := by
  intro d hdir
  -- Route correction: instead of separating `y` from the whole active-row cone first, we extract
  -- the polar inequality directly from short feasible segments.
  obtain ⟨ε, hεpos, hsegment⟩ :=
    exists_polyhedron_segment_of_active_direction A b x₀ d hx₀ hdir
  have hhalf_nonneg : 0 ≤ ε / 2 := by positivity
  have hhalf_le : ε / 2 ≤ ε := by nlinarith [hεpos]
  have hfeasible : x₀ + (ε / 2) • d ∈ polyhedron A b :=
    hsegment (ε / 2) hhalf_nonneg hhalf_le
  have hnormal : dotProduct y ((x₀ + (ε / 2) • d) - x₀) ≤ 0 := hy _ hfeasible
  have hsub : (x₀ + (ε / 2) • d) - x₀ = (ε / 2) • d := by
    ext i
    simp
  have hscaled : (ε / 2) * dotProduct y d ≤ 0 := by
    simpa [hsub, dotProduct_smul] using hnormal
  have hhalf_pos : 0 < ε / 2 := by positivity
  nlinarith [hscaled, hhalf_pos]

/-- The coordinatewise bilinear form on `Fin n → ℝ` recovers `dotProduct`. -/
private noncomputable def dotProductBilin : LinearMap.BilinForm ℝ (Fin n → ℝ) :=
  ∑ i : Fin n, LinearMap.BilinForm.linMulLin (LinearMap.proj i) (LinearMap.proj i)

/-- Evaluating `dotProductBilin` is the usual dot product. -/
@[simp] private lemma dotProductBilin_apply (u v : Fin n → ℝ) :
    dotProductBilin (n := n) u v = dotProduct u v := by
  -- Expand the coordinatewise bilinear form into the defining sum for `dotProduct`.
  simp [dotProductBilin, dotProduct]

/-- The dual cone of a set in Euclidean space, written using the real inner product. -/
private def dualCone {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∀ x ∈ K, 0 ≤ ⟪y, x⟫}

/-- The coordinatewise nonnegative cone in `EuclideanSpace ℝ (Fin m)`. -/
private def positiveOrthant (m : ℕ) : ProperCone ℝ (EuclideanSpace ℝ (Fin m)) where
  toSubmodule :=
    PointedCone.ofConeComb
      {v : EuclideanSpace ℝ (Fin m) | ∀ i : Fin m, 0 ≤ v i}
      ⟨0, by simp⟩
      (by
        intro x hx y hy a ha b hb i
        exact add_nonneg (smul_nonneg ha (hx i)) (smul_nonneg hb (hy i)))
  isClosed' := by
    -- The positive orthant is the intersection of the coordinatewise closed half-spaces.
    have hclosed : IsClosed {v : EuclideanSpace ℝ (Fin m) | ∀ i : Fin m, 0 ≤ v i} := by
      classical
      rw [show ({v : EuclideanSpace ℝ (Fin m) | ∀ i : Fin m, 0 ≤ v i} :
          Set (EuclideanSpace ℝ (Fin m))) =
          ⋂ i : Fin m, {v : EuclideanSpace ℝ (Fin m) | (0 : ℝ) ≤ v i} by
        ext v
        simp]
      exact isClosed_iInter
        (fun i : Fin m => isClosed_le continuous_const (by fun_prop))
    exact hclosed

/-- Membership in the coordinatewise nonnegative cone is coordinatewise nonnegativity. -/
@[simp] private lemma mem_positiveOrthant {m : ℕ} {x : EuclideanSpace ℝ (Fin m)} :
    x ∈ positiveOrthant m ↔ ∀ i : Fin m, 0 ≤ x i := Iff.rfl

/-- The coordinatewise nonnegative cone is self-dual for the Euclidean inner product. -/
private lemma innerDual_positiveOrthant {m : ℕ} :
    ProperCone.innerDual (positiveOrthant m : Set (EuclideanSpace ℝ (Fin m))) =
      positiveOrthant m := by
  ext y
  constructor
  · intro hy
    rw [ProperCone.mem_innerDual] at hy
    -- Test the dual inequality on basis vectors to recover each coordinate of `y`.
    exact fun i => by
      have h := hy (x := EuclideanSpace.single i (1 : ℝ)) (by
        intro j
        by_cases hji : j = i
        · subst hji
          rw [EuclideanSpace.single_apply]
          positivity
        · rw [EuclideanSpace.single_apply]
          simp [hji])
      simpa [EuclideanSpace.inner_single_left] using h
  · intro hy
    rw [ProperCone.mem_innerDual]
    intro x hx
    -- Expand the inner product as a finite sum of nonnegative terms.
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hy i) (hx i)

/-- `Matrix.toEuclideanLin` agrees with `mulVec` on Euclidean-space coordinates. -/
private lemma toEuclideanLin_eq_mulVec {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin A x = A.mulVec x := by
  -- Read the bundled linear map back in coordinates.
  ext i
  rfl

/-- The adjoint of `Aᵀ` viewed as a Euclidean linear map is the map associated to `A`. -/
private lemma adjoint_toEuclideanLin_transpose {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ((Matrix.toEuclideanLin Aᵀ).toContinuousLinearMap).adjoint =
      (Matrix.toEuclideanLin A).toContinuousLinearMap := by
  -- Convert the continuous-adjoint statement back to the linear-map adjoint theorem.
  change (LinearMap.adjoint (Matrix.toEuclideanLin Aᵀ)).toContinuousLinearMap =
    (Matrix.toEuclideanLin A).toContinuousLinearMap
  simpa using congrArg LinearMap.toContinuousLinearMap
    (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := Aᵀ)).symm

/-- The abstract cone image from `relative_hyperplane_separation` is the closure of the explicit
transpose-image cone. -/
private lemma positiveOrthant_map_eq_closure_transpose_nonnegative_image
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ((positiveOrthant m).map ((Matrix.toEuclideanLin Aᵀ).toContinuousLinearMap) :
        Set (EuclideanSpace ℝ (Fin n))) =
      closure {y : EuclideanSpace ℝ (Fin n) |
        ∃ v : EuclideanSpace ℝ (Fin m), (∀ i : Fin m, 0 ≤ v i) ∧ y = Aᵀ.mulVec v} := by
  have himage :
      ((Matrix.toEuclideanLin Aᵀ) '' (positiveOrthant m : Set (EuclideanSpace ℝ (Fin m)))) =
        {y : EuclideanSpace ℝ (Fin n) |
          ∃ v : EuclideanSpace ℝ (Fin m), (∀ i : Fin m, 0 ≤ v i) ∧ y = Aᵀ.mulVec v} := by
    ext y
    constructor
    · rintro ⟨v, hv, hvy⟩
      have hmul : ((Matrix.toEuclideanLin Aᵀ) v).ofLp = Aᵀ *ᵥ v.ofLp := by
        exact toEuclideanLin_eq_mulVec Aᵀ v
      exact ⟨v, hv, (congrArg (fun z => z.ofLp) hvy).symm.trans hmul⟩
    · rintro ⟨v, hv, hvy⟩
      have hmul : ((Matrix.toEuclideanLin Aᵀ) v).ofLp = Aᵀ *ᵥ v.ofLp := by
        exact toEuclideanLin_eq_mulVec Aᵀ v
      refine ⟨v, hv, ?_⟩
      ext i
      exact congrArg (fun z : Fin n → ℝ => z i) (hmul.trans hvy.symm)
  -- `ProperCone.map` is defined as the closure of the pointed-cone image.
  simpa [ProperCone.coe_map, PointedCone.coe_map] using congrArg closure himage

/-- The dual cone of a coordinatewise nonnegative preimage is the closure of the transpose-image
cone. -/
private lemma dualCone_eq_closure_transpose_nonnegative_image
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    dualCone {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin m, 0 ≤ (A.mulVec x) i} =
      closure {y : EuclideanSpace ℝ (Fin n) |
        ∃ v : EuclideanSpace ℝ (Fin m), (∀ i : Fin m, 0 ≤ v i) ∧ y = Aᵀ.mulVec v} := by
  calc
    dualCone {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin m, 0 ≤ (A.mulVec x) i} =
        ((positiveOrthant m).map ((Matrix.toEuclideanLin Aᵀ).toContinuousLinearMap) :
          Set (EuclideanSpace ℝ (Fin n))) := by
          ext y
          -- Route correction: handle the closure issue through the positive-orthant image instead
          -- of asserting exact image membership before closedness has been proved.
          simpa [dualCone, adjoint_toEuclideanLin_transpose, innerDual_positiveOrthant,
            mem_positiveOrthant, toEuclideanLin_eq_mulVec, real_inner_comm,
            forall_and_left] using
            (ProperCone.relative_hyperplane_separation
              (C := positiveOrthant m)
              (f := (Matrix.toEuclideanLin Aᵀ).toContinuousLinearMap)
              (b := y)).symm
    _ = closure {y : EuclideanSpace ℝ (Fin n) |
        ∃ v : EuclideanSpace ℝ (Fin m), (∀ i : Fin m, 0 ≤ v i) ∧ y = Aᵀ.mulVec v} :=
      positiveOrthant_map_eq_closure_transpose_nonnegative_image A

/-- The `i`-th row of `A`, viewed as a Euclidean-space vector. -/
private noncomputable def rowVector {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (A i)

/-- The coordinate subspace consisting of vectors supported on a finite set `s`. -/
private noncomputable abbrev supportedSubmodule {m : ℕ} (s : Finset (Fin m)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin m)) :=
  ⨅ i : {i // i ∉ s}, LinearMap.ker (EuclideanSpace.projₗ (𝕜 := ℝ) (i := i.1))

/-- Membership in the supported subspace is equivalent to vanishing outside the support. -/
@[simp] private lemma mem_supportedSubmodule {m : ℕ}
    (s : Finset (Fin m)) (v : EuclideanSpace ℝ (Fin m)) :
    v ∈ supportedSubmodule s ↔ ∀ i ∉ s, v i = 0 := by
  -- Unfold the infimum of coordinate kernels into coordinatewise vanishing.
  simp [supportedSubmodule]

/-- Expand `Aᵀ.mulVec v` as a finite sum of row vectors. -/
private lemma transpose_mulVec_eq_sum_rows {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin m)) :
    Matrix.toEuclideanLin Aᵀ v = ∑ i : Fin m, v i • rowVector A i := by
  -- Compare coordinates and rewrite the matrix product as a row expansion.
  ext j
  simp [rowVector, Matrix.mulVec, dotProduct, mul_comm]

/-- For a supported vector, only the chosen support contributes to the row expansion. -/
private lemma sum_rows_eq_sum_rows_support {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin m)) (v : supportedSubmodule s) :
    ∑ i : Fin m, v.1 i • rowVector A i = ∑ i ∈ s, v.1 i • rowVector A i := by
  -- Terms outside `s` vanish because the vector is supported on `s`.
  refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
  intro i _ hi
  have hvi : v.1 i = 0 := (mem_supportedSubmodule s v.1).mp v.2 i hi
  simp [hvi]

/-- The transpose map is injective on vectors supported on an independent row family. -/
private lemma supported_row_map_ker_eq_bot {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin m))
    (hli : LinearIndepOn ℝ (fun i : Fin m => rowVector A i) s) :
    LinearMap.ker ((Matrix.toEuclideanLin Aᵀ).comp (supportedSubmodule s).subtype) = ⊥ := by
  ext v
  constructor
  · intro hv
    -- On the support, linear independence forces every coefficient to vanish.
    rw [Submodule.mem_bot]
    ext i
    by_cases hi : i ∈ s
    · have hsum : ∑ j ∈ s, v.1 j • rowVector A j = 0 := by
        simpa [transpose_mulVec_eq_sum_rows, sum_rows_eq_sum_rows_support] using hv
      exact (linearIndepOn_finset_iff.mp hli) (fun j => v.1 j) hsum i hi
    · exact (mem_supportedSubmodule s v.1).mp v.2 i hi
  · intro hv
    -- The converse direction is immediate from `v = 0`.
    have hv0 : v = 0 := by simpa [Submodule.mem_bot] using hv
    simp [hv0]

/-- The transpose map restricted to vectors supported on `s`. -/
private noncomputable def supportedRowMap {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin m)) :
    supportedSubmodule s →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (Matrix.toEuclideanLin Aᵀ).comp (supportedSubmodule s).subtype

/-- The cone generated by rows indexed by `s`, encoded via supported nonnegative coefficients. -/
private noncomputable def rowSubsetCone {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin m)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∃ v : supportedSubmodule s, (∀ i : Fin m, 0 ≤ v.1 i) ∧ y = supportedRowMap A s v}

/-- An independent-support row cone is closed as the image of a closed orthant under an injective
linear map. -/
private lemma isClosed_rowSubsetCone {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin m))
    (hli : LinearIndepOn ℝ (fun i : Fin m => rowVector A i) s) :
    IsClosed (rowSubsetCone A s) := by
  have hclosed : IsClosed {v : supportedSubmodule s | ∀ i : Fin m, 0 ≤ v.1 i} := by
    -- The supported orthant is an intersection of coordinatewise closed half-spaces.
    rw [show ({v : supportedSubmodule s | ∀ i : Fin m, 0 ≤ v.1 i} :
        Set (supportedSubmodule s)) =
        ⋂ i : Fin m, {v : supportedSubmodule s | (0 : ℝ) ≤ v.1 i} by
      ext v
      simp]
    exact isClosed_iInter (fun i : Fin m => isClosed_le continuous_const (by fun_prop))
  have himage :
      rowSubsetCone A s =
        supportedRowMap A s '' {v : supportedSubmodule s | ∀ i : Fin m, 0 ≤ v.1 i} := by
    -- Rewrite the cone as the image of the supported orthant.
    ext y
    simp [rowSubsetCone, supportedRowMap, eq_comm]
  rw [himage]
  exact
    (LinearMap.isClosedEmbedding_of_injective (supported_row_map_ker_eq_bot A s hli)).isClosedMap
      _ hclosed

/-- Any supported row-cone witness is also a witness for the full transpose-image cone. -/
private lemma rowSubsetCone_subset_transpose_image {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin m)) :
    rowSubsetCone A s ⊆
      {y : EuclideanSpace ℝ (Fin n) |
        ∃ v : EuclideanSpace ℝ (Fin m), (∀ i : Fin m, 0 ≤ v i) ∧ y = Aᵀ.mulVec v} := by
  rintro y ⟨v, hvnonneg, rfl⟩
  -- Forget the support restriction and reuse the same coefficient vector in the ambient space.
  refine ⟨v.1, hvnonneg, ?_⟩
  simp [supportedRowMap]

/-- A nonnegative coefficient vector belongs to the row cone generated by its nonzero support. -/
private lemma rowSubsetCone_of_nonnegative_support {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {y : EuclideanSpace ℝ (Fin n)}
    (v : EuclideanSpace ℝ (Fin m)) (hvnonneg : ∀ i : Fin m, 0 ≤ v i)
    (hy : y = Aᵀ.mulVec v) :
    y ∈ rowSubsetCone A (Finset.univ.filter fun i : Fin m => v i ≠ 0) := by
  classical
  let s : Finset (Fin m) := Finset.univ.filter fun i : Fin m => v i ≠ 0
  have hvsupport : v ∈ supportedSubmodule s := by
    -- Coordinates outside the filtered support vanish by definition.
    rw [mem_supportedSubmodule]
    intro i hi
    by_cases hvi : v i = 0
    · exact hvi
    · exfalso
      exact hi (by simp [s, hvi])
  refine ⟨⟨v, hvsupport⟩, hvnonneg, ?_⟩
  change y = Matrix.toEuclideanLin Aᵀ v
  ext i
  simpa [toEuclideanLin_eq_mulVec] using congrArg (fun z : Fin n → ℝ => z i) hy

/-- If a supported row-cone witness has a zero coefficient at `i`, it already belongs to the cone
with `i` erased from the support. -/
private lemma rowSubsetCone_erase_of_zero_coordinate {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {s : Finset (Fin m)} {y : EuclideanSpace ℝ (Fin n)}
    (v : supportedSubmodule s) (hvnonneg : ∀ i : Fin m, 0 ≤ v.1 i)
    (hy : y = supportedRowMap A s v) {i : Fin m} (_hi : i ∈ s) (hvi : v.1 i = 0) :
    y ∈ rowSubsetCone A (s.erase i) := by
  have hvsupport : v.1 ∈ supportedSubmodule (s.erase i) := by
    -- Off the erased support, either we were already outside `s` or we are at the new zero
    -- coordinate.
    rw [mem_supportedSubmodule]
    intro j hj
    by_cases hji : j = i
    · simpa [hji] using hvi
    · exact (mem_supportedSubmodule s v.1).mp v.2 j (by
        intro hjs
        exact hj (Finset.mem_erase.mpr ⟨hji, hjs⟩))
  refine ⟨⟨v.1, hvsupport⟩, hvnonneg, ?_⟩
  simpa [supportedRowMap] using hy

/-- A dependent positive-support row representation can be shrunk to a strict subset. -/
private lemma rowSubsetCone_shrink_of_dependent {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {s : Finset (Fin m)} {y : EuclideanSpace ℝ (Fin n)}
    (v : supportedSubmodule s) (hvnonneg : ∀ i : Fin m, 0 ≤ v.1 i)
    (hvpos : ∀ i ∈ s, 0 < v.1 i) (hy : y = supportedRowMap A s v)
    (hdep : ¬ LinearIndepOn ℝ (fun i : Fin m => rowVector A i) s) :
    ∃ i ∈ s, y ∈ rowSubsetCone A (s.erase i) := by
  classical
  -- Extract a nontrivial linear relation among the rows indexed by `s`.
  rw [not_linearIndepOn_finset_iff] at hdep
  rcases hdep with ⟨f, hfsum, i₀, hi₀s, hfi₀⟩
  -- Reorient the relation so that some coefficient becomes strictly positive.
  let g : Fin m → ℝ := if ∃ i ∈ s, 0 < f i then f else fun i => -f i
  have hgsum : ∑ i ∈ s, g i • rowVector A i = 0 := by
    by_cases hpos : ∃ i ∈ s, 0 < f i
    · simp [g, hpos, hfsum]
    · have : ∑ i ∈ s, (-f i) • rowVector A i = 0 := by
        simpa [neg_smul, Finset.sum_neg_distrib] using congrArg Neg.neg hfsum
      simpa [g, hpos] using this
  have hgpos : ∃ i ∈ s, 0 < g i := by
    by_cases hpos : ∃ i ∈ s, 0 < f i
    · simp [g, hpos]
    · have hfi₀_neg : f i₀ < 0 := lt_of_le_of_ne (le_of_not_gt fun hgt =>
        hpos ⟨i₀, hi₀s, hgt⟩) hfi₀
      exact ⟨i₀, hi₀s, by simpa [g, hpos] using neg_pos.mpr hfi₀_neg⟩
  let p : Finset (Fin m) := s.filter fun i => 0 < g i
  have hp_nonempty : p.Nonempty := by
    rcases hgpos with ⟨i, his, hgi⟩
    exact ⟨i, by simp [p, his, hgi]⟩
  -- Choose a positive relation coefficient minimizing the ratio `v i / g i`.
  obtain ⟨iStar, hiStarP, hmin⟩ := p.exists_min_image (fun i => v.1 i / g i) hp_nonempty
  have hiStarS : iStar ∈ s := (Finset.mem_filter.mp hiStarP).1
  have hgiStar : 0 < g iStar := (Finset.mem_filter.mp hiStarP).2
  let lam : ℝ := v.1 iStar / g iStar
  let c : EuclideanSpace ℝ (Fin m) :=
    (EuclideanSpace.equiv (Fin m) ℝ).symm fun i => if i ∈ s then g i else 0
  have hc_apply : ∀ i : Fin m, c i = if i ∈ s then g i else 0 := by
    intro i
    simp [c]
  have hcsum :
      ∑ i : Fin m, c i • rowVector A i = ∑ i ∈ s, g i • rowVector A i := by
    -- The correction vector agrees with `g` on `s` and vanishes outside `s`.
    calc
      ∑ i : Fin m, c i • rowVector A i = ∑ i ∈ s, c i • rowVector A i := by
        refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
        intro i _ hi
        have hci : c i = 0 := by
          rw [hc_apply i]
          simp [hi]
        simp [hci]
      _ = ∑ i ∈ s, g i • rowVector A i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [hc_apply i]
        simp [hi]
  have hcmap : Matrix.toEuclideanLin Aᵀ c = 0 := by
    -- Convert the dependence relation into a vanishing transpose image.
    simpa [transpose_mulVec_eq_sum_rows, hcsum] using hgsum
  let wFun : EuclideanSpace ℝ (Fin m) := v.1 - lam • c
  have hw_support : wFun ∈ supportedSubmodule s := by
    -- The correction is supported on `s`, so the adjusted vector stays supported there.
    rw [mem_supportedSubmodule]
    intro i hi
    have hvi : v.1 i = 0 := (mem_supportedSubmodule s v.1).mp v.2 i hi
    have hci : c i = 0 := by
      rw [hc_apply i]
      simp [hi]
    simp [wFun, hvi, hci]
  let w : supportedSubmodule s := ⟨wFun, hw_support⟩
  have hlam_nonneg : 0 ≤ lam := by
    exact div_nonneg (le_of_lt (hvpos iStar hiStarS)) (le_of_lt hgiStar)
  have hw_nonneg : ∀ i : Fin m, 0 ≤ w.1 i := by
    intro i
    by_cases his : i ∈ s
    · by_cases hgi : 0 < g i
      · have hip : i ∈ p := by simp [p, his, hgi]
        have hratio : lam ≤ v.1 i / g i := by
          simpa [lam] using hmin i hip
        have hmul : lam * g i ≤ v.1 i := by
          calc
            lam * g i ≤ (v.1 i / g i) * g i :=
              mul_le_mul_of_nonneg_right hratio (le_of_lt hgi)
            _ = v.1 i := by
              rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ (show g i ≠ 0 from ne_of_gt hgi),
                mul_one]
        have hci : c i = g i := by
          rw [hc_apply i]
          simp [his]
        -- Minimality of the ratio keeps every positive-support coordinate nonnegative.
        simpa [w, wFun, hci] using sub_nonneg.mpr hmul
      · have hmul : lam * g i ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hlam_nonneg (le_of_not_gt hgi)
        have : 0 ≤ v.1 i - lam * g i := by
          linarith [hvnonneg i, hmul]
        have hci : c i = g i := by
          rw [hc_apply i]
          simp [his]
        simpa [w, wFun, hci] using this
    · have hvi : v.1 i = 0 := (mem_supportedSubmodule s v.1).mp v.2 i his
      have hci : c i = 0 := by
        rw [hc_apply i]
        simp [his]
      -- Outside the support, both the original vector and the correction vanish.
      simp [w, wFun, hvi, hci]
  have hwiStar : w.1 iStar = 0 := by
    -- The minimizing coordinate hits zero exactly.
    have hciStar : c iStar = g iStar := by
      rw [hc_apply iStar]
      simp [hiStarS]
    calc
      w.1 iStar = v.1 iStar - lam * g iStar := by simp [w, wFun, hciStar]
      _ = 0 := by
        simp [lam, div_eq_mul_inv, ne_of_gt hgiStar]
  have hyw : y = supportedRowMap A s w := by
    -- The correction lies in the kernel because it is built from a dependence relation.
    calc
      y = supportedRowMap A s v := hy
      _ = Matrix.toEuclideanLin Aᵀ v.1 := rfl
      _ = Matrix.toEuclideanLin Aᵀ w.1 := by
            change Matrix.toEuclideanLin Aᵀ v.1 =
              Matrix.toEuclideanLin Aᵀ (v.1 - lam • c)
            rw [LinearMap.map_sub, LinearMap.map_smul, hcmap, smul_zero, sub_zero]
      _ = supportedRowMap A s w := rfl
  exact ⟨iStar, hiStarS,
    rowSubsetCone_erase_of_zero_coordinate A w hw_nonneg hyw hiStarS hwiStar⟩

/-- Every point in the transpose-image cone admits a representation on an independent support. -/
private lemma exists_independent_rowSubsetCone {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ {y : EuclideanSpace ℝ (Fin n) |
      ∃ v : EuclideanSpace ℝ (Fin m), (∀ i : Fin m, 0 ≤ v i) ∧ y = Aᵀ.mulVec v}) :
    ∃ s : Finset (Fin m), LinearIndepOn ℝ (fun i : Fin m => rowVector A i) s ∧
      y ∈ rowSubsetCone A s := by
  classical
  rcases hy with ⟨v₀, hv₀nonneg, hy₀⟩
  let s₀ : Finset (Fin m) := Finset.univ.filter fun i : Fin m => v₀ i ≠ 0
  have hs₀cone : y ∈ rowSubsetCone A s₀ := by
    -- Start from the obvious support of the original nonnegative witness.
    exact rowSubsetCone_of_nonnegative_support A v₀ hv₀nonneg hy₀
  let candidates : Finset (Finset (Fin m)) := s₀.powerset.filter fun s =>
    y ∈ rowSubsetCone A s
  have hs₀cand : s₀ ∈ candidates := by
    -- The initial support is one admissible candidate.
    simp [candidates, s₀, hs₀cone]
  obtain ⟨s, hsCand, hsMin⟩ := candidates.exists_min_image Finset.card ⟨s₀, hs₀cand⟩
  have hs_subset : s ⊆ s₀ := (Finset.mem_powerset.mp ((Finset.mem_filter.mp hsCand).1))
  have hy_s : y ∈ rowSubsetCone A s := (Finset.mem_filter.mp hsCand).2
  rcases hy_s with ⟨v, hvnonneg, hyv⟩
  have hvpos : ∀ i ∈ s, 0 < v.1 i := by
    intro i hi
    -- A zero coefficient would let us erase `i` and contradict minimality.
    have hnonneg := hvnonneg i
    by_contra hnot
    have hzero : v.1 i = 0 := by linarith
    have hy_erase : y ∈ rowSubsetCone A (s.erase i) :=
      rowSubsetCone_erase_of_zero_coordinate A v hvnonneg hyv hi hzero
    have hs_erase_subset : s.erase i ⊆ s₀ := (Finset.erase_subset i s).trans hs_subset
    have hs_erase_cand : s.erase i ∈ candidates := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hs_erase_subset, hy_erase⟩
    exact (not_lt_of_ge (hsMin (s.erase i) hs_erase_cand)) (Finset.card_erase_lt_of_mem hi)
  by_cases hsli : LinearIndepOn ℝ (fun i : Fin m => rowVector A i) s
  · exact ⟨s, hsli, ⟨v, hvnonneg, hyv⟩⟩
  · -- Route correction: a dependent minimal support contradicts the shrink lemma.
    obtain ⟨i, hi, hy_erase⟩ := rowSubsetCone_shrink_of_dependent A v hvnonneg hvpos hyv hsli
    have hs_erase_subset : s.erase i ⊆ s₀ := (Finset.erase_subset i s).trans hs_subset
    have hs_erase_cand : s.erase i ∈ candidates := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hs_erase_subset, hy_erase⟩
    exact False.elim <|
      (not_lt_of_ge (hsMin (s.erase i) hs_erase_cand)) (Finset.card_erase_lt_of_mem hi)

/-- The transpose-image cone of the coordinatewise nonnegative orthant is closed. -/
private lemma isClosed_transpose_nonnegative_image
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    IsClosed {y : EuclideanSpace ℝ (Fin n) |
      ∃ v : EuclideanSpace ℝ (Fin m), (∀ i : Fin m, 0 ≤ v i) ∧ y = Aᵀ.mulVec v} := by
  classical
  let supports : Finset (Finset (Fin m)) :=
    Finset.univ.powerset.filter fun s =>
      LinearIndepOn ℝ (fun i : Fin m => rowVector A i) s
  have hEq :
      {y : EuclideanSpace ℝ (Fin n) |
        ∃ v : EuclideanSpace ℝ (Fin m), (∀ i : Fin m, 0 ≤ v i) ∧ y = Aᵀ.mulVec v} =
      ⋃ s ∈ supports, rowSubsetCone A s := by
    ext y
    constructor
    · intro hy
      -- Use support shrinking to land in one closed independent-support piece.
      obtain ⟨s, hsli, hys⟩ := exists_independent_rowSubsetCone A hy
      exact Set.mem_iUnion₂.2 ⟨s, by simp [supports, hsli], hys⟩
    · intro hy
      -- Every independent-support piece lies in the full transpose image cone.
      rw [Set.mem_iUnion₂] at hy
      rcases hy with ⟨s, _, hys⟩
      exact rowSubsetCone_subset_transpose_image A s hys
  rw [hEq]
  exact isClosed_biUnion_finset fun s hs =>
    isClosed_rowSubsetCone A s ((by simpa [supports] using hs) : _)

/-- Finite-dimensional Farkas lemma for the coordinatewise nonnegative matrix preimage. -/
private theorem dualCone_of_nonnegative_preimage_eq_range_transpose_nonnegative
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    dualCone {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin m, 0 ≤ (A.mulVec x) i} =
      {y : EuclideanSpace ℝ (Fin n) |
        ∃ v : EuclideanSpace ℝ (Fin m), (∀ i : Fin m, 0 ≤ v i) ∧ y = Aᵀ.mulVec v} := by
  -- Reduce exact image membership to the closedness of the explicit transpose-image cone.
  rw [dualCone_eq_closure_transpose_nonnegative_image]
  exact (isClosed_transpose_nonnegative_image A).closure_eq

/-- The cone generated by the active rows, written in the same coefficient form as the theorem
statement. -/
private def activeRowCone {m : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x₀ : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {y | ∃ μ : Fin m → ℝ,
    (∀ i, 0 ≤ μ i) ∧
    (∀ i, i ∉ activeSet A b x₀ → μ i = 0) ∧
    y = ∑ i, μ i • A i}

/-- Each active row belongs to the active-row cone via the Kronecker-delta coefficients. -/
private lemma activeRow_mem_activeRowCone {m : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x₀ : Fin n → ℝ)
    {i : Fin m} (hi : i ∈ activeSet A b x₀) :
    A i ∈ activeRowCone A b x₀ := by
  -- Use the coefficient family that is `1` on the chosen active row and `0` elsewhere.
  refine ⟨fun j => if j = i then 1 else 0, ?_, ?_, ?_⟩
  · -- These coefficients are coordinatewise nonnegative.
    intro j
    by_cases hji : j = i
    · simp [hji]
    · simp [hji]
  · -- Inactive rows still carry coefficient `0`.
    intro j hj
    by_cases hji : j = i
    · subst hji
      exact (hj hi).elim
    · simp [hji]
  · -- Only the chosen active row survives the finite sum.
    classical
    simp

/-- The active-row matrix keeps only the rows of `A` that are tight at `x₀`. -/
private def activeMatrix {m : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x₀ : Fin n → ℝ) :
    Matrix {i : Fin m // i ∈ activeSet A b x₀} (Fin n) ℝ :=
  fun i k => A i.1 k

/-- Multiplying the active-row matrix by a direction just restricts the ambient row pairing to the
active indices. -/
@[simp] private lemma mulVec_activeMatrix {m : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x₀ d : Fin n → ℝ)
    (i : {i : Fin m // i ∈ activeSet A b x₀}) :
    Matrix.mulVec (activeMatrix A b x₀) d i = dotProduct (A i.1) d := by
  simp [activeMatrix, Matrix.mulVec, dotProduct]

/-- Extend multipliers on the active set by zero outside the active constraints. -/
private def extendByZero {m : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x₀ : Fin n → ℝ)
    (μ : {i : Fin m // i ∈ activeSet A b x₀} → ℝ) :
    Fin m → ℝ := by
  classical
  exact fun i => if hi : i ∈ activeSet A b x₀ then μ ⟨i, hi⟩ else 0

/-- The zero extension is nonnegative when the active multipliers are nonnegative. -/
private lemma extendByZero_nonneg {m : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x₀ : Fin n → ℝ)
    {μ : {i : Fin m // i ∈ activeSet A b x₀} → ℝ}
    (hμ : ∀ i, 0 ≤ μ i) :
    ∀ i : Fin m, 0 ≤ extendByZero A b x₀ μ i := by
  classical
  intro i
  -- On active indices we read off `μ`; elsewhere the extension is zero.
  by_cases hi : i ∈ activeSet A b x₀
  · simp [extendByZero, hi, hμ ⟨i, hi⟩]
  · simp [extendByZero, hi]

/-- On active indices, the zero extension agrees with the original multiplier. -/
private lemma extendByZero_eq_active {m : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x₀ : Fin n → ℝ)
    (μ : {i : Fin m // i ∈ activeSet A b x₀} → ℝ)
    (i : {i : Fin m // i ∈ activeSet A b x₀}) :
    extendByZero A b x₀ μ i.1 = μ i := by
  classical
  simp [extendByZero, i.2]

/-- Outside the active set, the zero extension vanishes. -/
private lemma extendByZero_eq_zero_of_inactive {m : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x₀ : Fin n → ℝ)
    (μ : {i : Fin m // i ∈ activeSet A b x₀} → ℝ)
    {i : Fin m} (hi : i ∉ activeSet A b x₀) :
    extendByZero A b x₀ μ i = 0 := by
  classical
  simp [extendByZero, hi]

/-- If a vector is nonpositive on all active-feasible directions, then it lies in the bipolar of the
active-row cone for the dot-product pairing. -/
private lemma mem_activeRowCone_bipolar_of_normal {m : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x₀ : Fin n → ℝ) {y : Fin n → ℝ}
    (hpolar :
      ∀ d : Fin n → ℝ,
        (∀ i, i ∈ activeSet A b x₀ → dotProduct (A i) d ≤ 0) →
        dotProduct y d ≤ 0) :
    y ∈ PointedCone.dual (dotProductBilin (n := n)).flip
      (PointedCone.dual (dotProductBilin (n := n)) (activeRowCone A b x₀)) := by
  -- Unfold the bipolar condition and test an arbitrary dual vector against the active generators.
  rw [PointedCone.mem_dual]
  intro d hd
  have hactive_nonneg :
      ∀ i, i ∈ activeSet A b x₀ → 0 ≤ dotProduct (A i) d := by
    intro i hi
    have hrow : A i ∈ activeRowCone A b x₀ := activeRow_mem_activeRowCone A b x₀ hi
    simpa [dotProductBilin_apply] using hd hrow
  have hpolar_neg :
      dotProduct y (-d) ≤ 0 := by
    -- Feed `-d` into the polar inequality so that the active-row dual constraints flip sign.
    apply hpolar (-d)
    intro i hi
    have hi' : 0 ≤ dotProduct (A i) d := hactive_nonneg i hi
    simpa using neg_nonpos.mpr hi'
  -- Rewriting the bilinear form on `d` and `y` turns the polar inequality into dual membership.
  simpa [dotProductBilin_apply] using neg_nonneg.mpr hpolar_neg

/-- Finite-dimensional Farkas/bipolar theorem for the active-row cone. This is the exact remaining
bridge from the already-proved polar inequality to the desired coefficient representation. -/
private lemma activeRowCone_eq_bipolar {m : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x₀ : Fin n → ℝ) :
    PointedCone.dual (dotProductBilin (n := n)).flip
        (PointedCone.dual (dotProductBilin (n := n)) (activeRowCone A b x₀)) =
      activeRowCone A b x₀ := by
  classical
  refine le_antisymm ?_ (PointedCone.subset_dual_dual (p := dotProductBilin (n := n)))
  intro y hy
  change y ∈ PointedCone.dual (dotProductBilin (n := n)).flip
    (PointedCone.dual (dotProductBilin (n := n)) (activeRowCone A b x₀)) at hy
  rw [PointedCone.mem_dual] at hy
  let eI : {i : Fin m // i ∈ activeSet A b x₀} ≃
      Fin (Fintype.card {i : Fin m // i ∈ activeSet A b x₀}) := Fintype.equivFin _
  let Aact : Matrix (Fin (Fintype.card {i : Fin m // i ∈ activeSet A b x₀})) (Fin n) ℝ :=
    fun i k => A (eI.symm i).1 k
  let yE : EuclideanSpace ℝ (Fin n) := (EuclideanSpace.equiv (Fin n) ℝ).symm y
  have hyDualCone :
      yE ∈ dualCone {d : EuclideanSpace ℝ (Fin n) |
        ∀ i : Fin (Fintype.card {i : Fin m // i ∈ activeSet A b x₀}), 0 ≤ Matrix.mulVec Aact d i} := by
    rw [dualCone]
    intro d hd
    have hdDual :
        (d : Fin n → ℝ) ∈ PointedCone.dual (dotProductBilin (n := n)) (activeRowCone A b x₀) := by
      rw [PointedCone.mem_dual]
      intro z hz
      rcases hz with ⟨μ, hμnonneg, hμsupport, rfl⟩
      -- Active coefficients pair nonnegatively with `d`, while inactive coefficients vanish.
      rw [dotProductBilin_apply, sum_dotProduct]
      refine Finset.sum_nonneg ?_
      intro i _
      by_cases hi : i ∈ activeSet A b x₀
      · have hrow : 0 ≤ dotProduct (A i) d := by
          simpa [Aact, Matrix.mulVec, dotProduct] using hd (eI ⟨i, hi⟩)
        rw [smul_dotProduct]
        simp only [smul_eq_mul]
        exact mul_nonneg (hμnonneg i) hrow
      · have hμi : μ i = 0 := hμsupport i hi
        simp [hμi]
    -- Route correction: translate bipolar membership into the Euclidean dual cone of the active
    -- subsystem, then use the exact transpose-image description instead of an abstract closure
    -- argument on `activeRowCone` itself.
    have hdot : 0 ≤ dotProductBilin (n := n) y (d : Fin n → ℝ) := hy hdDual
    simpa [yE, dotProductBilin_apply, PiLp.inner_apply, RCLike.inner_apply, dotProduct, mul_comm]
      using hdot
  have himage :
      yE ∈ {z : EuclideanSpace ℝ (Fin n) |
        ∃ v : EuclideanSpace ℝ (Fin (Fintype.card {i : Fin m // i ∈ activeSet A b x₀})),
          (∀ i : Fin (Fintype.card {i : Fin m // i ∈ activeSet A b x₀}), 0 ≤ v i) ∧ z = Aactᵀ.mulVec v} := by
    let hEq := dualCone_of_nonnegative_preimage_eq_range_transpose_nonnegative Aact
    simpa [hEq] using hyDualCone
  rcases himage with ⟨μFin, hμ_nonneg, hμA⟩
  let μ : {i : Fin m // i ∈ activeSet A b x₀} → ℝ := fun i => μFin (eI i)
  have hμA_subtype : Matrix.mulVec (activeMatrix A b x₀)ᵀ μ = y := by
    ext k
    have hcoord :
        y k =
          ∑ j : Fin (Fintype.card {i : Fin m // i ∈ activeSet A b x₀}),
            A (eI.symm j).1 k * μFin j := by
      simpa [Aact, yE, Matrix.mulVec, dotProduct] using
        congrArg (fun v : Fin n → ℝ => v k) hμA
    calc
      (Matrix.mulVec (activeMatrix A b x₀)ᵀ μ) k =
          ∑ i : {i : Fin m // i ∈ activeSet A b x₀}, A i.1 k * μ i := by
        rfl
      _ = ∑ j : Fin (Fintype.card {i : Fin m // i ∈ activeSet A b x₀}),
            A (eI.symm j).1 k * μFin j := by
        simpa [μ] using
          (Equiv.sum_comp eI
            (fun j : Fin (Fintype.card {i : Fin m // i ∈ activeSet A b x₀}) =>
              A (eI.symm j).1 k * μFin j))
      _ = y k := hcoord.symm
  let μExt : Fin m → ℝ := extendByZero A b x₀ μ
  have hμ_nonneg_subtype : ∀ i : {i : Fin m // i ∈ activeSet A b x₀}, 0 ≤ μ i := by
    intro i
    simpa [μ] using hμ_nonneg (eI i)
  have hsum_subtype_coord :
      ∀ k : Fin n, ∑ i : {i : Fin m // i ∈ activeSet A b x₀}, A i.1 k * μ i = y k := by
    intro k
    calc
      ∑ i : {i : Fin m // i ∈ activeSet A b x₀}, A i.1 k * μ i =
          (Matrix.mulVec (activeMatrix A b x₀)ᵀ μ) k := by
        simp [Matrix.mulVec, activeMatrix, dotProduct]
      _ = y k := by
        exact congrArg (fun v : Fin n → ℝ => v k) hμA_subtype
  refine ⟨μExt, extendByZero_nonneg A b x₀ hμ_nonneg_subtype, ?_, ?_⟩
  · intro i hi
    simpa [μExt] using extendByZero_eq_zero_of_inactive A b x₀ μ hi
  · -- Convert the transpose-image equality back to the explicit active-row sum.
    ext k
    calc
      y k = ∑ i : {i : Fin m // i ∈ activeSet A b x₀}, A i.1 k * μ i := by
        exact (hsum_subtype_coord k).symm
      _ = Finset.sum ((Finset.univ : Finset (Fin m)).filter fun i => i ∈ activeSet A b x₀)
          (fun i => A i k * μExt i) := by
        symm
        simpa [μExt, extendByZero_eq_active] using
          (Finset.sum_subtype_eq_sum_filter
            (s := Finset.univ)
            (p := fun i : Fin m => i ∈ activeSet A b x₀)
            (f := fun i : Fin m => A i k * μExt i)).symm
      _ = ∑ i : Fin m, A i k * μExt i := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro i _
        by_cases hi : i ∈ activeSet A b x₀
        · simp [μExt, extendByZero, hi]
        · simp [μExt, extendByZero, hi]
      _ = (∑ i : Fin m, μExt i • A i) k := by
        simp [smul_eq_mul, mul_comm]

/-
Let C ⊆ ℝ^n and let x₀ ∈ ∂ C. Define the normal cone of C at x₀ by N_C(x₀): = {y ∈ ℝ^n | yᵀ(x - x₀)
≤
0 for all x ∈ C}. Prove that N_C(x₀) is a convex cone.
-/
theorem normalCone_is_convex_cone (C : Set (Fin n → ℝ)) (x₀ : Fin n → ℝ) :
    Convex ℝ (normalCone C x₀) ∧
      ∀ ⦃y : Fin n → ℝ⦄, y ∈ normalCone C x₀ → ∀ a : ℝ, 0 ≤ a → a • y ∈ normalCone C x₀ := by
  constructor
  · -- Use the convex-combination characterization of convexity.
    rw [convex_iff_add_mem]
    intro y₁ hy₁ y₂ hy₂ a b ha hb hab
    -- Unfold the normal-cone condition and test it at an arbitrary point of `C`.
    rw [normalCone] at hy₁ hy₂ ⊢
    intro x hx
    have hy₁x : dotProduct y₁ (x - x₀) ≤ 0 := hy₁ x hx
    have hy₂x : dotProduct y₂ (x - x₀) ≤ 0 := hy₂ x hx
    -- Rewrite the dot product of the convex combination using linearity.
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct]
    simp only [smul_eq_mul]
    -- The resulting scalar inequality is a nonnegative linear combination of two nonpositive terms.
    nlinarith
  · intro y hy a ha
    -- Unfold the normal-cone condition and evaluate it at an arbitrary point of `C`.
    rw [normalCone] at hy ⊢
    intro x hx
    have hyx : dotProduct y (x - x₀) ≤ 0 := hy x hx
    -- Rewrite the dot product through the scalar multiplication.
    rw [smul_dotProduct]
    simp only [smul_eq_mul]
    -- A nonnegative scalar multiple of a nonpositive real remains nonpositive.
    nlinarith

/-
Let P = {x ∈ ℝ^n | Ax preceq b}, where A ∈ ℝ^{m× n}, b ∈ ℝ^m, and Ax preceq b means (Ax)_i ≤ bᵢ for
i = 1, ..., m. Let x₀ ∈ ∂ P, and let I(x₀): = {i ∈ {1, ..., m} | a_iᵀ x₀ = bᵢ}, where a_iᵀ is the i
- th
row of A. Prove that N_P(x₀) = {\sum_{i ∈ I(x₀)} λ_i aᵢ | λ_i ≥ 0 for all i ∈ I(x₀)}.
-/
theorem normalCone_polyhedron_eq_nonneg_active_combinations {m : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x₀ : Fin n → ℝ) :
    x₀ ∈ frontier (polyhedron A b) →
    normalCone (polyhedron A b) x₀ =
      {y | ∃ μ : Fin m → ℝ,
        (∀ i, 0 ≤ μ i) ∧
        (∀ i, i ∉ activeSet A b x₀ → μ i = 0) ∧
        y = ∑ i, (μ i) • (A i)} := by
  intro hxFrontier
  have hx₀ : x₀ ∈ polyhedron A b := by
    -- The frontier of a closed set lies inside the set itself.
    exact (polyhedron_isClosed A b).frontier_subset hxFrontier
  ext y
  constructor
  · intro hy
    -- Route correction: the old route separated `y` from a closed active-row cone. The new route
    -- first proves that every normal vector is nonpositive on active-feasible directions, then
    -- packages that as bipolar membership for the active-row cone.
    have hpolar :
        ∀ d : Fin n → ℝ,
          (∀ i, i ∈ activeSet A b x₀ → dotProduct (A i) d ≤ 0) →
          dotProduct y d ≤ 0 :=
      normalCone_nonpos_on_activeDirections A b x₀ hx₀ hy
    have hyBipolar :
        y ∈ PointedCone.dual (dotProductBilin (n := n)).flip
          (PointedCone.dual (dotProductBilin (n := n)) (activeRowCone A b x₀)) :=
      mem_activeRowCone_bipolar_of_normal A b x₀ hpolar
    -- The remaining bridge is the finite-dimensional bipolar theorem for the active-row cone.
    have hBipolar :
        (PointedCone.dual (dotProductBilin (n := n)).flip
          (PointedCone.dual (dotProductBilin (n := n)) (activeRowCone A b x₀)) :
            Set (Fin n → ℝ)) =
          activeRowCone A b x₀ :=
      activeRowCone_eq_bipolar (A := A) (b := b) (x₀ := x₀)
    have hyBipolarSet :
        y ∈ (PointedCone.dual (dotProductBilin (n := n)).flip
          (PointedCone.dual (dotProductBilin (n := n)) (activeRowCone A b x₀)) :
            Set (Fin n → ℝ)) :=
      hyBipolar
    simpa [hBipolar] using hyBipolarSet
  · intro hy
    -- The forward inclusion is the direct active-row expansion proved above.
    exact nonneg_active_combination_mem_normalCone A b x₀ hy

end «problem-46»
