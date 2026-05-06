import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-74»

/- [BLOCK Exercise 8.14-(b) | 15 | defn]
An ellipsoid ∈ ℝ^n is a set of the form E = {c + Pu | ‖u‖_2 ≤ 1}, where c ∈ ℝ^n and P ∈ ℝ^{n×n} is
invertible.
-/
def ellipsoid (n : ℕ) (c : EuclideanSpace ℝ (Fin n)) (P : Matrix (Fin n) (Fin n) ℝ)
    (_hP : IsUnit P.det) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ 1 ∧ x = c + (P.mulVec u)}

/- [BLOCK Exercise 8.14-(b) | 16 | defn]
An ellipsoid E is inscribed in a set C if E ⊆ C.
-/
def inscribed {α : Type*} (E C : Set α) : Prop :=
  E ⊆ C

/-- The slab polytope cut out by the row inequalities `-1 ≤ A x ≤ 1`. -/
abbrev slabPolytope {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i : Fin m, (-1 : ℝ) ≤ (A.mulVec x) i ∧ (A.mulVec x) i ≤ (1 : ℝ)}

/-- A strict-feasibility witness belongs to the corresponding closed slab polytope. -/
lemma mem_slabPolytope_of_strict_bounds
    {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (hlower : ∀ i : Fin m, (-1 : ℝ) < (A.mulVec x) i)
    (hupper : ∀ i : Fin m, (A.mulVec x) i < (1 : ℝ)) :
    x ∈ slabPolytope A := by
  -- Passing from strict inequalities to weak inequalities puts the point in the closed slab.
  intro i
  constructor <;> linarith [hlower i, hupper i]

/-- The slab polytope is convex because each row inequality is preserved by convex combinations. -/
lemma slabPolytope_convex
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    Convex ℝ (slabPolytope A) := by
  -- Check the lower and upper row bounds after expanding `A (a • x + b • y)`.
  intro x hx y hy a b ha hb hab
  intro i
  have hofLp :
      (a • x + b • y).ofLp = a • x.ofLp + b • y.ofLp := by
    -- Coercions from `EuclideanSpace` to functions respect the pointwise vector-space operations.
    ext j
    simp
  have hmul :
      (A *ᵥ (a • x.ofLp + b • y.ofLp)) i = a * (A *ᵥ x.ofLp) i + b * (A *ᵥ y.ofLp) i := by
    -- Expand the `i`-th row and distribute the coefficients through the finite sum.
    calc
      (A *ᵥ (a • x.ofLp + b • y.ofLp)) i
          = ∑ j, A i j * (a * x.ofLp j + b * y.ofLp j) := by
              simp [Matrix.mulVec, dotProduct]
      _ = ∑ j, (a * (A i j * x.ofLp j) + b * (A i j * y.ofLp j)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
      _ = a * ∑ j, A i j * x.ofLp j + b * ∑ j, A i j * y.ofLp j := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = a * (A *ᵥ x.ofLp) i + b * (A *ᵥ y.ofLp) i := by
            simp [Matrix.mulVec, dotProduct]
  constructor
  · calc
      -1 ≤ a * (A.mulVec x) i + b * (A.mulVec y) i := by
        nlinarith [ha, hb, hab, (hx i).1, (hy i).1]
      _ = (A *ᵥ (a • x.ofLp + b • y.ofLp)) i := by
        symm
        exact hmul
      _ = (A.mulVec (a • x + b • y)) i := by
        rfl
  · calc
      (A.mulVec (a • x + b • y)) i = (A *ᵥ (a • x.ofLp + b • y.ofLp)) i := by
        rfl
      _ = a * (A.mulVec x) i + b * (A.mulVec y) i := hmul
      _ ≤ 1 := by
        nlinarith [ha, hb, hab, (hx i).2, (hy i).2]

/-- The strict slab cut out by `A` is open. -/
lemma isOpen_strictSlabPolytope
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    IsOpen {x : EuclideanSpace ℝ (Fin n) |
      ∀ i : Fin m, (-1 : ℝ) < (A.mulVec x) i ∧ (A.mulVec x) i < (1 : ℝ)} := by
  -- Each row constraint is the intersection of two open half-spaces, and there are only finitely many rows.
  have hmulVec : Continuous fun x : EuclideanSpace ℝ (Fin n) => A.mulVec x := by
    simpa using
      (continuous_const.matrix_mulVec
        (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)))
  have hrow :
      ∀ i : Fin m, IsOpen {x : EuclideanSpace ℝ (Fin n) |
        (-1 : ℝ) < (A.mulVec x) i ∧ (A.mulVec x) i < (1 : ℝ)} := by
    intro i
    have hcoord : Continuous fun x : EuclideanSpace ℝ (Fin n) => (A.mulVec x) i :=
      (continuous_apply i).comp hmulVec
    have hlower : IsOpen {x : EuclideanSpace ℝ (Fin n) | (-1 : ℝ) < (A.mulVec x) i} := by
      simpa using hcoord.isOpen_preimage (s := Set.Ioi (-1 : ℝ)) isOpen_Ioi
    have hupper : IsOpen {x : EuclideanSpace ℝ (Fin n) | (A.mulVec x) i < (1 : ℝ)} := by
      simpa using hcoord.isOpen_preimage (s := Set.Iio (1 : ℝ)) isOpen_Iio
    -- Combine the lower and upper open half-spaces for the `i`-th row.
    simpa [Set.setOf_and] using hlower.inter hupper
  have hopen :
      IsOpen (⋂ i : Fin m, {x : EuclideanSpace ℝ (Fin n) |
        (-1 : ℝ) < (A.mulVec x) i ∧ (A.mulVec x) i < (1 : ℝ)}) :=
    isOpen_iInter_of_finite hrow
  -- Rewrite the quantified strict slab as a finite intersection of the row-wise open constraints.
  convert hopen using 1
  ext x
  simp

/-- A strict-feasibility witness lies in the interior of the slab polytope. -/
lemma mem_interior_slabPolytope_of_strict_bounds
    {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (hlower : ∀ i : Fin m, (-1 : ℝ) < (A.mulVec x) i)
    (hupper : ∀ i : Fin m, (A.mulVec x) i < (1 : ℝ)) :
    x ∈ interior (slabPolytope A) := by
  let S : Set (EuclideanSpace ℝ (Fin n)) :=
    {y | ∀ i : Fin m, (-1 : ℝ) < (A.mulVec y) i ∧ (A.mulVec y) i < (1 : ℝ)}
  have hxS : x ∈ S := by
    -- The given strict inequalities place `x` in the open strict slab.
    intro i
    exact ⟨hlower i, hupper i⟩
  have hS_open : IsOpen S := by
    -- Route correction: instead of building an explicit Euclidean ball, use that the strict slab is open.
    simpa [S] using isOpen_strictSlabPolytope A
  have hS_subset : S ⊆ slabPolytope A := by
    intro y hy
    -- Every strict-feasible point is also feasible for the closed slab.
    exact mem_slabPolytope_of_strict_bounds (fun i => (hy i).1) (fun i => (hy i).2)
  -- An open subset of the slab is contained in its interior.
  exact interior_maximal hS_subset hS_open hxS

/-- The strict-feasibility hypothesis gives the slab polytope nonempty interior. -/
lemma slabPolytope_interior_nonempty
    {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    (hnonempty :
      ∃ x : EuclideanSpace ℝ (Fin n),
        (∀ i : Fin m, (-1 : ℝ) < (A.mulVec x) i) ∧
        (∀ i : Fin m, (A.mulVec x) i < (1 : ℝ))) :
    (interior (slabPolytope A)).Nonempty := by
  rcases hnonempty with ⟨x, hlower, hupper⟩
  -- The strict-feasibility witness lies in the interior by the previous lemma.
  exact ⟨x, mem_interior_slabPolytope_of_strict_bounds hlower hupper⟩

/-- Inscribedness in a slab polytope is equivalent to checking each row on unit-ball parameters. -/
lemma inscribed_ellipsoid_slab_rowwise_iff
    {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {c : EuclideanSpace ℝ (Fin n)}
    {P : Matrix (Fin n) (Fin n) ℝ}
    {hP : IsUnit P.det} :
    inscribed (ellipsoid n c P hP) (slabPolytope A) ↔
      ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ 1 →
        ∀ i : Fin m,
          (-1 : ℝ) ≤ (A.mulVec c) i + ((A * P).mulVec u) i ∧
            (A.mulVec c) i + ((A * P).mulVec u) i ≤ (1 : ℝ) := by
  constructor
  · intro h u hu i
    -- Evaluate the inscribed condition at the affine image of the unit-ball vector `u`.
    have hu_mem :
        (show EuclideanSpace ℝ (Fin n) from WithLp.toLp 2 (c.ofLp + P *ᵥ u.ofLp)) ∈
          ellipsoid n c P hP := by
      exact ⟨u, hu, by simp⟩
    have hmem :
        (show EuclideanSpace ℝ (Fin n) from WithLp.toLp 2 (c.ofLp + P *ᵥ u.ofLp)) ∈
          slabPolytope A := h hu_mem
    -- Expanding `A (c + P u)` gives the desired row-wise affine bounds.
    simpa [slabPolytope, Matrix.mulVec_add, Matrix.mulVec_mulVec, add_comm, add_left_comm,
      add_assoc] using hmem i
  · intro h x hx
    rcases hx with ⟨u, hu, hxu⟩
    have hxu' : x.ofLp = c.ofLp + P *ᵥ u.ofLp := by
      simpa using hxu
    intro i
    -- The row-wise unit-ball bounds imply that every ellipsoid point lies in the slab.
    simpa [hxu', slabPolytope, Matrix.mulVec_add, Matrix.mulVec_mulVec, add_comm, add_left_comm,
      add_assoc] using h u hu i

/-- Bounding a scalar affine functional on the Euclidean unit ball is equivalent to the support
estimate `|s| + ‖r‖ ≤ 1`. -/
lemma unit_ball_affine_bounds_iff_abs_add_norm_le_one
    {n : ℕ}
    {s : ℝ}
    {r : EuclideanSpace ℝ (Fin n)} :
    (∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ 1 →
      (-1 : ℝ) ≤ s + inner ℝ r u ∧ s + inner ℝ r u ≤ 1) ↔
      |s| + ‖r‖ ≤ 1 := by
  constructor
  · intro h
    by_cases hr : r = 0
    · -- When the linear part vanishes, the claim is exactly the scalar interval bound at `u = 0`.
      subst hr
      have h0 := h 0 (by simp)
      simpa using (abs_le.2 h0)
    · let u : EuclideanSpace ℝ (Fin n) := (‖r‖⁻¹ : ℝ) • r
      have hu_norm : ‖u‖ = 1 := by
        -- Normalize `r` to a unit vector so that the affine bound is tested in the extremal
        -- direction of the linear part.
        dsimp [u]
        simpa using norm_smul_inv_norm hr
      have hu : ‖u‖ ≤ 1 := by
        -- The normalized vector lies on the unit sphere, hence in the closed unit ball.
        simp [hu_norm]
      have hu' := h u hu
      have hneg_u := h (-u) (by simp [hu_norm])
      have hinner : inner ℝ r u = ‖r‖ := by
        -- In the normalized direction, the linear part reaches its norm.
        dsimp [u]
        rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp [norm_ne_zero_iff.mpr hr]
      have hs_upper : s ≤ 1 - ‖r‖ := by
        -- The upper unit-ball bound at `u` gives the upper scalar constraint on `s`.
        linarith [hu'.2, hinner]
      have hs_lower : ‖r‖ - 1 ≤ s := by
        -- The lower unit-ball bound at `-u` gives the matching lower scalar constraint on `s`.
        have hinner_neg : inner ℝ r (-u) = -‖r‖ := by
          simp [hinner]
        linarith [hneg_u.1, hinner_neg]
      have hs_abs : |s| ≤ 1 - ‖r‖ := by
        -- Combine the upper and lower scalar constraints into the absolute-value bound on `s`.
        rw [abs_le]
        constructor
        · linarith [hs_lower]
        · linarith [hs_upper]
      calc
        |s| + ‖r‖ ≤ (1 - ‖r‖) + ‖r‖ := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hs_abs ‖r‖
        _ = 1 := by ring
  · intro h u hu
    have hinner : |inner ℝ r u| ≤ ‖r‖ := by
      -- Cauchy-Schwarz bounds the linear part on the unit ball by the norm of `r`.
      calc
        |inner ℝ r u| ≤ ‖r‖ * ‖u‖ := abs_real_inner_le_norm r u
        _ ≤ ‖r‖ * 1 := by gcongr
        _ = ‖r‖ := by ring
    have habs : |s + inner ℝ r u| ≤ 1 := by
      -- The triangle inequality and the support estimate reduce the affine bound to `h`.
      calc
        |s + inner ℝ r u| ≤ |s| + |inner ℝ r u| := abs_add_le _ _
        _ ≤ |s| + ‖r‖ := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hinner |s|
        _ ≤ 1 := h
    exact abs_le.mp habs

/-- A radius-`n` inverse-coordinate bound yields membership in the `n`-scaled ellipsoid. -/
lemma mem_scaled_ellipsoid_of_norm_le
    {n : ℕ}
    (hn : 0 < n)
    {c x : EuclideanSpace ℝ (Fin n)}
    {P : Matrix (Fin n) (Fin n) ℝ} :
    (∃ y : EuclideanSpace ℝ (Fin n), ‖y‖ ≤ (n : ℝ) ∧ x.ofLp = c.ofLp + P *ᵥ y.ofLp) →
      ∃ u : EuclideanSpace ℝ (Fin n),
        ‖u‖ ≤ 1 ∧ x = c + ((n : ℝ) • (P.mulVec u)) := by
  intro hx
  rcases hx with ⟨y, hy, hxy⟩
  refine ⟨(n : ℝ)⁻¹ • y, ?_, ?_⟩
  · have hn_real : (0 : ℝ) < n := by
      exact_mod_cast hn
    -- Rescale the radius-`n` bound back to the unit ball.
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt hn_real))]
    have hscaled :
        (n : ℝ)⁻¹ * ‖y‖ ≤ (n : ℝ)⁻¹ * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr (le_of_lt hn_real))
    calc
      (n : ℝ)⁻¹ * ‖y‖ ≤ (n : ℝ)⁻¹ * (n : ℝ) := hscaled
      _ = 1 := by field_simp [hn_real.ne']
  · have hn_ne : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    -- Pull the scaling through `P.mulVec` and cancel `n * n⁻¹`.
    have hx_scaled :
        x.ofLp = c.ofLp + (n : ℝ) • (P *ᵥ (((n : ℝ)⁻¹ • y).ofLp)) := by
      calc
        x.ofLp = c.ofLp + P *ᵥ y.ofLp := hxy
        _ = c.ofLp + (((n : ℝ) * (n : ℝ)⁻¹) • (P *ᵥ y.ofLp)) := by
          simp [hn_ne]
        _ = c.ofLp + ((n : ℝ) • ((n : ℝ)⁻¹ • (P *ᵥ y.ofLp))) := by
          rw [smul_smul]
        _ = c.ofLp + (n : ℝ) • (P *ᵥ (((n : ℝ)⁻¹ • y).ofLp)) := by
          simp [Matrix.mulVec_smul]
    exact hx_scaled

/-- The anisotropic rank-one update acts by scaling the `v`-direction and leaving the orthogonal
complement scaled by `b`. -/
lemma directional_stretch_mulVec
    {n : ℕ}
    {a b : ℝ}
    {v u : EuclideanSpace ℝ (Fin n)} :
    let M : Matrix (Fin n) (Fin n) ℝ := b • 1 + (a - b) • Matrix.vecMulVec v.ofLp v.ofLp
    M *ᵥ u.ofLp = b • u.ofLp + (((a - b) * inner ℝ v u) • v.ofLp) := by
  -- Expand the matrix action and rewrite the rank-one term as the Euclidean projection onto `v`.
  dsimp
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  calc
    b • u.ofLp + (a - b) • (Matrix.vecMulVec v.ofLp v.ofLp *ᵥ u.ofLp)
        = b • u.ofLp + (a - b) • ((v.ofLp ⬝ᵥ u.ofLp) • v.ofLp) := by
            simp [Matrix.vecMulVec_mulVec]
    _ = b • u.ofLp + (((a - b) * inner ℝ v u) • v.ofLp) := by
          simp [PiLp.inner_apply, dotProduct, mul_comm, smul_smul]

/-- The John one-point enlargement parameters satisfy the exact quadratic identity used to
normalize the transported point back into the unit ball. -/
lemma one_point_weight_identity
    {n : ℕ}
    {t α : ℝ}
    (hn : 0 < n)
    (ht : (n : ℝ) < t) :
    let δ : ℝ := (t - n) / (n + 1)
    let a : ℝ := (t + 1) / (n + 1)
    let b2 : ℝ := ((n - 1 : ℝ) * (t + 1)) / ((n + 1) * (t - 1))
    let wgt : ℝ := δ * (1 + α) / (t - 1)
    (δ + a * α - wgt * t) ^ 2 + b2 * (1 - α ^ 2) = (1 - wgt) ^ 2 := by
  -- This is the scalar identity behind the explicit one-point enlargement.
  have hn_real : (0 : ℝ) < n := by
    exact_mod_cast hn
  have h_one_le : (1 : ℝ) ≤ n := by
    exact_mod_cast Nat.succ_le_of_lt hn
  have ht_one : (1 : ℝ) < t := lt_of_le_of_lt h_one_le ht
  have ht_sub_one_ne : t - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt ht_one)
  dsimp
  field_simp [ht_sub_one_ne]
  ring

/-- The anisotropic rank-one stretch has determinant `a * b^(n - 1)` along a unit direction. -/
lemma directional_stretch_det
    {n : ℕ}
    (hn : 0 < n)
    {a b : ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (hv_norm : ‖v‖ = 1) :
    let M : Matrix (Fin n) (Fin n) ℝ :=
      b • 1 + (a - b) • Matrix.vecMulVec v.ofLp v.ofLp
    M.det = a * b ^ (n - 1) := by
  rcases n with _ | n
  · cases Nat.lt_asymm hn hn
  · dsimp
    let V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.vecMulVec v.ofLp v.ofLp
    have hdot_norm : v.ofLp ⬝ᵥ v.ofLp = ‖v‖ ^ 2 := by
      calc
        v.ofLp ⬝ᵥ v.ofLp = ∑ i, v.ofLp i ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
        _ = ‖v‖ ^ 2 := by
          simpa using (EuclideanSpace.norm_sq_eq v).symm
    have hdot : v.ofLp ⬝ᵥ v.ofLp = 1 := by
      simpa [hv_norm] using hdot_norm
    have hchar :
        (((a - b) : ℝ) • V).charpoly =
          Polynomial.X ^ (n + 1) - ((a - b) : ℝ) • Polynomial.X ^ n := by
      simpa [V, hdot, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
        (Matrix.charpoly_vecMulVec (((a - b) : ℝ) • v.ofLp) v.ofLp)
    have heval :
        ((((a - b) : ℝ) • V).charpoly).eval (-b) = (-1 : ℝ) ^ (n + 1) * (a * b ^ n) := by
      rw [hchar]
      simp [pow_succ, sub_eq_add_neg, smul_eq_mul, mul_comm, mul_assoc]
      ring
    have hmatrix :
        ((((a - b) : ℝ) • V).charpoly).eval (-b) =
          (-1 : ℝ) ^ (n + 1) * (b • 1 + ((a - b) : ℝ) • V).det := by
      rw [Matrix.eval_charpoly]
      have hneg :
          Matrix.scalar (Fin (n + 1)) (-b) - ((a - b) : ℝ) • V =
            -(b • 1 + ((a - b) : ℝ) • V) := by
        ext i j
        by_cases hij : i = j
        · subst hij
          simp [Matrix.scalar, V, sub_eq_add_neg]
          ring
        · simp [Matrix.scalar, hij, V, sub_eq_add_neg]
      rw [hneg, Matrix.det_neg]
      simp
    have hsign_ne : (-1 : ℝ) ^ (n + 1) ≠ 0 := by
      exact pow_ne_zero _ (by norm_num)
    have hdet_eq :
        (-1 : ℝ) ^ (n + 1) * (a * b ^ n) =
          (-1 : ℝ) ^ (n + 1) * (b • 1 + ((a - b) : ℝ) • V).det := by
      calc
        (-1 : ℝ) ^ (n + 1) * (a * b ^ n)
            = ((((a - b) : ℝ) • V).charpoly).eval (-b) := by
                simpa using heval.symm
        _ = (-1 : ℝ) ^ (n + 1) * (b • 1 + ((a - b) : ℝ) • V).det := by
              simpa using hmatrix
    have hdet_eq' :
        (a * b ^ n) * (-1 : ℝ) ^ (n + 1) =
          (b • 1 + ((a - b) : ℝ) • V).det * (-1 : ℝ) ^ (n + 1) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hdet_eq
    exact (mul_left_inj' hsign_ne).mp hdet_eq'.symm

/-- The determinant gain factor in John's one-point enlargement is strictly larger than `1` once
the offending inverse coordinate has norm `t > n`. -/
lemma one_point_det_gain_gt_one
    {n : ℕ}
    (hn : 0 < n)
    {t : ℝ}
    (ht : (n : ℝ) < t) :
    let a : ℝ := (t + 1) / (n + 1)
    let b : ℝ := Real.sqrt (((n - 1 : ℝ) * (t + 1)) / ((n + 1) * (t - 1)))
    1 < a * b ^ (n - 1) := by
  dsimp
  by_cases h1 : n = 1
  · subst h1
    have ht1 : (1 : ℝ) < t := by
      simpa using ht
    simp
    nlinarith
  · have hnat_one_lt : 1 < n := by
      omega
    have hn_real : (0 : ℝ) < n := by
      exact_mod_cast hn
    have hn_one_real : (1 : ℝ) < n := by
      exact_mod_cast hnat_one_lt
    let hfun : ℝ → ℝ :=
      fun s => (n + 1 : ℝ) * Real.log (s + 1) - (n - 1 : ℝ) * Real.log (s - 1)
    have hmono : StrictMonoOn hfun (Set.Ici (n : ℝ)) := by
      refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ ?_
      · intro x hx
        have hx_ge : (n : ℝ) ≤ x := by
          simpa using hx
        have hx_add : 0 < x + 1 := by
          linarith
        have hx_sub : 0 < x - 1 := by
          linarith
        exact (((continuousWithinAt_id.add continuousWithinAt_const).log hx_add.ne').const_mul _
          |>.sub (((continuousWithinAt_id.sub continuousWithinAt_const).log hx_sub.ne').const_mul _))
      · intro x hx
        have hx_gt : (n : ℝ) < x := by
          simpa using hx
        have hx_add : 0 < x + 1 := by
          linarith
        have hx_sub : 0 < x - 1 := by
          linarith
        have hderiv :
            deriv hfun x = (n + 1 : ℝ) / (x + 1) - (n - 1 : ℝ) / (x - 1) := by
          have hlog_add :
              deriv (fun s : ℝ => Real.log (s + 1)) x = 1 / (x + 1) := by
            simpa using
              (deriv.log (x := x) (f := fun s : ℝ => s + 1) (by fun_prop) hx_add.ne')
          have hlog_sub :
              deriv (fun s : ℝ => Real.log (s - 1)) x = 1 / (x - 1) := by
            simpa using
              (deriv.log (x := x) (f := fun s : ℝ => s - 1) (by fun_prop) hx_sub.ne')
          have hdiff_add :
              DifferentiableAt ℝ (fun s : ℝ => (n + 1 : ℝ) * Real.log (s + 1)) x := by
            exact ((differentiableAt_id.add_const 1).log hx_add.ne').const_mul _
          have hdiff_sub :
              DifferentiableAt ℝ (fun s : ℝ => (n - 1 : ℝ) * Real.log (s - 1)) x := by
            exact ((differentiableAt_id.sub_const 1).log hx_sub.ne').const_mul _
          calc
            deriv hfun x
                = deriv (fun s : ℝ => (n + 1 : ℝ) * Real.log (s + 1)
                    - (n - 1 : ℝ) * Real.log (s - 1)) x := by
                      rfl
            _ = deriv (fun s : ℝ => (n + 1 : ℝ) * Real.log (s + 1)) x -
                  deriv (fun s : ℝ => (n - 1 : ℝ) * Real.log (s - 1)) x := by
                    simpa using (deriv_sub hdiff_add hdiff_sub)
          rw [deriv_const_mul_field, deriv_const_mul_field, hlog_add, hlog_sub]
          ring
        rw [hderiv]
        have hfrac :
            (n + 1 : ℝ) / (x + 1) - (n - 1 : ℝ) / (x - 1) =
              (2 * (x - n)) / ((x + 1) * (x - 1)) := by
          field_simp [hx_add.ne', hx_sub.ne']
          ring
        rw [hfrac]
        have hnum : 0 < 2 * (x - n) := by
          linarith
        have hden : 0 < (x + 1) * (x - 1) := by
          positivity
        exact div_pos hnum hden
    have hlogdiff : 0 < hfun t - hfun n := by
      have hstrict := hmono (show (n : ℝ) ∈ Set.Ici (n : ℝ) by simp)
        (show t ∈ Set.Ici (n : ℝ) by exact le_of_lt ht) ht
      linarith
    let X : ℝ := ((n - 1 : ℝ) * (t + 1)) / ((n + 1) * (t - 1))
    let q : ℝ := ((t + 1) / (n + 1)) * (Real.sqrt X) ^ (n - 1)
    have hX_pos : 0 < X := by
      dsimp [X]
      have ht_add : 0 < t + 1 := by
        linarith [ht]
      have ht_sub : 0 < t - 1 := by
        linarith [hn_one_real, ht]
      have hn_add : 0 < (n : ℝ) + 1 := by
        positivity
      have hn_sub : 0 < (n : ℝ) - 1 := by
        linarith
      exact div_pos (mul_pos hn_sub ht_add) (mul_pos hn_add ht_sub)
    have hq_pos : 0 < q := by
      dsimp [q]
      have ht_add : 0 < t + 1 := by
        linarith [ht]
      have hn_add : 0 < (n : ℝ) + 1 := by
        positivity
      exact mul_pos (div_pos ht_add hn_add) (pow_pos (Real.sqrt_pos.2 hX_pos) _)
    have hlogq :
        2 * Real.log q = hfun t - hfun n := by
      have ht_add : 0 < t + 1 := by
        linarith [ht]
      have ht_sub : 0 < t - 1 := by
        linarith [hn_one_real, ht]
      have hn_add : 0 < (n : ℝ) + 1 := by
        positivity
      have hn_sub : 0 < (n : ℝ) - 1 := by
        linarith
      have hsqrt_pos : 0 < Real.sqrt X := Real.sqrt_pos.2 hX_pos
      calc
        2 * Real.log q
            = 2 * (Real.log ((t + 1) / (n + 1)) + Real.log ((Real.sqrt X) ^ (n - 1))) := by
                rw [show q = ((t + 1) / (n + 1)) * (Real.sqrt X) ^ (n - 1) by rfl,
                  Real.log_mul (show ((t + 1) / (n + 1)) ≠ 0 by positivity)
                    (pow_ne_zero _ hsqrt_pos.ne')]
        _ = 2 * Real.log ((t + 1) / (n + 1)) + 2 * ((n - 1 : ℝ) * Real.log (Real.sqrt X)) := by
              rw [← Real.rpow_natCast, Real.log_rpow hsqrt_pos]
              rw [Nat.cast_sub hnat_one_lt.le]
              ring
        _ = 2 * (Real.log (t + 1) - Real.log (n + 1)) + (n - 1 : ℝ) * Real.log X := by
              rw [Real.log_div (show t + 1 ≠ 0 by positivity) (show (n : ℝ) + 1 ≠ 0 by positivity),
                Real.log_sqrt hX_pos.le]
              ring_nf
        _ = hfun t - hfun n := by
              dsimp [hfun, X]
              rw [Real.log_div (show ((n - 1 : ℝ) * (t + 1)) ≠ 0 by positivity)
                  (show ((n + 1 : ℝ) * (t - 1)) ≠ 0 by positivity)]
              rw [Real.log_mul (show (n : ℝ) - 1 ≠ 0 by positivity)
                  (show t + 1 ≠ 0 by positivity)]
              rw [Real.log_mul (show (n : ℝ) + 1 ≠ 0 by positivity)
                  (show t - 1 ≠ 0 by positivity)]
              ring_nf
    have hq_log_pos : 0 < Real.log q := by
      nlinarith [hlogdiff]
    exact (Real.log_lt_log_iff one_pos hq_pos).mp (by simpa [Real.log_one] using hq_log_pos)

/- [BLOCK Exercise 8.14-(b) | 17 | defn]
Given a family F of ellipsoids, an ellipsoid E* ∈ F is a maximum-volume ellipsoid if vol(E*) ≥
vol(E) for all E ∈ F.
-/
def maximumVolumeEllipsoid
    {α : Type*}
    (vol : Set α → ℝ)
    (F : Set (Set α))
    (E_star : Set α) : Prop :=
  E_star ∈ F ∧ ∀ E ∈ F, vol E_star ≥ vol E

/- [BLOCK Exercise 8.14-(b) | 18 | thm]
Let C={x∈ ℝ^n| -1preceq Axpreceq 1}, where A∈ ℝ^{m× n}, 1∈ ℝ^m is the all-ones vector, and for u,v∈
ℝ^m, upreceq v means uᵢ≤ vᵢ for all i=1,dots,m, while uprec v means uᵢ<vᵢ for all i=1,dots,m. Assume
{x∈ ℝ^n| -1prec Axprec 1}ne emptyset. An ellipsoid ∈ ℝ^n means a set of the form E={c+Pu| ‖u‖_2≤ 1},
where c∈ ℝ^n and P∈ ℝ^{n×n} is invertible. If E⊆ C, we say that E is inscribed in C. For t>0, the
ellipsoid obtained by scaling E by the factor t about its center c is {c+tPu| ‖u‖_2≤ 1}. Show that
if E is a maximum-volume ellipsoid among all ellipsoids inscribed in C, then the ellipsoid obtained
by scaling E by the factor n about its center contains C.
-/
open scoped Matrix

set_option maxHeartbeats 10000000 in
theorem john_ellipsoid_scaling_contains_polytope
    {m n : ℕ}
    (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (c : EuclideanSpace ℝ (Fin n))
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : IsUnit P.det)
    (hnonempty :
      ∃ x : EuclideanSpace ℝ (Fin n),
        (∀ i : Fin m, (-1 : ℝ) < (A.mulVec x) i) ∧
        (∀ i : Fin m, (A.mulVec x) i < (1 : ℝ)))
    (hinscribed :
      inscribed (ellipsoid n c P hP)
        {x : EuclideanSpace ℝ (Fin n) |
          ∀ i : Fin m, (-1 : ℝ) ≤ (A.mulVec x) i ∧ (A.mulVec x) i ≤ (1 : ℝ)})
    (hmax :
      ∀ (c' : EuclideanSpace ℝ (Fin n)) (P' : Matrix (Fin n) (Fin n) ℝ)
        (hP' : IsUnit P'.det),
        inscribed (ellipsoid n c' P' hP')
          {x : EuclideanSpace ℝ (Fin n) |
            ∀ i : Fin m, (-1 : ℝ) ≤ (A.mulVec x) i ∧ (A.mulVec x) i ≤ (1 : ℝ)} →
        |P'.det| ≤ |P.det|) :
    {x : EuclideanSpace ℝ (Fin n) |
      ∀ i : Fin m, (-1 : ℝ) ≤ (A.mulVec x) i ∧ (A.mulVec x) i ≤ (1 : ℝ)} ⊆
      {x : EuclideanSpace ℝ (Fin n) |
        ∃ u : EuclideanSpace ℝ (Fin n),
          ‖u‖ ≤ 1 ∧ x = c + ((n : ℝ) • (P.mulVec u))} := by
  let C : Set (EuclideanSpace ℝ (Fin n)) := slabPolytope A
  have hC_convex : Convex ℝ C := by
    -- The ambient polytope is a convex body candidate for John's theorem.
    simpa [C] using slabPolytope_convex A
  have hC_interior : (interior C).Nonempty := by
    -- The strict-feasibility hypothesis gives the nonempty interior required by the theorem.
    simpa [C] using slabPolytope_interior_nonempty (A := A) hnonempty
  have hE_inscribed : inscribed (ellipsoid n c P hP) C := by
    -- This is exactly the given inscribed hypothesis after naming the slab polytope.
    simpa [C, slabPolytope] using hinscribed
  have hE_max :
      ∀ (c' : EuclideanSpace ℝ (Fin n)) (P' : Matrix (Fin n) (Fin n) ℝ)
        (hP' : IsUnit P'.det),
        inscribed (ellipsoid n c' P' hP') C →
        |P'.det| ≤ |P.det| := by
    intro c' P' hP' hinscribed'
    -- The determinant-maximality hypothesis is already stated for the same slab polytope.
    simpa [C] using hmax c' P' hP' hinscribed'
  have hE_rows :
      ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ 1 →
        ∀ i : Fin m,
          (-1 : ℝ) ≤ (A.mulVec c) i + ((A * P).mulVec u) i ∧
            (A.mulVec c) i + ((A * P).mulVec u) i ≤ (1 : ℝ) := by
    -- Rewrite the inscribed ellipsoid condition into row-wise slab bounds on the unit ball.
    exact (inscribed_ellipsoid_slab_rowwise_iff (A := A) (c := c) (P := P) (hP := hP)).1
      hE_inscribed
  sorry

end «problem-74»
