import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-40»
/-
Let n ∈ ℕ, and define ℝ_{+ +}^n = {x = (x₁, ..., xₙ)∈ ℝ^n: xₖ > 0, k = 1, ..., n}. Given the
function
f: ℝ_{+ +}^n o ℝ, f(x) = (prod_{k = 1}^n xₖ ight)^{1/n}. Prove that f is twice differentiable on
ℝ_{+ +}^n.
-/
theorem geometricMean_twiceDifferentiableOn_positiveOrthant (n : ℕ) (hn : 0 < n) :
    ContDiffOn ℝ 2
      (fun x : Fin n → ℝ => Real.rpow (∏ k, x k) (1 / (n : ℝ)))
      {x : Fin n → ℝ | ∀ k, 0 < x k} := by
  -- Route correction: rather than expanding derivatives of `Real.rpow` by hand, use the
  -- existing `ContDiffOn` API for finite products and nonvanishing real powers.
  have hprod :
      ContDiffOn ℝ 2 (fun x : Fin n → ℝ => ∏ k, x k) {x : Fin n → ℝ | ∀ k, 0 < x k} := by
    -- Each coordinate projection is smooth on every set, so their finite product is smooth too.
    simpa using
      (contDiffOn_prod (t := Finset.univ)
        (f := fun k : Fin n => fun x : Fin n → ℝ => x k)
        (fun k _ =>
          contDiffOn_apply (𝕜 := ℝ) (E := ℝ) k {x : Fin n → ℝ | ∀ j, 0 < x j}))
  have hne :
      ∀ x ∈ {x : Fin n → ℝ | ∀ k, 0 < x k}, (∏ k, x k) ≠ 0 := by
    intro x hx
    -- Positivity of every coordinate forces positivity, hence nonvanishing, of the product.
    have hpos : 0 < ∏ k, x k := Finset.prod_pos fun k _ => hx k
    exact hpos.ne'
  -- The geometric mean is the positive-orthant product raised to a constant real power.
  simpa using (hprod.rpow_const_of_ne (p := 1 / (n : ℝ)) hne)

/-- The coordinate directional derivative of the geometric mean on the positive orthant. -/
lemma geometricMean_firstPartial (n : ℕ) (x : Fin n → ℝ) (hx : ∀ k, 0 < x k) (i : Fin n) :
    (fderiv ℝ (fun z : Fin n → ℝ => Real.rpow (∏ k, z k) (1 / (n : ℝ))) x)
        (Pi.single i (1 : ℝ)) =
      (1 / (n : ℝ)) * Real.rpow (∏ k, x k) (1 / (n : ℝ)) / x i := by
  -- Route correction: compute the derivative of the product with the packaged finite-product rule,
  -- then simplify on the single-coordinate direction instead of expanding everything by hand.
  have hprod_pos : 0 < ∏ k, x k := Finset.prod_pos fun k _ => hx k
  have hgm :=
      (hasFDerivAt_finset_prod (𝕜 := ℝ) (u := Finset.univ) (x := x)).rpow_const
        (p := ((n : ℝ)⁻¹)) (Or.inl hprod_pos.ne') 
  have hfderiv :
      (fderiv ℝ (fun z : Fin n → ℝ => (∏ k, z k) ^ ((n : ℝ)⁻¹)) x) (Pi.single i (1 : ℝ)) =
        ((n : ℝ)⁻¹) * (∏ k, x k) ^ (((n : ℝ)⁻¹) - 1) * ∏ j ∈ Finset.univ.erase i, x j := by
    -- Evaluating the derivative on `Pi.single i 1` isolates the `i`-th product term.
    simpa [Pi.single_apply] using
      congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single i (1 : ℝ))) hgm.fderiv
  have hxi : x i ≠ 0 := (hx i).ne'
  have hsplit : ∏ k, x k = x i * ∏ j ∈ Finset.univ.erase i, x j := by
    -- Split the full product into the distinguished factor `x i` and the remaining product.
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Finset.mul_prod_erase (s := Finset.univ) (f := x) (by simp : i ∈ Finset.univ)).symm
  have hquot : ∏ j ∈ Finset.univ.erase i, x j = (∏ k, x k) / x i := by
    -- The erased product is exactly the full product divided by the missing coordinate.
    rw [hsplit]
    field_simp [hxi]
  have hpow :
      (∏ k, x k) ^ (((n : ℝ)⁻¹) - 1) * (∏ k, x k) = (∏ k, x k) ^ ((n : ℝ)⁻¹) := by
    -- Multiply by the positive product to shift the `rpow` exponent by one.
    simpa [Real.rpow_one] using
      (Real.rpow_add hprod_pos (((n : ℝ)⁻¹) - 1) 1).symm
  have hmain :
      (fderiv ℝ (fun z : Fin n → ℝ => (∏ k, z k) ^ ((n : ℝ)⁻¹)) x) (Pi.single i (1 : ℝ)) =
        ((n : ℝ)⁻¹) * (∏ k, x k) ^ ((n : ℝ)⁻¹) / x i := by
    calc
      (fderiv ℝ (fun z : Fin n → ℝ => (∏ k, z k) ^ ((n : ℝ)⁻¹)) x) (Pi.single i (1 : ℝ)) =
          ((n : ℝ)⁻¹) * ((∏ k, x k) ^ (((n : ℝ)⁻¹) - 1) * ((∏ k, x k) / x i)) := by
            rw [hfderiv, hquot]
            ring
      _ = ((n : ℝ)⁻¹) * (((∏ k, x k) ^ (((n : ℝ)⁻¹) - 1) * (∏ k, x k)) / x i) := by
            field_simp [hxi]
      _ = ((n : ℝ)⁻¹) * ((∏ k, x k) ^ ((n : ℝ)⁻¹) / x i) := by rw [hpow]
      _ = ((n : ℝ)⁻¹) * (∏ k, x k) ^ ((n : ℝ)⁻¹) / x i := by ring
  simpa [one_div] using hmain

/-- The entries of the negative Hessian of the geometric mean on the positive orthant. -/
lemma geometricMean_negativeHessianEntry
    (n : ℕ) (x : Fin n → ℝ) (hx : ∀ k, 0 < x k) (i j : Fin n) :
    -(fderiv ℝ
        (fun y : Fin n → ℝ =>
          (fderiv ℝ (fun z : Fin n → ℝ => Real.rpow (∏ k, z k) (1 / (n : ℝ))) y)
            (Pi.single j (1 : ℝ))) x)
        (Pi.single i (1 : ℝ)) =
      (1 / (n : ℝ)) * Real.rpow (∏ k, x k) (1 / (n : ℝ)) *
        (if i = j then (1 - 1 / (n : ℝ)) / (x i)^2 else -(1 / (n : ℝ)) / (x i * x j)) := by
  let gm : (Fin n → ℝ) → ℝ := fun z => Real.rpow (∏ k, z k) (1 / (n : ℝ))
  let a : ℝ := (n : ℝ)⁻¹
  have hfirst :
      ∀ y : Fin n → ℝ, (∀ k, 0 < y k) →
        (fderiv ℝ gm y) (Pi.single j (1 : ℝ)) = a * gm y / y j := by
    intro y hy
    -- Reuse the first-partial identity at nearby positive points.
    simpa [gm, a, one_div] using geometricMean_firstPartial n y hy j
  have hopen : IsOpen {y : Fin n → ℝ | ∀ k, 0 < y k} := by
    -- The positive orthant is open because each coordinate positivity condition is open.
    simpa [Set.setOf_forall] using
      (isOpen_biInter_finset (s := (Finset.univ : Finset (Fin n)))
        (f := fun k => {y : Fin n → ℝ | 0 < y k})
        (fun k hk => isOpen_lt continuous_const (continuous_apply k)))
  have heq :
      (fun y : Fin n → ℝ => (fderiv ℝ gm y) (Pi.single j (1 : ℝ))) =ᶠ[nhds x]
        (fun y : Fin n → ℝ => a * gm y * (y j)⁻¹) := by
    -- Route correction: replace the nested derivative by its explicit first-partial formula only
    -- on a neighborhood where all coordinates stay positive.
    filter_upwards [hopen.mem_nhds hx] with y hy
    simpa [div_eq_mul_inv] using hfirst y hy
  have htarget :
      (fderiv ℝ (fun y : Fin n → ℝ => (fderiv ℝ gm y) (Pi.single j (1 : ℝ))) x)
          (Pi.single i (1 : ℝ)) =
        (fderiv ℝ (fun y : Fin n → ℝ => a * gm y * (y j)⁻¹) x) (Pi.single i (1 : ℝ)) := by
    -- Convert the eventual equality above into equality of derivatives at `x`.
    exact congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single i (1 : ℝ))) heq.fderiv_eq
  have hprod_pos : 0 < ∏ k, x k := Finset.prod_pos fun k _ => hx k
  have hgm_fd :=
      (hasFDerivAt_finset_prod (𝕜 := ℝ) (u := Finset.univ) (x := x)).rpow_const
        (p := a) (Or.inl hprod_pos.ne')
  have hgm_fderiv : HasFDerivAt gm (fderiv ℝ gm x) x := by
    -- Rewrite the explicit derivative into the canonical `fderiv` form for later product rules.
    have hfd_eq :
        fderiv ℝ gm x =
          ((a * (∏ k, x k) ^ (a - 1)) •
            ∑ i, (∏ j ∈ Finset.univ.erase i, x j) •
              (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)) := by
      simpa [gm, a, one_div] using hgm_fd.fderiv
    rw [hfd_eq]
    simpa [gm, a, one_div] using hgm_fd
  have hscaled := hgm_fderiv.const_mul a
  have hrecip :
      HasFDerivAt (fun y : Fin n → ℝ => (y j)⁻¹)
        (((-1 / (x j)^2 : ℝ)) •
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j)) x := by
    -- Differentiate the reciprocal coordinate factor by a scalar derivative composed with projection.
    simpa using
      ((HasDerivAt.inv (hasDerivAt_id (x := x j)) (hx j).ne').comp_hasFDerivAt x
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).hasFDerivAt))
  have hexp := hscaled.mul hrecip
  have hexp_eval :
      (fderiv ℝ (fun y : Fin n → ℝ => a * gm y * (y j)⁻¹) x) (Pi.single i (1 : ℝ)) =
        (if j = i then a * gm x * (-1 / (x j)^2) else 0) +
          (x j)⁻¹ * (a * (fderiv ℝ gm x) (Pi.single i (1 : ℝ))) := by
    -- Evaluate the product-rule derivative on the coordinate direction `Pi.single i 1`.
    simpa [Pi.single_apply] using
      congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single i (1 : ℝ))) hexp.fderiv
  have hfirst_i : (fderiv ℝ gm x) (Pi.single i (1 : ℝ)) = a * gm x / x i := by
    -- The remaining `gm` derivative is exactly the first-partial formula in the `i` direction.
    exact geometricMean_firstPartial n x hx i |>.trans (by simp [gm, a, one_div])
  have hneg_target :
      -(fderiv ℝ (fun y : Fin n → ℝ => (fderiv ℝ gm y) (Pi.single j (1 : ℝ))) x)
          (Pi.single i (1 : ℝ)) =
        -(fderiv ℝ (fun y : Fin n → ℝ => a * gm y * (y j)⁻¹) x) (Pi.single i (1 : ℝ)) := by
    -- Negating preserves the equality between the nested derivative and the explicit quotient route.
    simpa using congrArg Neg.neg htarget
  rw [hneg_target]
  by_cases hij : i = j
  · subst hij
    -- On the diagonal, the reciprocal derivative contributes the extra `(1 - a)` factor.
    have hgoal :
        -(fderiv ℝ (fun y : Fin n → ℝ => a * gm y * (y i)⁻¹) x) (Pi.single i (1 : ℝ)) =
          (1 / (n : ℝ)) * Real.rpow (∏ k, x k) (1 / (n : ℝ)) *
            ((1 - 1 / (n : ℝ)) / (x i)^2) := by
      have hderiv := congrArg Neg.neg hexp_eval
      rw [hfirst_i] at hderiv
      simp [gm, a, one_div] at hderiv
      field_simp [(hx i).ne'] at hderiv ⊢
      have hn_ne : (n : ℝ) ≠ 0 := by
        exact_mod_cast (Fin.pos_iff_nonempty.mpr ⟨i⟩).ne'
      field_simp [hn_ne] at hderiv ⊢
      ring_nf at hderiv ⊢
      simpa [mul_assoc, mul_comm, gm, a, one_div] using hderiv
    simpa using hgoal
  · -- Off the diagonal, only the product-rule term with `∂ᵢ gm` survives.
    have hgoal :
        -(fderiv ℝ (fun y : Fin n → ℝ => a * gm y * (y j)⁻¹) x) (Pi.single i (1 : ℝ)) =
          (1 / (n : ℝ)) * Real.rpow (∏ k, x k) (1 / (n : ℝ)) *
            (-(1 / (n : ℝ)) / (x i * x j)) := by
      have hji : j ≠ i := by simpa [eq_comm] using hij
      have hderiv := congrArg Neg.neg hexp_eval
      rw [hfirst_i] at hderiv
      simp [hij, gm, a, one_div] at hderiv
      field_simp [(hx i).ne', (hx j).ne'] at hderiv ⊢
      have hn_ne : (n : ℝ) ≠ 0 := by
        exact_mod_cast (Fin.pos_iff_nonempty.mpr ⟨i⟩).ne'
      field_simp [hn_ne] at hderiv ⊢
      ring_nf at hderiv ⊢
      have hderiv' := congrArg Neg.neg hderiv
      simp [hji] at hderiv'
      simpa [mul_comm, mul_left_comm, mul_assoc, gm, a, one_div] using hderiv'
    simpa [hij] using hgoal

/-
Let n ∈ ℕ, and define ℝ_{+ +}^n = {x = (x₁, ..., xₙ)∈ ℝ^n: xₖ > 0, k = 1, ..., n}. Given the
function
f: ℝ_{+ +}^n o ℝ, f(x) = (prod_{k = 1}^n xₖ ight)^{1/n}. Prove that for any x ∈ ℝ_{+ +}^n, the
Hessian
matrix abla^2 f(x) is negative semidefinite.
-/
theorem geometricMean_hessian_nonpos (n : ℕ) (hn : 0 < n) :
    ∀ x : Fin n → ℝ,
      (∀ k, 0 < x k) →
      Matrix.PosSemidef
        (-fun i j =>
          (fderiv ℝ
            (fun y : Fin n → ℝ =>
              (fderiv ℝ
                (fun z : Fin n → ℝ => Real.rpow (∏ k, z k) (1 / (n : ℝ))) y)
                (Pi.single j (1 : ℝ))) x)
            (Pi.single i (1 : ℝ))) := by
  intro x hx
  let a : ℝ := (n : ℝ)⁻¹
  let gmx : ℝ := Real.rpow (∏ k, x k) (1 / (n : ℝ))
  let s : Fin n → ℝ := fun i => (x i)⁻¹
  let M : Matrix (Fin n) (Fin n) ℝ :=
    (a * gmx) •
      (Matrix.diagonal (fun i => (s i)^2) - a • Matrix.vecMulVec s s)
  have hM :
      (-fun i j =>
          (fderiv ℝ
            (fun y : Fin n → ℝ =>
              (fderiv ℝ
                (fun z : Fin n → ℝ => Real.rpow (∏ k, z k) (1 / (n : ℝ))) y)
                (Pi.single j (1 : ℝ))) x)
            (Pi.single i (1 : ℝ))) = M := by
    -- The explicit second-partial formula matches a diagonal minus rank-one matrix.
    ext i j
    by_cases hij : i = j
    · subst hij
      have hentry := geometricMean_negativeHessianEntry n x hx i i
      simp [M, a, gmx, s, one_div, div_eq_mul_inv, Matrix.vecMulVec_apply] at hentry ⊢
      ring_nf at hentry ⊢
      exact hentry
    · have hji : j ≠ i := by simpa [eq_comm] using hij
      have hentry := geometricMean_negativeHessianEntry n x hx i j
      simp [M, a, gmx, s, hij, hji, one_div, div_eq_mul_inv, Matrix.vecMulVec_apply] at hentry ⊢
      ring_nf at hentry ⊢
      exact hentry
  rw [hM]
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · -- The explicit matrix is symmetric, hence Hermitian over `ℝ`.
    refine Matrix.IsHermitian.ext ?_
    intro i j
    by_cases hij : i = j
    · subst hij
      simp [M, a, gmx, s, Matrix.diagonal, Matrix.vecMulVec]
    · have hji : j ≠ i := by simpa [eq_comm] using hij
      simp [M, a, gmx, s, Matrix.diagonal, Matrix.vecMulVec, hij, hji, mul_comm, mul_left_comm,
        mul_assoc]
  · intro v
    have ha_pos : 0 < a := by
      -- The scalar factor `a = 1 / n` is positive because `n > 0`.
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      dsimp [a]
      positivity
    have hgmx_pos : 0 < gmx := by
      -- The geometric mean itself stays positive on the positive orthant.
      dsimp [gmx]
      exact Real.rpow_pos_of_pos (Finset.prod_pos fun k _ => hx k) _
    have hdiag :
        dotProduct v ((Matrix.diagonal (fun i => (s i)^2) : Matrix (Fin n) (Fin n) ℝ).mulVec v) =
          ∑ i : Fin n, (v i * s i)^2 := by
      -- The diagonal part contributes the sum of coordinate squares.
      simp [Matrix.mulVec, dotProduct, Matrix.diagonal, s, pow_two, mul_comm, mul_left_comm,
        mul_assoc]
    have hrank :
        dotProduct v ((Matrix.vecMulVec s s : Matrix (Fin n) (Fin n) ℝ).mulVec v) =
          (dotProduct s v)^2 := by
      -- The rank-one term collapses to the square of a single dot product.
      rw [Matrix.vecMulVec_mulVec]
      rw [dotProduct_smul]
      rw [dotProduct_comm s v]
      simp [pow_two]
    have hbase :
        dotProduct v
            ((Matrix.diagonal (fun i => (s i)^2) - a • Matrix.vecMulVec s s).mulVec v) =
          (∑ i : Fin n, (v i * s i)^2) - a * (dotProduct s v)^2 := by
      -- Rewrite the quadratic form into a diagonal term minus the rank-one correction.
      simpa [smul_eq_mul] using
        (by
          rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, hdiag, hrank] :
            dotProduct v
                ((Matrix.diagonal (fun i => (s i)^2) - a • Matrix.vecMulVec s s).mulVec v) =
              (∑ i : Fin n, (v i * s i)^2) - a • (dotProduct s v)^2)
    have hcs :
        (dotProduct s v)^2 ≤ (n : ℝ) * ∑ i : Fin n, (v i * s i)^2 := by
      -- Cauchy-Schwarz on the vector with coordinates `v i / x i`.
      simpa [dotProduct, Finset.card_univ, Fintype.card_fin, s, mul_comm, mul_left_comm,
        mul_assoc] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin n => v i * s i))
    have hinner :
        0 ≤ (∑ i : Fin n, (v i * s i)^2) - a * (dotProduct s v)^2 := by
      -- Since `a = 1 / n`, the Cauchy-Schwarz bound is exactly the needed nonnegativity.
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      have hbound :
          ((n : ℝ)⁻¹) * (dotProduct s v)^2 ≤ ∑ i : Fin n, (v i * s i)^2 := by
        have hmul :=
            mul_le_mul_of_nonneg_left hcs (show 0 ≤ (n : ℝ)⁻¹ by positivity)
        have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
        simpa [mul_assoc, hn_ne] using hmul
      dsimp [a]
      nlinarith
    calc
      0 ≤ a * gmx * ((∑ i : Fin n, (v i * s i)^2) - a * (dotProduct s v)^2) := by
            exact mul_nonneg (le_of_lt (mul_pos ha_pos hgmx_pos)) hinner
      _ = dotProduct v (M.mulVec v) := by
            -- Restore the matrix quadratic form from the scalar decomposition above.
            rw [show dotProduct v (M.mulVec v) =
                (a * gmx) *
                  dotProduct v
                    ((Matrix.diagonal (fun i => (s i)^2) - a • Matrix.vecMulVec s s).mulVec v) by
                  dsimp [M]
                  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]]
            rw [hbase]

/-
Let n ∈ ℕ, and define ℝ_{+ +}^n = {x = (x₁, ..., xₙ)∈ ℝ^n: xₖ > 0, k = 1, ..., n}. Given the
function
f: ℝ_{+ +}^n o ℝ, f(x) = (prod_{k = 1}^n xₖ ight)^{1/n}. Prove that f is a concave function on
ℝ_{+ +}^n.
-/
theorem geometricMean_concaveOn_positiveOrthant (n : ℕ) (hn : 0 < n) :
    ConcaveOn ℝ {x : Fin n → ℝ | ∀ k, 0 < x k}
      (fun x : Fin n → ℝ => Real.rpow (∏ k, x k) (1 / (n : ℝ))) := by
  refine ⟨?_, ?_⟩
  · -- The positive orthant is convex because a convex combination with one positive weight
    -- preserves strict positivity coordinatewise.
    intro x hx y hy a b ha hb hab k
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simp [Pi.add_apply, ha0, hb1, hy k]
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
      have hax_pos : 0 < a * x k := mul_pos ha_pos (hx k)
      have hby_nonneg : 0 ≤ b * y k := mul_nonneg hb (hy k).le
      simpa [Pi.smul_apply, Pi.add_apply] using add_pos_of_pos_of_nonneg hax_pos hby_nonneg
  · intro x hx y hy a b ha hb hab
    let gx : ℝ := Real.rpow (∏ k, x k) (1 / (n : ℝ))
    let gy : ℝ := Real.rpow (∏ k, y k) (1 / (n : ℝ))
    let s : ℝ := a * gx + b * gy
    have hprodx_pos : 0 < ∏ k, x k := Finset.prod_pos fun k _ => hx k
    have hprody_pos : 0 < ∏ k, y k := Finset.prod_pos fun k _ => hy k
    have hgx_pos : 0 < gx := by
      -- Each geometric mean is positive because every coordinate is positive.
      dsimp [gx]
      exact Real.rpow_pos_of_pos hprodx_pos _
    have hgy_pos : 0 < gy := by
      -- The same positivity holds for the second endpoint.
      dsimp [gy]
      exact Real.rpow_pos_of_pos hprody_pos _
    have hs_pos : 0 < s := by
      -- The weighted sum `s = a * gx + b * gy` is positive because the weights are nonnegative
      -- and add up to one.
      dsimp [s]
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        rw [ha0, hb1]
        simpa using hgy_pos
      · have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
        have hax_pos : 0 < a * gx := mul_pos ha_pos hgx_pos
        have hby_nonneg : 0 ≤ b * gy := mul_nonneg hb hgy_pos.le
        exact add_pos_of_pos_of_nonneg hax_pos hby_nonneg
    have hnR_ne : (n : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hn)
    have hxn : ∀ k, 0 ≤ x k := fun k => (hx k).le
    have hyn : ∀ k, 0 ≤ y k := fun k => (hy k).le
    have hgx_natpow : gx ^ n = ∏ k, x k := by
      -- Raising `gx` back to the `n`th power recovers the original product.
      dsimp [gx]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hprodx_pos.le]
      field_simp [hnR_ne]
      rw [Real.rpow_one]
    have hgy_natpow : gy ^ n = ∏ k, y k := by
      -- The same normalization identity holds for `gy`.
      dsimp [gy]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hprody_pos.le]
      field_simp [hnR_ne]
      rw [Real.rpow_one]
    have hnormx_prod : ∏ k, x k / gx = 1 := by
      -- After dividing each coordinate by its geometric mean, the normalized coordinates
      -- multiply to one.
      rw [Finset.prod_div_distrib]
      rw [show (∏ _k : Fin n, gx) = gx ^ n by simp]
      rw [hgx_natpow]
      exact div_self hprodx_pos.ne'
    have hnormy_prod : ∏ k, y k / gy = 1 := by
      -- The second normalized vector also has product one.
      rw [Finset.prod_div_distrib]
      rw [show (∏ _k : Fin n, gy) = gy ^ n by simp]
      rw [hgy_natpow]
      exact div_self hprody_pos.ne'
    have hcoord (k : Fin n) :
        s * ((x k / gx) ^ (a * gx / s) * (y k / gy) ^ (b * gy / s)) ≤ a * x k + b * y k := by
      -- Apply weighted AM-GM to the normalized coordinates with weights proportional to
      -- `a * gx` and `b * gy`, then rescale by `s`.
      have hweights : a * gx / s + b * gy / s = 1 := by
        calc
          a * gx / s + b * gy / s = (a * gx + b * gy) / s := by ring_nf
          _ = s / s := by rfl
          _ = 1 := div_self hs_pos.ne'
      have hx_div_nonneg : 0 ≤ x k / gx := div_nonneg (hxn k) hgx_pos.le
      have hy_div_nonneg : 0 ≤ y k / gy := div_nonneg (hyn k) hgy_pos.le
      have hax_div_nonneg : 0 ≤ a * gx / s := div_nonneg (mul_nonneg ha hgx_pos.le) hs_pos.le
      have hby_div_nonneg : 0 ≤ b * gy / s := div_nonneg (mul_nonneg hb hgy_pos.le) hs_pos.le
      have hamgm := Real.geom_mean_le_arith_mean2_weighted
          hax_div_nonneg hby_div_nonneg hx_div_nonneg hy_div_nonneg hweights
      have hm := mul_le_mul_of_nonneg_left hamgm hs_pos.le
      field_simp [hs_pos.ne', hgx_pos.ne', hgy_pos.ne'] at hm ⊢
      ring_nf at hm ⊢
      exact hm
    have hprod_coord :
        ∏ k, s * ((x k / gx) ^ (a * gx / s) * (y k / gy) ^ (b * gy / s)) ≤
          ∏ k, (a * x k + b * y k) := by
      -- Multiplying the coordinatewise inequalities keeps the inequality direction because
      -- all factors on the left are nonnegative.
      apply Finset.prod_le_prod
      · intro k _
        exact mul_nonneg hs_pos.le <|
          mul_nonneg (Real.rpow_nonneg (div_nonneg (hxn k) hgx_pos.le) _)
            (Real.rpow_nonneg (div_nonneg (hyn k) hgy_pos.le) _)
      · intro k _
        exact hcoord k
    have hnormalized :
        ∏ k, ((x k / gx) ^ (a * gx / s) * (y k / gy) ^ (b * gy / s)) = 1 := by
      -- The normalized factors collapse because the normalized products of `x` and `y`
      -- are both equal to one.
      rw [Finset.prod_mul_distrib]
      rw [Real.finset_prod_rpow Finset.univ (fun k : Fin n => x k / gx)
          (fun k _ => div_nonneg (hxn k) hgx_pos.le) (a * gx / s)]
      rw [Real.finset_prod_rpow Finset.univ (fun k : Fin n => y k / gy)
          (fun k _ => div_nonneg (hyn k) hgy_pos.le) (b * gy / s)]
      rw [hnormx_prod, hnormy_prod]
      simp
    have hleft :
        ∏ k, s * ((x k / gx) ^ (a * gx / s) * (y k / gy) ^ (b * gy / s)) = s ^ n := by
      -- The left-hand product is just `s^n` because the normalized product equals one.
      rw [Finset.prod_mul_distrib]
      rw [show (∏ _k : Fin n, s) = s ^ n by simp]
      rw [hnormalized]
      simp
    have hs_natpow_le : s ^ n ≤ ∏ k, (a * x k + b * y k) := by
      -- Repackage the multiplied coordinatewise estimate as a bound on `s^n`.
      rw [← hleft]
      exact hprod_coord
    have hs_rpow_le : s ^ (n : ℝ) ≤ ∏ k, (a * x k + b * y k) := by
      -- Rewrite the natural power as a real power to prepare for taking the `n`th root.
      simpa [Real.rpow_natCast] using hs_natpow_le
    have hroot := Real.rpow_le_rpow (show 0 ≤ s ^ (n : ℝ) by positivity)
      hs_rpow_le (show 0 ≤ 1 / (n : ℝ) by positivity)
    -- Taking the `n`th root of the product inequality gives the desired concavity estimate.
    calc
      a * Real.rpow (∏ k, x k) (1 / (n : ℝ)) + b * Real.rpow (∏ k, y k) (1 / (n : ℝ)) = s := by
        rfl
      _ = (s ^ (n : ℝ)) ^ (1 / (n : ℝ)) := by
        symm
        rw [← Real.rpow_mul hs_pos.le]
        field_simp [hnR_ne]
        rw [Real.rpow_one]
      _ ≤ Real.rpow (∏ k, (a * x k + b * y k)) (1 / (n : ℝ)) := hroot
      _ = Real.rpow (∏ k, (a • x + b • y) k) (1 / (n : ℝ)) := by
        simp [Pi.smul_apply, Pi.add_apply]

end «problem-40»
