import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-59»
/-
Consider the optimization problem [ begin{} text{minimize} & x^T A x + 2 b^T x text{subject to} &
x^T x le 1, end{} ] with variable (x in mathbf{R}^n). Do not assume that (A succeq 0).
-/
structure QuadraticTrustRegionProblem (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  A_symm : A.IsSymm
  b : Fin n → ℝ

def QuadraticTrustRegionProblem.objective {n : ℕ} (p : QuadraticTrustRegionProblem n) :
    (Fin n → ℝ) → ℝ :=
  fun x => dotProduct x (p.A *ᵥ x) + 2 * dotProduct p.b x

def QuadraticTrustRegionProblem.feasibleSet {n : ℕ} (_p : QuadraticTrustRegionProblem n) :
    Set (Fin n → ℝ) :=
  {x | dotProduct x x ≤ 1}

def QuadraticTrustRegionProblem.isFeasible {n : ℕ} (_p : QuadraticTrustRegionProblem n)
    (x : Fin n → ℝ) : Prop :=
  dotProduct x x ≤ 1

/-- For a symmetric real matrix, the associated matrix bilinear form is symmetric. -/
lemma dotProduct_mulVec_eq_dotProduct_mulVec_transpose {n : ℕ} (p : QuadraticTrustRegionProblem n)
    (x y : Fin n → ℝ) : dotProduct x (p.A *ᵥ y) = dotProduct y (p.A *ᵥ x) := by
  -- Rewrite the left pairing through `vecMul`, then use the symmetry of `A`.
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, p.A_symm.eq, dotProduct_comm]

/-- Along an affine line through `x`, the objective is an explicit quadratic polynomial in `t`. -/
lemma objective_line_expansion {n : ℕ} (p : QuadraticTrustRegionProblem n) (x d : Fin n → ℝ)
    (t : ℝ) :
    p.objective (x + t • d) - p.objective x =
      t ^ 2 * dotProduct d (p.A *ᵥ d) + 2 * t * dotProduct d (p.A *ᵥ x + p.b) := by
  -- Expand every term, then collapse the mixed terms using symmetry of `A`.
  have hsym : dotProduct x (p.A *ᵥ d) = dotProduct d (p.A *ᵥ x) :=
    dotProduct_mulVec_eq_dotProduct_mulVec_transpose p x d
  rw [QuadraticTrustRegionProblem.objective, QuadraticTrustRegionProblem.objective,
    Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul, dotProduct_add]
  simp [hsym, dotProduct_comm, sub_eq_add_neg]
  ring

/-- The original objective coincides with the Euclidean-space quadratic-plus-linear expression. -/
lemma objective_eq_euclidean {n : ℕ} (p : QuadraticTrustRegionProblem n)
    (z : EuclideanSpace ℝ (Fin n)) :
    p.objective z.ofLp =
      ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) p.A).reApplyInnerSelf z +
        (2 • innerSL ℝ (WithLp.toLp 2 p.b)) z := by
  -- Translate both the quadratic and linear terms through `toEuclideanLin` and `toLp`.
  simp [QuadraticTrustRegionProblem.objective, ContinuousLinearMap.reApplyInnerSelf_apply,
    EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM, dotProduct_comm]

/-- The coordinate dot product of a real vector with itself is its Euclidean norm square. -/
lemma dotProduct_self_eq_norm_sq {n : ℕ} (x : Fin n → ℝ) :
    dotProduct x x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
  -- Rewrite the Euclidean norm square in coordinates and simplify absolute values over `ℝ`.
  simpa [dotProduct, sq] using
    (EuclideanSpace.norm_sq_eq (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))).symm

/-- The Euclidean reformulation of the objective has derivative `2 (T x + b)`. -/
lemma phi_hasStrictFDerivAt {n : ℕ}
    (xE bE : EuclideanSpace ℝ (Fin n))
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : φ = fun z => T.reApplyInnerSelf z + (2 • innerSL ℝ bE) z)
    (hT_symm :
      ((T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric) :
    HasStrictFDerivAt φ (2 • innerSL ℝ (T xE + bE)) xE := by
  -- Differentiate the quadratic part and the linear part separately, then combine them.
  subst hφ
  convert
    (hT_symm.hasStrictFDerivAt_reApplyInnerSelf xE).add ((2 • innerSL ℝ bE).hasStrictFDerivAt)
      using 1
  · ext z
    simp

/-
Let (n in mathbf{N}), let (A in mathbf{S}^n) be a real symmetric (n \times n) matrix, and let (b
in mathbf{R}^n). Let (I) denote the (n \times n) identity matrix, let (|x |_2 = (x^T x)^{1/2})
for (x in mathbf{R}^n), and for (M in mathbf{S}^n), let (M succeq 0) mean that (M) is positive
semidefinite. Consider the quadratic trust - region problem. Prove that if (x) is a global minimizer
of this problem, then there exists (lambda in mathbf{R}) such that (|x |_2 leq 1, lambda geq 0, A
+ lambda I succeq 0, (A + lambda I)x = - b, lambda bigl(1 - |x |_2^2 bigr) = 0.)
-/
set_option maxHeartbeats 4000000 in
theorem trust_region_global_minimizer_exists_kkt_multiplier
    {n : ℕ} (p : QuadraticTrustRegionProblem n) (x : Fin n → ℝ)
    (h_min :
      x ∈ p.feasibleSet ∧
        ∀ y : Fin n → ℝ, y ∈ p.feasibleSet → p.objective x ≤ p.objective y) :
    ∃ lam : ℝ,
      x ∈ p.feasibleSet ∧
      0 ≤ lam ∧
      (p.A + lam • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
      ((p.A + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x = (fun i => -p.b i)) ∧
      lam * (1 - dotProduct x x) = 0 := by
  let xE : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  let bE : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 p.b
  let T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) p.A
  let φ : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun z => T.reApplyInnerSelf z + (2 • innerSL ℝ bE) z
  have hφx : φ xE = p.objective x := by
    -- This identifies the original coordinates with the Euclidean-space objective.
    simpa [φ, xE, bE, T] using (objective_eq_euclidean p xE).symm
  have hT_symm : ((T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric := by
    -- Symmetry of `A` becomes symmetry of the corresponding Euclidean operator.
    simpa [T, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
      (Matrix.isHermitian_iff_isSymmetric (A := p.A)).mp (by simpa using p.A_symm)
  have hfeas : x ∈ p.feasibleSet := h_min.1
  have hmin_on : IsMinOn p.objective p.feasibleSet x := by
    -- Unpack the global-minimality hypothesis into `IsMinOn` form.
    simpa [isMinOn_iff] using h_min.2
  have hfeas_le : dotProduct x x ≤ 1 := hfeas
  rcases lt_or_eq_of_le hfeas_le with hlt | hEq
  · -- Route correction: instead of a monolithic interior proof, use line-derivative zero on the
    -- open ball to get stationarity, then a one-variable local-minimum argument for PSD.
    have hxE_norm_sq : ‖xE‖ ^ 2 < 1 := by
      rw [← dotProduct_self_eq_norm_sq x]
      exact hlt
    have hxE_mem_ball : xE ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      have hxE_nonneg : 0 ≤ ‖xE‖ := norm_nonneg xE
      nlinarith
    have hphi_min_closedBall :
        IsMinOn φ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) xE := by
      -- Global minimality transfers to the Euclidean closed unit ball.
      intro y hy
      have hy_norm_le : ‖y‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hy
      have hy_feas : y.ofLp ∈ p.feasibleSet := by
        have hy_sq : dotProduct y.ofLp y.ofLp ≤ 1 := by
          have hy_nonneg : 0 ≤ ‖y‖ := norm_nonneg y
          have hy_norm_sq_le : ‖y‖ ^ 2 ≤ 1 := by
            nlinarith
          simpa [sq] using (dotProduct_self_eq_norm_sq y.ofLp).trans_le hy_norm_sq_le
        simpa [QuadraticTrustRegionProblem.feasibleSet] using hy_sq
      have hy_obj : p.objective y.ofLp = φ y := by
        simpa [φ, bE, T] using (objective_eq_euclidean p y)
      have hx_obj : p.objective x = φ xE := hφx.symm
      simpa [hx_obj, hy_obj] using h_min.2 y.ofLp hy_feas
    have hclosedBall_nhds :
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ∈ 𝓝 xE := by
      have hball_nhds :
          Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ∈ 𝓝 xE :=
        Metric.isOpen_ball.mem_nhds hxE_mem_ball
      exact mem_of_superset hball_nhds Metric.ball_subset_closedBall
    have hphi_local : IsLocalMin φ xE := hphi_min_closedBall.isLocalMin hclosedBall_nhds
    have hphi_grad_zero :
        2 • innerSL ℝ (T xE + bE) = 0 := by
      -- The Euclidean reformulation has zero derivative at a strict-interior local minimum.
      exact hphi_local.hasFDerivAt_eq_zero (phi_hasStrictFDerivAt xE bE T φ rfl hT_symm).hasFDerivAt
    have hEuclid_station : T xE + bE = 0 := by
      -- Cancel the scalar factor `2`, then use injectivity of the Riesz map.
      have hdual_zero : innerSL ℝ (T xE + bE) = 0 := by
        apply smul_right_injective (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
          (two_ne_zero : (2 : ℝ) ≠ 0)
        simpa [two_smul, smul_add, add_smul] using hphi_grad_zero
      have hdual_zero' :
          (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin n))) (T xE + bE) =
            (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin n))) 0 := by
        simpa using hdual_zero
      exact (InnerProductSpace.toDualMap ℝ _).injective hdual_zero'
    have hgrad_zero : p.A *ᵥ x + p.b = 0 := by
      -- Transport interior stationarity back to coordinates.
      have hcoord_raw := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z.ofLp) hEuclid_station
      simpa [xE, bE, T, Matrix.ofLp_toEuclideanCLM] using hcoord_raw
    have hstationary : p.A *ᵥ x = (fun i => -p.b i) := by
      -- Rewrite the zero-gradient identity into the requested stationarity form.
      ext i
      have hi := congrArg (fun v => v i) hgrad_zero
      exact eq_neg_of_add_eq_zero_left hi
    have hpsd : p.A.PosSemidef := by
      -- Along each line through `xE`, a small local-minimum step leaves only the quadratic term.
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
      · exact (Matrix.isHermitian_iff_isSymmetric).2 hT_symm
      · intro d
        let dE : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 d
        have hline_local : IsLocalMin (φ ∘ fun t : ℝ => xE + t • dE) 0 := by
          -- Restrict the local minimum to the affine line in direction `d`.
          have hphi_local0 : IsLocalMin φ ((fun t : ℝ => xE + t • dE) 0) := by
            simpa [dE] using hphi_local
          refine hphi_local0.comp_continuous (g := fun t : ℝ => xE + t • dE) (b := 0) ?_
          fun_prop
        have hlineSet : {t : ℝ | φ xE ≤ φ (xE + t • dE)} ∈ 𝓝 (0 : ℝ) := by
          simpa [Function.comp, dE] using
            (show {t : ℝ | (φ ∘ fun u : ℝ => xE + u • dE) 0 ≤
                (φ ∘ fun u : ℝ => xE + u • dE) t} ∈ 𝓝 (0 : ℝ) from hline_local)
        rcases Metric.mem_nhds_iff.mp hlineSet with ⟨ε, hεpos, hεsub⟩
        let t : ℝ := ε / 2
        have ht_pos : 0 < t := by
          dsimp [t]
          positivity
        have ht_mem : t ∈ Metric.ball (0 : ℝ) ε := by
          dsimp [Metric.ball, t]
          simpa [Real.dist_eq, abs_of_nonneg hεpos.le, abs_of_nonneg ht_pos.le] using hεpos
        have hphi_le : φ xE ≤ φ (xE + t • dE) := hεsub ht_mem
        have hobj_nonneg :
            0 ≤ p.objective (x + t • d) - p.objective x := by
          -- Rewrite the Euclidean local-minimum inequality back to coordinates.
          have ht_arg : xE + t • dE = WithLp.toLp 2 (x + t • d) := by
            simp [xE, dE]
          have hphi_t : φ (xE + t • dE) = p.objective (x + t • d) := by
            rw [ht_arg]
            simpa [φ, bE, T] using
              (objective_eq_euclidean p (WithLp.toLp 2 (x + t • d))).symm
          have hobj_le : p.objective x ≤ p.objective (x + t • d) := by
            calc
              p.objective x = φ xE := hφx.symm
              _ ≤ φ (xE + t • dE) := hphi_le
              _ = p.objective (x + t • d) := hphi_t
          exact sub_nonneg.mpr hobj_le
        have hquad :
            p.objective (x + t • d) - p.objective x = t ^ 2 * dotProduct d (p.A *ᵥ d) := by
          -- Stationarity removes the linear term from the line expansion.
          rw [objective_line_expansion]
          have hlin : dotProduct d (p.A *ᵥ x + p.b) = 0 := by
            rw [hgrad_zero]
            simp
          simp [hlin]
        have ht_sq_pos : 0 < t ^ 2 := by
          nlinarith [sq_pos_of_ne_zero ht_pos.ne']
        have : 0 ≤ dotProduct d (p.A *ᵥ d) := by
          have hobj_nonneg' : 0 ≤ t ^ 2 * dotProduct d (p.A *ᵥ d) := by
            simpa [hquad] using hobj_nonneg
          nlinarith [hobj_nonneg', ht_sq_pos]
        simpa using this
    refine ⟨0, hfeas, le_rfl, ?_, ?_, ?_⟩
    · simpa using hpsd
    · simpa using hstationary
    · ring
  · -- Route correction: keep the boundary argument in Euclidean space until the multiplier
    -- equation is a clean vector identity, then transport once back to coordinates.
    have hxE_norm_sq : ‖xE‖ ^ 2 = 1 := by
      -- The boundary hypothesis says the Euclidean lift lies on the unit sphere.
      rw [← dotProduct_self_eq_norm_sq x]
      exact hEq
    have hconstraint_min :
        IsLocalMinOn φ {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ^ 2 = ‖xE‖ ^ 2} xE := by
      -- Restrict the global minimizer to the sphere cut out by the active norm constraint.
      have hsphere_min :
          IsMinOn φ {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ^ 2 = ‖xE‖ ^ 2} xE := by
        intro y hy
        have hy_feas : y.ofLp ∈ p.feasibleSet := by
          -- Equality of norm squares identifies the lifted point with a feasible boundary point.
          have hy_sq : dotProduct y.ofLp y.ofLp ≤ 1 := by
            calc
              dotProduct y.ofLp y.ofLp = ‖y‖ ^ 2 := by
                simpa using (dotProduct_self_eq_norm_sq y.ofLp)
              _ = ‖xE‖ ^ 2 := hy
              _ = 1 := hxE_norm_sq
              _ ≤ 1 := le_rfl
          simpa [QuadraticTrustRegionProblem.feasibleSet] using hy_sq
        have hy_obj : p.objective y.ofLp = φ y := by
          -- The Euclidean objective agrees with the coordinate objective at every point.
          simpa [φ, bE, T] using (objective_eq_euclidean p y)
        have hx_obj : p.objective x = φ xE := hφx.symm
        simpa [hx_obj, hy_obj] using h_min.2 y.ofLp hy_feas
      exact hsphere_min.localize
    have hconstraint_extr :
        IsLocalExtrOn φ {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ^ 2 = ‖xE‖ ^ 2} xE := by
      -- A local minimum on the active sphere is the local extremum input for Lagrange multipliers.
      exact Or.inl hconstraint_min
    obtain ⟨a, b, hab_ne, hab_eq⟩ :=
      IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d hconstraint_extr
        (hasStrictFDerivAt_norm_sq xE) (phi_hasStrictFDerivAt xE bE T φ rfl hT_symm)
    have hstationary_vec :
        a • xE + b • (T xE + bE) = 0 := by
      -- Convert the dual-valued Lagrange equation into an honest vector equation.
      have hdual :
          a • innerSL ℝ xE + b • innerSL ℝ (T xE + bE) = 0 := by
        apply smul_right_injective (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
          (two_ne_zero : (2 : ℝ) ≠ 0)
        simpa [two_smul, smul_add, add_smul, add_assoc] using hab_eq
      have hdual' :
          innerSL ℝ (a • xE + b • (T xE + bE)) = 0 := by
        ext z
        have hz :=
          congrArg (fun f : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => f z) hdual
        simpa [innerSL_apply_apply, real_inner_smul_left, add_comm, add_left_comm,
          add_assoc, smul_add] using hz
      have hdual'' :
          innerSL ℝ (a • xE + b • (T xE + bE)) =
            innerSL ℝ (0 : EuclideanSpace ℝ (Fin n)) := by
        simpa using hdual'
      exact innerSL_inj.mp hdual''
    have hxE_ne : xE ≠ 0 := by
      -- A unit vector cannot vanish.
      intro hxE_zero
      have : ‖xE‖ ^ 2 = 0 := by simp [hxE_zero]
      linarith [hxE_norm_sq]
    have hb_ne : b ≠ 0 := by
      -- The multiplier of the objective derivative cannot vanish, or else `xE = 0`.
      intro hb
      have ha_ne : a ≠ 0 := by simpa [hb] using hab_ne
      have hxE_zero : xE = 0 := by
        apply smul_right_injective (EuclideanSpace ℝ (Fin n)) ha_ne
        simpa [hb] using hstationary_vec
      exact hxE_ne hxE_zero
    let lam : ℝ := a / b
    have hEuclid_station : T xE + bE + lam • xE = 0 := by
      -- Divide the Lagrange equation by the nonzero scalar `b`.
      have hb_station :
          b • (T xE + bE + lam • xE) = 0 := by
        calc
          b • (T xE + bE + lam • xE)
              = b • (T xE + bE) + (b * lam) • xE := by
                  simp [smul_add, smul_smul, add_comm]
          _ = b • (T xE + bE) + a • xE := by
                  have hb_mul_lam : b * lam = a := by
                    dsimp [lam]
                    field_simp [hb_ne]
                  rw [hb_mul_lam]
          _ = 0 := by
                  simpa [add_comm, add_left_comm, add_assoc] using hstationary_vec
      rcases smul_eq_zero.mp hb_station with hb_zero | hzero
      · exact False.elim (hb_ne hb_zero)
      · exact hzero
    have hgrad_shift : p.A *ᵥ x + p.b + lam • x = 0 := by
      -- Transport the Euclidean stationarity equation back to coordinate vectors exactly once.
      have hcoord_raw := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z.ofLp) hEuclid_station
      simpa [xE, bE, T, lam, Matrix.ofLp_toEuclideanCLM] using hcoord_raw
    have hstationary_shifted :
        ((p.A + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x) + p.b = 0 := by
      -- Collect the `λ x` term into the shifted matrix action.
      simpa [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, add_assoc,
        add_left_comm, add_comm] using hgrad_shift
    have hstationary :
        ((p.A + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x = (fun i => -p.b i)) := by
      -- Rewrite the zero-sum stationarity equation into the requested coordinate form.
      ext i
      have hi := congrArg (fun v : Fin n → ℝ => v i) hstationary_shifted
      exact eq_neg_of_add_eq_zero_left hi
    have hlam_nonneg : 0 ≤ lam := by
      -- Moving radially inward stays feasible; a negative multiplier would decrease the objective.
      by_contra hlam_neg
      have hlam_lt : lam < 0 := lt_of_not_ge hlam_neg
      let alpha : ℝ := dotProduct x (p.A *ᵥ x)
      let t : ℝ := min 1 (-lam / (2 * (|alpha| + 1)))
      have ht_pos : 0 < t := by
        -- The chosen radial step is strictly positive because `lam < 0`.
        have hfrac_pos : 0 < -lam / (2 * (|alpha| + 1)) := by
          have hnum_pos : 0 < -lam := by linarith
          have hden_pos : 0 < 2 * (|alpha| + 1) := by positivity
          exact div_pos hnum_pos hden_pos
        exact lt_min one_pos hfrac_pos
      have ht_nonneg : 0 ≤ t := ht_pos.le
      have ht_le_one : t ≤ 1 := by
        exact min_le_left _ _
      have hradial_feas : (1 - t) • x ∈ p.feasibleSet := by
        -- Scaling a boundary point by a factor in `[0, 1]` keeps it in the unit ball.
        have hone_sub_nonneg : 0 ≤ 1 - t := by linarith
        have hone_sub_le_one : 1 - t ≤ 1 := by linarith
        have hsq_le : (1 - t) * (1 - t) ≤ 1 := by
          nlinarith
        have hfeas_scaled : dotProduct ((1 - t) • x) ((1 - t) • x) ≤ 1 := by
          simpa [hEq, dotProduct_smul, smul_dotProduct, mul_assoc] using hsq_le
        simpa [QuadraticTrustRegionProblem.feasibleSet] using hfeas_scaled
      have hobj_nonneg :
          0 ≤ p.objective ((1 - t) • x) - p.objective x := by
        -- Global minimality applies to the inward radial feasible point.
        exact sub_nonneg.mpr (h_min.2 ((1 - t) • x) hradial_feas)
      have hlin_negx : dotProduct (-x) (p.A *ᵥ x + p.b) = lam := by
        -- Dotting the stationarity equation with `-x` isolates the multiplier.
        have hdot := congrArg (fun v : Fin n → ℝ => dotProduct (-x) v) hgrad_shift
        have hdot' : -lam + dotProduct (-x) (p.A *ᵥ x + p.b) = 0 := by
          simpa [dotProduct_add, dotProduct_smul, dotProduct_comm, hEq, mul_comm, mul_left_comm,
            mul_assoc] using hdot
        linarith
      have hobj_line :
          p.objective ((1 - t) • x) - p.objective x =
            t ^ 2 * alpha + 2 * t * lam := by
        -- The explicit line expansion along direction `-x` reduces to a scalar quadratic.
        have hrewrite : x + t • (-x) = (1 - t) • x := by
          ext i
          simp [smul_eq_mul]
          ring
        calc
          p.objective ((1 - t) • x) - p.objective x
              = p.objective (x + t • (-x)) - p.objective x := by rw [hrewrite]
          _ = t ^ 2 * dotProduct (-x) (p.A *ᵥ (-x)) +
                2 * t * dotProduct (-x) (p.A *ᵥ x + p.b) := by
                simpa using (objective_line_expansion p x (-x) t)
          _ = t ^ 2 * alpha + 2 * t * lam := by
                simp [alpha, hlin_negx, Matrix.mulVec_neg, dotProduct_neg, dotProduct_comm]
      have ht_bound : t ≤ -lam / (2 * (|alpha| + 1)) := by
        exact min_le_right _ _
      have hobj_lt : t ^ 2 * alpha + 2 * t * lam < 0 := by
        -- The negative linear term dominates the quadratic remainder for this small step.
        have habs₁ : alpha ≤ |alpha| := le_abs_self alpha
        have habs₂ : -|alpha| ≤ alpha := neg_abs_le alpha
        have habs₃ : |alpha| ≤ |alpha| + 1 := by linarith
        have ht_scaled : 2 * t * (|alpha| + 1) ≤ -lam := by
          have hden_nonneg : 0 ≤ 2 * (|alpha| + 1) := by positivity
          have hmul := mul_le_mul_of_nonneg_right ht_bound hden_nonneg
          have hden_ne : 2 * (|alpha| + 1) ≠ 0 := by positivity
          have hmul' : t * (2 * (|alpha| + 1)) ≤ -lam := by
            simpa [hden_ne] using hmul
          nlinarith [hmul']
        have hquad_abs : t ^ 2 * alpha ≤ t ^ 2 * |alpha| := by
          nlinarith
        have hquad_bound : t ^ 2 * |alpha| ≤ -t * lam / 2 := by
          nlinarith [ht_scaled, ht_nonneg, habs₃]
        have hsum_le : t ^ 2 * alpha + 2 * t * lam ≤ 3 * t * lam / 2 := by
          nlinarith [hquad_abs, hquad_bound]
        have hlin_lt : 3 * t * lam / 2 < 0 := by
          nlinarith [ht_pos, hlam_lt]
        exact lt_of_le_of_lt hsum_le hlin_lt
      have : p.objective ((1 - t) • x) - p.objective x < 0 := by
        simpa [hobj_line] using hobj_lt
      exact (not_lt_of_ge hobj_nonneg) this
    let M : Matrix (Fin n) (Fin n) ℝ := p.A + lam • (1 : Matrix (Fin n) (Fin n) ℝ)
    let qform : (Fin n → ℝ) → ℝ := fun d => dotProduct d (M *ᵥ d)
    have hqform_eq :
        ∀ d : Fin n → ℝ, qform d = dotProduct d (p.A *ᵥ d) + lam * dotProduct d d := by
      intro d
      -- Expanding the shifted matrix action gives the scalar quadratic form formula.
      calc
        qform d = dotProduct d (M *ᵥ d) := rfl
        _ = dotProduct d (p.A *ᵥ d + lam • d) := by
              simp [M, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
        _ = dotProduct d (p.A *ᵥ d) + lam * dotProduct d d := by
              simp [dotProduct_add, dotProduct_smul]
    have hM_symm : M.IsSymm := by
      -- The shifted matrix remains symmetric.
      have hone_symm : (1 : Matrix (Fin n) (Fin n) ℝ).IsSymm := Matrix.isSymm_one
      dsimp [M]
      exact p.A_symm.add (hone_symm.smul lam)
    have hquad_nonorthogonal :
        ∀ d : Fin n → ℝ, dotProduct x d ≠ 0 → 0 ≤ qform d := by
      intro d hxd
      -- For a nonorthogonal direction, the exact sphere chord gives the quadratic form directly.
      have hd_ne : d ≠ 0 := by
        intro hd_zero
        exact hxd (by simp [hd_zero])
      have hdd_pos : 0 < dotProduct d d := by
        rw [dotProduct_self_eq_norm_sq d]
        have hdE_ne : (WithLp.toLp 2 d : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
          simpa using hd_ne
        have hd_norm_pos : 0 < ‖(WithLp.toLp 2 d : EuclideanSpace ℝ (Fin n))‖ := by
          exact norm_pos_iff.mpr hdE_ne
        nlinarith
      have hdd_ne : dotProduct d d ≠ 0 := ne_of_gt hdd_pos
      let t : ℝ := -2 * dotProduct x d / dotProduct d d
      have hy_eq :
          dotProduct (x + t • d) (x + t • d) = 1 := by
        -- This specific step length lands exactly back on the unit sphere.
        have ht_rel : 2 * t * dotProduct x d + t ^ 2 * dotProduct d d = 0 := by
          dsimp [t]
          field_simp [hdd_ne]
          ring
        calc
          dotProduct (x + t • d) (x + t • d)
              = dotProduct x x + 2 * t * dotProduct x d + t ^ 2 * dotProduct d d := by
                  simp [dotProduct_add, dotProduct_smul, dotProduct_comm, mul_comm,
                    mul_left_comm]
                  ring
          _ = 1 := by
              rw [hEq]
              linarith
      have hy_feas : x + t • d ∈ p.feasibleSet := by
        -- Points on the sphere are feasible for the trust-region problem.
        simp [QuadraticTrustRegionProblem.feasibleSet, hy_eq]
      have hobj_nonneg :
          0 ≤ p.objective (x + t • d) - p.objective x := by
        -- Global minimality applies to this exact boundary chord endpoint.
        exact sub_nonneg.mpr (h_min.2 (x + t • d) hy_feas)
      have hlin :
          dotProduct d (p.A *ᵥ x + p.b) = -lam * dotProduct x d := by
        -- Dotting stationarity with `d` turns the linear coefficient into the multiplier term.
        have hdot := congrArg (fun v : Fin n → ℝ => dotProduct d v) hgrad_shift
        have hdot' : dotProduct d (p.A *ᵥ x + p.b) + lam * dotProduct x d = 0 := by
          simpa [dotProduct_add, dotProduct_smul, dotProduct_comm, mul_comm, mul_left_comm,
            mul_assoc] using hdot
        linarith
      have ht_lam :
          -2 * t * lam * dotProduct x d = t ^ 2 * lam * dotProduct d d := by
        -- The same chord identity converts the linear term into the missing `λ‖d‖²` term.
        have ht_rel' : -2 * t * dotProduct x d = t ^ 2 * dotProduct d d := by
          dsimp [t]
          field_simp [hdd_ne]
        calc
          -2 * t * lam * dotProduct x d = lam * (-2 * t * dotProduct x d) := by ring
          _ = lam * (t ^ 2 * dotProduct d d) := by rw [ht_rel']
          _ = t ^ 2 * lam * dotProduct d d := by ring
      have hobj_eq :
          p.objective (x + t • d) - p.objective x = t ^ 2 * qform d := by
        -- The line expansion and the stationarity identity assemble into the shifted quadratic form.
        calc
          p.objective (x + t • d) - p.objective x
              = t ^ 2 * dotProduct d (p.A *ᵥ d) + 2 * t * dotProduct d (p.A *ᵥ x + p.b) := by
                  simpa using (objective_line_expansion p x d t)
          _ = t ^ 2 * dotProduct d (p.A *ᵥ d) - 2 * t * lam * dotProduct x d := by
                  rw [hlin]
                  ring
          _ = t ^ 2 * dotProduct d (p.A *ᵥ d) + (-2 * t * lam * dotProduct x d) := by
                  ring
          _ = t ^ 2 * dotProduct d (p.A *ᵥ d) + t ^ 2 * lam * dotProduct d d := by
                  rw [ht_lam]
          _ = t ^ 2 * (dotProduct d (p.A *ᵥ d) + lam * dotProduct d d) := by
                  ring
          _ = t ^ 2 * qform d := by
                  rw [hqform_eq]
      have ht_ne : t ≠ 0 := by
        -- Nonorthogonality of `d` makes the chord step nontrivial.
        dsimp [t]
        have hnum_ne : -2 * dotProduct x d ≠ 0 := by
          intro hzero
          have : dotProduct x d = 0 := by linarith
          exact hxd this
        exact div_ne_zero hnum_ne hdd_ne
      have hscaled_nonneg : 0 ≤ t ^ 2 * qform d := by
        rw [← hobj_eq]
        exact hobj_nonneg
      have hq_nonneg : 0 ≤ qform d := by
        -- A nonzero square factor cannot flip the sign of the quadratic form.
        by_contra hq_neg
        have hq_lt : qform d < 0 := lt_of_not_ge hq_neg
        have ht_sq_ne : t ^ 2 ≠ 0 := by
          exact pow_ne_zero 2 ht_ne
        have ht_sq_pos : 0 < t ^ 2 := lt_of_le_of_ne (sq_nonneg t) ht_sq_ne.symm
        have hscaled_neg : t ^ 2 * qform d < 0 := mul_neg_of_pos_of_neg ht_sq_pos hq_lt
        exact (not_lt_of_ge hscaled_nonneg) hscaled_neg
      exact hq_nonneg
    have hquad_orthogonal :
        ∀ d : Fin n → ℝ, dotProduct x d = 0 → 0 ≤ qform d := by
      intro d hxd
      -- Approximate an orthogonal direction by nearby nonorthogonal directions `d - ε x`.
      by_contra hneg
      let g : ℝ → ℝ := fun ε => qform (d - ε • x)
      have hg_cont : Continuous g := by
        -- The quadratic form is continuous, and so is the affine perturbation in `ε`.
        have hh : Continuous fun ε : ℝ => d - ε • x := by
          exact continuous_const.sub (continuous_id.smul continuous_const)
        have hg_eq :
            g = fun ε : ℝ =>
              dotProduct (d - ε • x) (p.A *ᵥ (d - ε • x)) +
                lam * dotProduct (d - ε • x) (d - ε • x) := by
          funext ε
          change qform (d - ε • x) = _ + _
          simpa using hqform_eq (d - ε • x)
        rw [hg_eq]
        exact (hh.dotProduct (continuous_const.matrix_mulVec hh)).add
          (continuous_const.mul (hh.dotProduct hh))
      have hg_neg_nhds : {ε : ℝ | g ε < 0} ∈ 𝓝 (0 : ℝ) := by
        -- Continuity propagates the negative value at `ε = 0` to a whole neighborhood.
        have hneg0 : g 0 < 0 := by simpa [g, qform] using hneg
        exact hg_cont.continuousAt.preimage_mem_nhds (Iio_mem_nhds hneg0)
      rcases Metric.mem_nhds_iff.mp hg_neg_nhds with ⟨δ, hδ_pos, hδ_sub⟩
      let ε : ℝ := δ / 2
      have hε_pos : 0 < ε := by
        dsimp [ε]
        positivity
      have hε_mem : ε ∈ Metric.ball (0 : ℝ) δ := by
        dsimp [Metric.ball, ε]
        simpa [Real.dist_eq, abs_of_nonneg hδ_pos.le, abs_of_nonneg hε_pos.le] using hδ_pos
      have hgε_neg : g ε < 0 := hδ_sub hε_mem
      have hxd_pert :
          dotProduct x (d - ε • x) ≠ 0 := by
        -- The perturbation shifts an orthogonal direction by exactly `-ε` in the radial component.
        have hxdeq : dotProduct x (d - ε • x) = -ε := by
          calc
            dotProduct x (d - ε • x) = dotProduct x d - ε * dotProduct x x := by
              rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
            _ = -ε := by
              rw [hxd, hEq]
              ring
        intro hzero
        have : ε = 0 := by
          rw [hxdeq] at hzero
          linarith
        exact hε_pos.ne' this
      have hgε_nonneg : 0 ≤ g ε := by
        -- The perturbed direction is nonorthogonal, so the exact chord argument applies to it.
        simpa [g] using hquad_nonorthogonal (d - ε • x) hxd_pert
      exact (not_lt_of_ge hgε_nonneg) hgε_neg
    have hpsd : M.PosSemidef := by
      -- The shifted matrix is PSD once every quadratic form value is nonnegative.
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
      · simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hM_symm
      · intro d
        by_cases hxd : dotProduct x d = 0
        · simpa [qform] using hquad_orthogonal d hxd
        · simpa [qform] using hquad_nonorthogonal d hxd
    refine ⟨lam, hfeas, hlam_nonneg, ?_, ?_, ?_⟩
    · simpa [M] using hpsd
    · simpa [M] using hstationary
    · simp [hEq]

end «problem-59»
