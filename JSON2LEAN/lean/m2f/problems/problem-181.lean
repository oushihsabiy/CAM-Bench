import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-181»

def l2Norm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, (x i) ^ 2)

/-
Let A ∈ 𝕊_ {+ +}^n, b ∈ ℝ^n, and Δ > 0, where 𝕊_ + + ^n denotes the set of all n × n real symmetric
positive definite matrices. Consider the quadratic optimization problem

min_(x ∈ ℝ^n) x^T A x + 2 b^T x s. t. ‖x‖_2 ≤ Δ.
-/
structure QuadraticBallConstrainedProblem (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  b : Fin n → ℝ
  Δ : ℝ
  symm : A.IsSymm
  posDef : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < dotProduct x (A.mulVec x)
  delta_pos : 0 < Δ

def QuadraticBallConstrainedProblem.feasible {n : ℕ}
    (p : QuadraticBallConstrainedProblem n) (x : Fin n → ℝ) : Prop :=
  l2Norm x ≤ p.Δ

def QuadraticBallConstrainedProblem.objective {n : ℕ}
    (p : QuadraticBallConstrainedProblem n) (x : Fin n → ℝ) : ℝ :=
  dotProduct x (p.A.mulVec x) + 2 * dotProduct p.b x

/-- The matrix in a quadratic ball-constrained problem is positive definite. -/
lemma quadratic_problem_matrix_posDef {n : ℕ} (p : QuadraticBallConstrainedProblem n) :
    p.A.PosDef := by
  -- The structure hypotheses are exactly the real positive-definite matrix criterion.
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · simpa using p.symm
  · intro x hx
    simpa using p.posDef x hx

/-- The unconstrained candidate satisfies the stationarity equation `A x₀ = -b`. -/
lemma unconstrained_candidate_mulVec_eq_neg_b
    {n : ℕ} (p : QuadraticBallConstrainedProblem n) {x₀ : Fin n → ℝ}
    (hx₀ : x₀ = -(p.A⁻¹.mulVec p.b)) :
    p.A.mulVec x₀ = -p.b := by
  letI : Invertible p.A := (quadratic_problem_matrix_posDef p).isUnit.invertible
  -- Rewrite `x₀` and cancel the inverse by multiplying on the left by `A`.
  rw [hx₀, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible,
    Matrix.one_mulVec]

/-- Translating the objective by a stationary point leaves only a quadratic error term. -/
lemma objective_translate_eq_objective_at_candidate_add_quadratic
    {n : ℕ} (p : QuadraticBallConstrainedProblem n) {x₀ : Fin n → ℝ}
    (hAx₀ : p.A.mulVec x₀ = -p.b) :
    ∀ y, p.objective (x₀ + y) = p.objective x₀ + dotProduct y (p.A.mulVec y) := by
  intro y
  have hsymmMul : x₀ ᵥ* p.A = p.A.mulVec x₀ := by
    -- Symmetry identifies the row action with the column action.
    simpa [p.symm.eq] using (Matrix.vecMul_transpose p.A x₀)
  have hcross : dotProduct x₀ (p.A.mulVec y) = dotProduct y (p.A.mulVec x₀) := by
    -- Rewrite the mixed term through the transpose action and commute the real dot product.
    calc
      dotProduct x₀ (p.A.mulVec y) = dotProduct (x₀ ᵥ* p.A) y := by
        rw [Matrix.dotProduct_mulVec]
      _ = dotProduct (p.A.mulVec x₀) y := by
        rw [hsymmMul]
      _ = dotProduct y (p.A.mulVec x₀) := by
        rw [dotProduct_comm]
  -- Expand the translated objective and cancel the linear terms with stationarity.
  calc
    p.objective (x₀ + y)
        = dotProduct x₀ (p.A.mulVec x₀) + dotProduct x₀ (p.A.mulVec y) +
            (dotProduct y (p.A.mulVec x₀) + dotProduct y (p.A.mulVec y)) +
            (2 * dotProduct p.b x₀ + 2 * dotProduct p.b y) := by
          simp [QuadraticBallConstrainedProblem.objective, Matrix.mulVec_add, add_dotProduct,
            dotProduct_add, mul_add, add_assoc, add_left_comm, add_comm]
    _ = dotProduct x₀ (p.A.mulVec x₀) + 2 * dotProduct p.b x₀ + dotProduct y (p.A.mulVec y) := by
          rw [hcross, hAx₀, dotProduct_neg, dotProduct_neg, dotProduct_comm y p.b]
          ring
    _ = p.objective x₀ + dotProduct y (p.A.mulVec y) := by
          simp [QuadraticBallConstrainedProblem.objective, add_left_comm, add_comm]

/-- The objective value at the unconstrained candidate is `-bᵀ A⁻¹ b`. -/
lemma objective_at_unconstrained_candidate
    {n : ℕ} (p : QuadraticBallConstrainedProblem n) {x₀ : Fin n → ℝ}
    (hx₀ : x₀ = -(p.A⁻¹.mulVec p.b)) :
    p.objective x₀ = -dotProduct p.b (p.A⁻¹.mulVec p.b) := by
  have hAx₀ : p.A.mulVec x₀ = -p.b := unconstrained_candidate_mulVec_eq_neg_b p hx₀
  -- Replace the quadratic term using stationarity, then rewrite `x₀`.
  calc
    p.objective x₀ = dotProduct x₀ (p.A.mulVec x₀) + 2 * dotProduct p.b x₀ := by
      rfl
    _ = dotProduct x₀ (-p.b) + 2 * dotProduct p.b x₀ := by
      rw [hAx₀]
    _ = -dotProduct p.b x₀ + 2 * dotProduct p.b x₀ := by
      rw [dotProduct_neg, dotProduct_comm x₀ p.b]
    _ = dotProduct p.b x₀ := by
      ring
    _ = -dotProduct p.b (p.A⁻¹.mulVec p.b) := by
      rw [hx₀, dotProduct_neg]

/-
Let quadratic ball - constrained problem. Let x_0 = - A^ - 1b. Prove that if ‖x_0‖_2 ≤ Δ, then the
optimal solution is x^* = x_0, and write down the corresponding expression for the optimal value of
the optimization problem.
-/
theorem unconstrained_minimizer_is_optimal_when_feasible
    {n : ℕ} (p : QuadraticBallConstrainedProblem n) (x₀ : Fin n → ℝ)
    (hx₀ : x₀ = -(p.A⁻¹.mulVec p.b))
    (hfeas : p.feasible x₀) :
    IsMinOn p.objective {x | p.feasible x} x₀ ∧
      p.objective x₀ = -dotProduct p.b (p.A⁻¹.mulVec p.b) := by
  have htranslate :
      ∀ y, p.objective (x₀ + y) = p.objective x₀ + dotProduct y (p.A.mulVec y) :=
    objective_translate_eq_objective_at_candidate_add_quadratic p
      (unconstrained_candidate_mulVec_eq_neg_b p hx₀)
  have hglobal : IsMinOn p.objective Set.univ x₀ := by
    intro x hx
    let y : Fin n → ℝ := x - x₀
    have hy : x₀ + y = x := by
      -- Every point is the candidate plus its displacement from the candidate.
      ext i
      dsimp [y]
      ring
    have hnonneg : 0 ≤ dotProduct y (p.A.mulVec y) := by
      -- Positive definiteness gives nonnegativity of the residual quadratic term.
      by_cases hy0 : y = 0
      · simp [hy0]
      · exact le_of_lt (p.posDef y hy0)
    -- Compare the value at `x` with the translated expansion around `x₀`.
    calc
      p.objective x₀ ≤ p.objective x₀ + dotProduct y (p.A.mulVec y) := by
        simpa using add_le_add_left hnonneg (p.objective x₀)
      _ = p.objective (x₀ + y) := by
        rw [(htranslate y).symm]
      _ = p.objective x := by
        rw [hy]
  constructor
  · -- Restrict the global minimum to the feasible ball.
    exact hglobal.on_subset (Set.subset_univ _)
  · -- Evaluate the objective at the explicit unconstrained minimizer.
    exact objective_at_unconstrained_candidate p hx₀

/-
Let quadratic ball - constrained problem. Let x_0 = - A^ - 1b. Prove that if ‖x_0‖_2 > Δ, then there
exists a unique λ^* > 0 such that ‖(A + λ^* I)^ - 1 b‖_2 = Δ, and the optimal solution is x^* = - (A
+ λ^*
I)^ - 1 b, and write down the corresponding expression for the optimal value of the optimization
problem.
-/
set_option maxHeartbeats 2000000 in
theorem boundary_case_has_shifted_inverse_characterization
    {n : ℕ} (p : QuadraticBallConstrainedProblem n) (x₀ : Fin n → ℝ)
    (hx₀ : x₀ = -(p.A⁻¹.mulVec p.b))
    (houtside : p.Δ < l2Norm x₀) :
    ∃! lam : ℝ,
      0 < lam ∧
      l2Norm (((p.A + lam • 1)⁻¹).mulVec p.b) = p.Δ ∧
      IsMinOn p.objective {x | p.feasible x} (-(((p.A + lam • 1)⁻¹).mulVec p.b)) ∧
      p.objective (-(((p.A + lam • 1)⁻¹).mulVec p.b)) =
        -dotProduct p.b (((p.A + lam • 1)⁻¹).mulVec p.b) -
          lam * p.Δ ^ 2 := by
  -- Route correction: instead of introducing unfinished global helpers, solve the boundary case
  -- through a Euclidean-space minimizer, then recover the shifted inverse candidate locally.
  let objectiveE : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) p.A).reApplyInnerSelf y +
      (((2 : ℝ) • innerSL ℝ (WithLp.toLp 2 p.b)) y)
  have hAherm : p.A.IsHermitian := by
    -- Over `ℝ`, symmetry is exactly Hermitian symmetry.
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using p.symm
  have hAeuclid_symm :
      ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) p.A :
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).toLinearMap).IsSymmetric := by
    -- The Euclidean linear operator attached to a symmetric real matrix is symmetric.
    simpa [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
      (Matrix.isHermitian_iff_isSymmetric).mp hAherm
  have hl2_eq_norm : ∀ x : Fin n → ℝ, l2Norm x = ‖WithLp.toLp 2 x‖ := by
    -- The custom `l2Norm` is the ordinary Euclidean norm after moving to `WithLp 2`.
    intro x
    simpa [l2Norm, EuclideanSpace.norm_eq]
  have hobjectiveE : ∀ x : Fin n → ℝ, objectiveE (WithLp.toLp 2 x) = p.objective x := by
    -- Rewrite the Euclidean objective back in coordinates.
    intro x
    have hquad :
        dotProduct x (p.A.mulVec x) =
          (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) p.A).reApplyInnerSelf
            (WithLp.toLp 2 x) := by
      simpa [ContinuousLinearMap.reApplyInnerSelf_apply,
        Matrix.ofLp_toEuclideanCLM, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
        (hAeuclid_symm.coe_reApplyInnerSelf_apply (WithLp.toLp 2 x)).symm
    have hlin :
        2 * dotProduct p.b x =
          (((2 : ℝ) • innerSL ℝ (WithLp.toLp 2 p.b)) (WithLp.toLp 2 x)) := by
      simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    simp [objectiveE, QuadraticBallConstrainedProblem.objective, hquad, hlin]
  have hobjectiveE_cont : Continuous objectiveE := by
    -- Both the quadratic term and the linear term are continuous on Euclidean space.
    exact (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) p.A).reApplyInnerSelf_continuous.add
      ((((2 : ℝ) • innerSL ℝ (WithLp.toLp 2 p.b))).continuous)
  let closedBallE : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall 0 p.Δ
  have hclosedBallE_nonempty : closedBallE.Nonempty := by
    -- The origin is feasible because `Δ > 0`.
    exact ⟨0, by simpa [closedBallE, dist_eq_norm] using (p.delta_pos.le : 0 ≤ p.Δ)⟩
  obtain ⟨yStar, hyStar_mem, hyStar_min⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) p.Δ).exists_isMinOn
      hclosedBallE_nonempty hobjectiveE_cont.continuousOn
  let xStar : Fin n → ℝ := WithLp.ofLp yStar
  have hyStar_feas : ‖yStar‖ ≤ p.Δ := by
    simpa [closedBallE] using hyStar_mem
  have hxStar_feas : p.feasible xStar := by
    -- Pull the Euclidean closed-ball bound back to the original coordinates.
    simpa [QuadraticBallConstrainedProblem.feasible, xStar, hl2_eq_norm] using hyStar_feas
  have hxStar_min : IsMinOn p.objective {x | p.feasible x} xStar := by
    -- Every feasible coordinate vector maps into the Euclidean closed ball.
    intro x hx
    have hxBall : WithLp.toLp 2 x ∈ closedBallE := by
      simpa [closedBallE, QuadraticBallConstrainedProblem.feasible, hl2_eq_norm] using hx
    simpa [xStar, hobjectiveE x, hobjectiveE xStar] using hyStar_min hxBall
  have hobjectiveE_deriv :
      HasStrictFDerivAt objectiveE
        (2 • innerSL ℝ
          ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) p.A) yStar + WithLp.toLp 2 p.b)) yStar := by
    -- Differentiate the quadratic and linear terms separately.
    have hquad :=
      hAeuclid_symm.hasStrictFDerivAt_reApplyInnerSelf yStar
    have hlin :
        HasStrictFDerivAt
          (fun z : EuclideanSpace ℝ (Fin n) =>
            (((2 : ℝ) • innerSL ℝ (WithLp.toLp 2 p.b)) z))
          (((2 : ℝ) • innerSL ℝ (WithLp.toLp 2 p.b))) yStar := by
      simpa using (((2 : ℝ) • innerSL ℝ (WithLp.toLp 2 p.b))).hasStrictFDerivAt
    simpa [objectiveE, ContinuousLinearMap.add_apply, two_smul, smul_add] using hquad.add hlin
  have hx0_ball_eq :
      objectiveE (WithLp.toLp 2 x₀) = p.objective x₀ := hobjectiveE x₀
  have hyStar_boundary : ‖yStar‖ = p.Δ := by
    by_contra hyStrict
    have hyStrict' : ‖yStar‖ < p.Δ := lt_of_le_of_ne hyStar_feas hyStrict
    have hball_subset :
        Metric.ball yStar (p.Δ - ‖yStar‖) ⊆ closedBallE := by
      intro z hz
      change z ∈ Metric.closedBall 0 p.Δ
      rw [Metric.mem_closedBall, dist_eq_norm]
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have hznorm : ‖z‖ < p.Δ := by
        calc
          ‖z‖ ≤ ‖z - yStar‖ + ‖yStar‖ := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              norm_add_le (z - yStar) yStar
          _ < (p.Δ - ‖yStar‖) + ‖yStar‖ := by
            simpa [add_comm, add_left_comm, add_assoc] using add_lt_add_right hz ‖yStar‖
          _ = p.Δ := by ring
      simpa using hznorm.le
    have hclosedBallE_nhds : closedBallE ∈ 𝓝 yStar := by
      refine mem_of_superset (Metric.ball_mem_nhds _ (sub_pos.mpr hyStrict')) hball_subset
    have hyStar_localMin : IsLocalMin objectiveE yStar := by
      -- An interior minimizer on the closed ball is an unconstrained local minimizer.
      exact hyStar_min.localize.isLocalMin hclosedBallE_nhds
    have hderiv_zero : 2 • innerSL ℝ
        ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) p.A) yStar + WithLp.toLp 2 p.b) = 0 := by
      simpa using hyStar_localMin.hasFDerivAt_eq_zero hobjectiveE_deriv.hasFDerivAt
    have hstationary_dual :
        innerSL ℝ
          ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) p.A) yStar + WithLp.toLp 2 p.b) = 0 := by
      apply smul_right_injective (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (two_ne_zero : (2 : ℝ) ≠ 0)
      simpa [two_smul] using hderiv_zero
    have hstationary :
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) p.A) yStar + WithLp.toLp 2 p.b = 0 := by
      have hzero :
          innerSL ℝ
            ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) p.A) yStar + WithLp.toLp 2 p.b) =
            innerSL ℝ (0 : EuclideanSpace ℝ (Fin n)) := by
        simpa using hstationary_dual
      exact innerSL_inj.mp hzero
    have hAxStar : p.A.mulVec xStar = -p.b := by
      -- Returning from Euclidean space gives the stationarity equation in coordinates.
      simpa [xStar, Matrix.ofLp_toEuclideanCLM, eq_neg_iff_add_eq_zero] using congrArg WithLp.ofLp hstationary
    letI : Invertible p.A := (quadratic_problem_matrix_posDef p).isUnit.invertible
    have hxStar_eq_x0 : xStar = x₀ := by
      -- Positive definiteness makes the stationary point unique.
      calc
        xStar = (p.A⁻¹ * p.A).mulVec xStar := by
          simp [Matrix.inv_mul_of_invertible]
        _ = p.A⁻¹.mulVec (p.A.mulVec xStar) := by rw [Matrix.mulVec_mulVec]
        _ = -(p.A⁻¹.mulVec p.b) := by rw [hAxStar, Matrix.mulVec_neg]
        _ = x₀ := by rw [hx₀]
    have : l2Norm x₀ ≤ p.Δ := by
      simpa [hxStar_eq_x0] using hxStar_feas
    exact (not_lt_of_ge this) houtside
  have hyStar_sq : ‖yStar‖ ^ 2 = p.Δ ^ 2 := by
    -- The Euclidean minimizer sits exactly on the sphere of radius `Δ`.
    rw [hyStar_boundary]
  have hconstraint_min :
      IsLocalMinOn objectiveE {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ^ 2 = p.Δ ^ 2} yStar := by
    -- Restrict the global ball minimum to the boundary sphere cut out by `‖y‖ = Δ`.
    have hySphere_min :
        IsMinOn objectiveE {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ^ 2 = p.Δ ^ 2} yStar := by
      intro y hy
      have hyBall : y ∈ closedBallE := by
        have hynorm : ‖y‖ = p.Δ := (sq_eq_sq₀ (norm_nonneg _) p.delta_pos.le).mp hy
        simpa [closedBallE, dist_eq_norm, hynorm]
      exact hyStar_min hyBall
    exact hySphere_min.localize
  have hconstraint_extr :
      IsLocalExtrOn objectiveE {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ^ 2 = ‖yStar‖ ^ 2} yStar := by
    simpa [hyStar_sq] using
      (show IsLocalExtrOn objectiveE {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ^ 2 = p.Δ ^ 2} yStar from
        Or.inl hconstraint_min)
  obtain ⟨a, b, hab_ne, hab_eq⟩ :=
    IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d
      hconstraint_extr
      (hasStrictFDerivAt_norm_sq yStar) hobjectiveE_deriv
  have hstationary_vec :
      a • yStar +
        b • (((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) p.A) yStar) + WithLp.toLp 2 p.b) = 0 := by
    -- Convert the dual equality from Lagrange multipliers into a vector equality.
    have h0 :
        a • innerSL ℝ yStar +
          b • innerSL ℝ
            (((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) p.A) yStar) + WithLp.toLp 2 p.b) = 0 := by
      apply smul_right_injective (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (two_ne_zero : (2 : ℝ) ≠ 0)
      simpa [two_smul, smul_add, add_smul, add_assoc] using hab_eq
    have h0' :
        innerSL ℝ
          (a • yStar +
            b • (((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) p.A) yStar) + WithLp.toLp 2 p.b)) = 0 := by
      ext z
      have hz :=
        congrArg (fun f : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => f z) h0
      simpa [innerSL_apply_apply, real_inner_smul_left, add_comm, add_left_comm,
        add_assoc, smul_add] using hz
    have h0'' :
        innerSL ℝ
          (a • yStar +
            b • (((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) p.A) yStar) + WithLp.toLp 2 p.b)) =
          innerSL ℝ (0 : EuclideanSpace ℝ (Fin n)) := by
      simpa using h0'
    exact innerSL_inj.mp h0''
  have hb_ne : b ≠ 0 := by
    intro hb
    have ha_ne : a ≠ 0 := by simpa [hb] using hab_ne
    have hyStar_zero : yStar = 0 := by
      apply smul_right_injective (EuclideanSpace ℝ (Fin n)) ha_ne
      simpa [hb] using hstationary_vec
    have : 0 = p.Δ := by
      simpa [hyStar_zero] using hyStar_boundary
    linarith [p.delta_pos]
  let lam : ℝ := a / b
  have hstationary_shift :
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) p.A) yStar + WithLp.toLp 2 p.b =
        -(lam • yStar) := by
    -- Divide the multiplier identity by the nonzero coefficient `b`.
    have hscaled :
        b •
            (lam • yStar +
              ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) p.A) yStar +
                WithLp.toLp 2 p.b)) =
          0 := by
      calc
        b •
            (lam • yStar +
              ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) p.A) yStar +
                WithLp.toLp 2 p.b))
            =
          a • yStar +
            b •
              (((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) p.A) yStar) +
                WithLp.toLp 2 p.b) := by
              simp [lam, smul_add, smul_smul, div_eq_mul_inv, hb_ne, mul_assoc, mul_comm,
                mul_left_comm, add_assoc, add_left_comm, add_comm]
        _ = 0 := hstationary_vec
    have hzero :
        lam • yStar +
          ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) p.A) yStar + WithLp.toLp 2 p.b) = 0 := by
      apply smul_right_injective (EuclideanSpace ℝ (Fin n)) hb_ne
      simpa using hscaled
    have hzero' :
        ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) p.A) yStar + WithLp.toLp 2 p.b) +
          lam • yStar = 0 := by
      simpa [add_assoc, add_left_comm, add_comm] using hzero
    exact eq_neg_iff_add_eq_zero.mpr hzero'
  have hshift_sum :
      p.A.mulVec xStar + p.b + lam • xStar = 0 := by
    -- Move the Euclidean stationarity equation back to coordinates.
    simpa [xStar, Matrix.ofLp_toEuclideanCLM, add_assoc, add_left_comm, add_comm] using
      congrArg WithLp.ofLp (eq_neg_iff_add_eq_zero.mp hstationary_shift)
  have hshift_mat : (p.A + lam • 1).mulVec xStar = -p.b := by
    -- This is the matrix stationarity equation for the shifted problem.
    apply eq_neg_iff_add_eq_zero.mpr
    simpa [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, add_assoc, add_left_comm,
      add_comm] using hshift_sum
  let v : EuclideanSpace ℝ (Fin n) :=
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) p.A) yStar + WithLp.toLp 2 p.b
  have hyStar_localMin_ball : IsLocalMinOn objectiveE closedBallE yStar := hyStar_min.localize
  have hzero_mem : (0 : EuclideanSpace ℝ (Fin n)) ∈ closedBallE := by
    -- The origin belongs to the feasible ball because `Δ > 0`.
    simpa [closedBallE, dist_eq_norm] using (p.delta_pos.le : 0 ≤ p.Δ)
  have hy_inward :
      -yStar ∈ posTangentConeAt closedBallE yStar := by
    -- The inward radial direction stays inside the closed ball.
    have hsegment : segment ℝ yStar 0 ⊆ closedBallE :=
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) p.Δ).segment_subset hyStar_mem hzero_mem
    simpa using sub_mem_posTangentConeAt_of_segment_subset hsegment
  have hderiv_inward :
      0 ≤ (2 • innerSL ℝ v) (-yStar) := by
    -- Local minimality on the ball forces the derivative in every inward direction to be nonnegative.
    exact hyStar_localMin_ball.hasFDerivWithinAt_nonneg
      hobjectiveE_deriv.hasFDerivAt.hasFDerivWithinAt hy_inward
  have hinner_nonpos :
      (innerSL ℝ v) yStar ≤ 0 := by
    -- Evaluating the derivative in the inward direction turns the sign into a nonpositivity statement.
    let qA : ℝ := (innerSL ℝ ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) p.A) yStar)) yStar
    let qB : ℝ := (innerSL ℝ (WithLp.toLp 2 p.b)) yStar
    have h : 2 * qB ≤ -(2 * qA) := by
      simpa [v, qA, qB, innerSL_apply_apply] using hderiv_inward
    have hsum : qA + qB ≤ 0 := by
      nlinarith
    simpa [v, qA, qB, innerSL_apply_apply] using hsum
  have hlam_nonneg : 0 ≤ lam := by
    -- Route correction: the multiplier sign comes from the inward derivative, not from ad hoc algebra.
    have hinner_eq :
        (innerSL ℝ v) yStar = -lam * ‖yStar‖ ^ 2 := by
      simpa [v, real_inner_self_eq_norm_sq, mul_assoc, mul_comm, mul_left_comm] using
        congrArg (fun z => (innerSL ℝ z) yStar) hstationary_shift
    have hprod_nonneg : 0 ≤ lam * ‖yStar‖ ^ 2 := by
      nlinarith [hinner_nonpos, hinner_eq]
    have hnorm_sq_pos : 0 < ‖yStar‖ ^ 2 := by
      rw [hyStar_boundary]
      nlinarith [p.delta_pos]
    nlinarith
  have hlam_ne_zero : lam ≠ 0 := by
    -- If `lam = 0`, then `xStar` solves the original unconstrained stationarity equation, so it
    -- must equal `x₀`, contradicting `houtside`.
    intro hlam_zero
    have hAxStar : p.A.mulVec xStar = -p.b := by
      simpa [hlam_zero, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using hshift_mat
    letI : Invertible p.A := (quadratic_problem_matrix_posDef p).isUnit.invertible
    have hxStar_eq_x0 : xStar = x₀ := by
      calc
        xStar = (p.A⁻¹ * p.A).mulVec xStar := by
          simp [Matrix.inv_mul_of_invertible]
        _ = p.A⁻¹.mulVec (p.A.mulVec xStar) := by
          rw [Matrix.mulVec_mulVec]
        _ = -(p.A⁻¹.mulVec p.b) := by
          rw [hAxStar, Matrix.mulVec_neg]
        _ = x₀ := by
          rw [hx₀]
    have : l2Norm x₀ ≤ p.Δ := by
      simpa [hxStar_eq_x0] using hxStar_feas
    exact (not_lt_of_ge this) houtside
  have hlam_pos : 0 < lam := by
    -- Positivity is the nonnegative sign plus the exclusion of the degenerate stationary case.
    exact lt_of_le_of_ne hlam_nonneg (by
      intro hzero
      exact hlam_ne_zero hzero.symm)
  have hshifted_posDef :
      ∀ {μ : ℝ}, 0 ≤ μ → (p.A + μ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
    -- Any nonnegative identity shift preserves positive definiteness.
    intro μ hμ
    have hsemidefμ : (μ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
      exact Matrix.PosSemidef.one.smul hμ
    exact (quadratic_problem_matrix_posDef p).add_posSemidef hsemidefμ
  have hshift_posDef : (p.A + lam • 1).PosDef := by
    -- Adding a nonnegative multiple of the identity preserves positive definiteness.
    exact hshifted_posDef hlam_nonneg
  have hshift_symm : (p.A + lam • 1).IsSymm := by
    -- Over `ℝ`, Hermitian symmetry is ordinary matrix symmetry.
    simpa [Matrix.IsSymm, Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hshift_posDef.isHermitian
  have hshift_dotpos :
      ∀ x : Fin n → ℝ, x ≠ 0 → 0 < dotProduct x ((p.A + lam • 1).mulVec x) := by
    -- The shifted quadratic form stays strictly positive on nonzero vectors.
    intro x hx
    simpa using hshift_posDef.dotProduct_mulVec_pos hx
  let q : QuadraticBallConstrainedProblem n :=
    { A := p.A + lam • 1
      b := p.b
      Δ := p.Δ
      symm := hshift_symm
      posDef := hshift_dotpos
      delta_pos := p.delta_pos }
  let z : Fin n → ℝ := ((p.A + lam • 1)⁻¹).mulVec p.b
  have hxStar_repr : xStar = -z := by
    -- Invert the shifted stationarity equation to recover the explicit optimizer.
    letI : Invertible (p.A + lam • 1) := hshift_posDef.isUnit.invertible
    calc
      xStar = (1 : Matrix (Fin n) (Fin n) ℝ).mulVec xStar := by
        simp
      _ = (((p.A + lam • 1)⁻¹) * (p.A + lam • 1)).mulVec xStar := by
        rw [Matrix.inv_mul_of_invertible]
      _ = ((p.A + lam • 1)⁻¹).mulVec ((p.A + lam • 1).mulVec xStar) := by
        rw [Matrix.mulVec_mulVec]
      _ = -z := by
        rw [hshift_mat, Matrix.mulVec_neg]
  have hxStar_feas_q : q.feasible xStar := by
    -- The shifted problem has the same feasible set.
    simpa [q, QuadraticBallConstrainedProblem.feasible] using hxStar_feas
  have hq_opt := unconstrained_minimizer_is_optimal_when_feasible q xStar hxStar_repr hxStar_feas_q
  have hq_min : IsMinOn q.objective {x | q.feasible x} xStar := hq_opt.1
  have hq_value :
      q.objective xStar = -dotProduct p.b (((p.A + lam • 1)⁻¹).mulVec p.b) := by
    -- The shifted problem is solved by the same explicit inverse formula.
    simpa [q] using hq_opt.2
  have hdot_eq_norm_sq : ∀ x : Fin n → ℝ, dotProduct x x = ‖WithLp.toLp 2 x‖ ^ 2 := by
    -- The coordinate dot product is exactly the Euclidean norm square.
    intro x
    have hsq := congrArg (fun t : ℝ => t * t) (hl2_eq_norm x)
    unfold l2Norm at hsq
    have hsq' :
        √(∑ i, x i * x i) * √(∑ i, x i * x i) = ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 x‖ := by
      simpa [pow_two] using hsq
    have hsqrt : √(∑ i, x i * x i) * √(∑ i, x i * x i) = dotProduct x x := by
      rw [dotProduct, ← pow_two]
      exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => mul_self_nonneg (x i))
    calc
      dotProduct x x = √(∑ i, x i * x i) * √(∑ i, x i * x i) := hsqrt.symm
      _ = ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 x‖ := hsq'
      _ = ‖WithLp.toLp 2 x‖ ^ 2 := by rw [pow_two]
  have hxStar_l2 : l2Norm xStar = p.Δ := by
    -- The minimizing point lies on the boundary sphere.
    simpa [xStar, hl2_eq_norm] using hyStar_boundary
  have hxStar_sq : dotProduct xStar xStar = p.Δ ^ 2 := by
    -- Squaring the Euclidean norm identity converts the boundary condition into a dot-product identity.
    have hxStar_norm : ‖WithLp.toLp 2 xStar‖ = p.Δ := by
      simpa [hl2_eq_norm xStar] using hxStar_l2
    rw [hdot_eq_norm_sq xStar]
    nlinarith [norm_nonneg (WithLp.toLp 2 xStar), hxStar_norm]
  have hfeas_sq_le : ∀ {x : Fin n → ℝ}, p.feasible x → dotProduct x x ≤ p.Δ ^ 2 := by
    -- Feasibility controls the Euclidean norm square by `Δ²`.
    intro x hx
    have hxnorm : ‖WithLp.toLp 2 x‖ ≤ p.Δ := by
      simpa [QuadraticBallConstrainedProblem.feasible, hl2_eq_norm] using hx
    rw [hdot_eq_norm_sq x]
    nlinarith [norm_nonneg (WithLp.toLp 2 x), hxnorm]
  have hq_objective_eq :
      ∀ x : Fin n → ℝ, q.objective x = p.objective x + lam * dotProduct x x := by
    -- Expanding the shifted quadratic form adds exactly `lam * ‖x‖²`.
    intro x
    simp [q, QuadraticBallConstrainedProblem.objective, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_add, dotProduct_smul, smul_dotProduct, mul_assoc, mul_comm,
      mul_left_comm, add_assoc, add_left_comm, add_comm]
  have hxStar_min_shift : IsMinOn p.objective {x | p.feasible x} xStar := by
    -- Compare the shifted objective at `xStar` and any feasible point, then subtract the
    -- nonnegative `lam * ‖x‖²` correction.
    intro x hx
    have hq_le : q.objective xStar ≤ q.objective x := by
      simpa [q, QuadraticBallConstrainedProblem.feasible] using
        hq_min (show q.feasible x by simpa [q, QuadraticBallConstrainedProblem.feasible] using hx)
    have hq_xStar : q.objective xStar = p.objective xStar + lam * p.Δ ^ 2 := by
      rw [hq_objective_eq, hxStar_sq]
    have hq_x : q.objective x = p.objective x + lam * dotProduct x x := hq_objective_eq x
    have hx_sq_le : dotProduct x x ≤ p.Δ ^ 2 := hfeas_sq_le hx
    have hcorr : lam * dotProduct x x ≤ lam * p.Δ ^ 2 := by
      gcongr
    have hmain : p.objective xStar + lam * p.Δ ^ 2 ≤ p.objective x + lam * dotProduct x x := by
      nlinarith [hq_le, hq_xStar, hq_x]
    have hmain' : p.objective xStar + lam * p.Δ ^ 2 ≤ p.objective x + lam * p.Δ ^ 2 :=
      le_trans hmain (by gcongr)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      sub_le_sub_right hmain' (lam * p.Δ ^ 2)
  have hxStar_value :
      p.objective xStar =
        -dotProduct p.b (((p.A + lam • 1)⁻¹).mulVec p.b) - lam * p.Δ ^ 2 := by
    -- The shifted objective value differs from the original by exactly `lam * Δ²` on the boundary.
    have hq_xStar : q.objective xStar = p.objective xStar + lam * p.Δ ^ 2 := by
      rw [hq_objective_eq, hxStar_sq]
    have hq_xStar' :
        p.objective xStar = q.objective xStar - lam * p.Δ ^ 2 := by
      calc
        p.objective xStar = p.objective xStar + lam * p.Δ ^ 2 - lam * p.Δ ^ 2 := by
          ring
        _ = q.objective xStar - lam * p.Δ ^ 2 := by
          rw [hq_xStar]
    calc
      p.objective xStar = q.objective xStar - lam * p.Δ ^ 2 := hq_xStar'
      _ = -dotProduct p.b (((p.A + lam • 1)⁻¹).mulVec p.b) - lam * p.Δ ^ 2 := by
        rw [hq_value]
  refine ⟨lam, ?_, ?_⟩
  · refine ⟨hlam_pos, ?_, ?_, ?_⟩
    · -- The explicit inverse point lies on the boundary sphere.
      change l2Norm z = p.Δ
      have hxStar_l2_neg : l2Norm (-z) = p.Δ := by
        have htmp := hxStar_l2
        rw [hxStar_repr] at htmp
        exact htmp
      have hnorm_neg :
          ‖WithLp.toLp 2 (-z)‖ = p.Δ := by
        rw [hl2_eq_norm (-z)] at hxStar_l2_neg
        exact hxStar_l2_neg
      rw [hl2_eq_norm z]
      calc
        ‖WithLp.toLp 2 z‖ = ‖WithLp.toLp 2 (-z)‖ := by
          exact (norm_neg (WithLp.toLp 2 z)).symm
        _ = p.Δ := hnorm_neg
    · -- Rewriting the optimizer identifies the minimum point in the original problem.
      change IsMinOn p.objective {x | p.feasible x} (-z)
      have hxStar_eq : -z = xStar := hxStar_repr.symm
      exact hxStar_eq ▸ hxStar_min_shift
    · -- Rewriting the optimizer also gives the claimed objective value.
      change p.objective (-z) = -dotProduct p.b z - lam * p.Δ ^ 2
      have hxStar_eq : -z = xStar := hxStar_repr.symm
      exact hxStar_eq ▸ hxStar_value
  · intro lam' hlam'
    -- Route correction: reuse the already-built shifted problem `q` to identify the second witness,
    -- then compare the two shifted stationarity equations instead of packaging a second heavy problem.
    rcases hlam' with ⟨hlam'_pos, hz'_boundary, hmin', _⟩
    let z' : Fin n → ℝ := ((p.A + lam' • 1)⁻¹).mulVec p.b
    let x' : Fin n → ℝ := -z'
    have hz'_norm : ‖WithLp.toLp 2 z'‖ = p.Δ := by
      -- Rewrite the boundary condition into the Euclidean norm used by the translated objective.
      rw [← hl2_eq_norm z']
      exact hz'_boundary
    have hx'_norm : ‖WithLp.toLp 2 x'‖ = p.Δ := by
      -- Negating the witness does not change its Euclidean norm.
      calc
        ‖WithLp.toLp 2 x'‖ = ‖WithLp.toLp 2 z'‖ := by
          simp [x']
        _ = p.Δ := hz'_norm
    have hx'_feas : p.feasible x' := by
      -- The second witness lies on the same boundary sphere, hence is feasible.
      simpa [QuadraticBallConstrainedProblem.feasible, hl2_eq_norm x'] using hx'_norm.le
    have hx'_sq : dotProduct x' x' = p.Δ ^ 2 := by
      -- Converting the norm identity to a dot-product identity aligns the correction terms in `q`.
      rw [hdot_eq_norm_sq x']
      nlinarith [norm_nonneg (WithLp.toLp 2 x'), hx'_norm]
    have hp_eq : p.objective xStar = p.objective x' := by
      -- Both boundary points minimize the original constrained problem.
      have hp_le1 : p.objective xStar ≤ p.objective x' := hxStar_min_shift hx'_feas
      have hp_le2 : p.objective x' ≤ p.objective xStar := hmin' hxStar_feas
      exact le_antisymm hp_le1 hp_le2
    have hq_eq : q.objective x' = q.objective xStar := by
      -- On the boundary, `q.objective` differs from `p.objective` by the same `lam * Δ²` term.
      calc
        q.objective x' = p.objective x' + lam * p.Δ ^ 2 := by
          rw [hq_objective_eq, hx'_sq]
        _ = p.objective xStar + lam * p.Δ ^ 2 := by
          rw [← hp_eq]
        _ = q.objective xStar := by
          rw [hq_objective_eq, hxStar_sq]
    have hq_stationary : q.A.mulVec xStar = -q.b := by
      -- `xStar` is the unconstrained minimizer of the shifted problem `q`.
      exact unconstrained_candidate_mulVec_eq_neg_b q hxStar_repr
    have hx'_decomp : xStar + (x' - xStar) = x' := by
      -- Writing `x'` as the shifted point plus its displacement prepares the translation formula.
      ext i
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hzero_quadratic :
        dotProduct (x' - xStar) (q.A.mulVec (x' - xStar)) = 0 := by
      -- Equal shifted objective values force the translated quadratic error term to vanish.
      have htranslate :=
        objective_translate_eq_objective_at_candidate_add_quadratic q hq_stationary (x' - xStar)
      rw [hx'_decomp, hq_eq] at htranslate
      linarith
    have hx'_eq_xStar : x' = xStar := by
      -- Positive definiteness of `q.A` makes the vanishing quadratic error possible only at `0`.
      have hsub_zero : x' - xStar = 0 := by
        by_contra hne
        have hpos : 0 < dotProduct (x' - xStar) (q.A.mulVec (x' - xStar)) := q.posDef _ hne
        linarith
      exact sub_eq_zero.mp hsub_zero
    have hshift'_mat : (p.A + lam' • 1).mulVec x' = -p.b := by
      -- Cancel the explicit inverse to recover the shifted stationarity equation for the second witness.
      letI : Invertible (p.A + lam' • 1) := (hshifted_posDef (le_of_lt hlam'_pos)).isUnit.invertible
      calc
        (p.A + lam' • 1).mulVec x' = (p.A + lam' • 1).mulVec (-z') := by
          rfl
        _ = -((p.A + lam' • 1).mulVec z') := by
          rw [Matrix.mulVec_neg]
        _ = -((p.A + lam' • 1).mulVec (((p.A + lam' • 1)⁻¹).mulVec p.b)) := by
          rfl
        _ = -(((p.A + lam' • 1) * (p.A + lam' • 1)⁻¹).mulVec p.b) := by
          rw [Matrix.mulVec_mulVec]
        _ = -((1 : Matrix (Fin n) (Fin n) ℝ).mulVec p.b) := by
          rw [Matrix.mul_inv_of_invertible]
        _ = -p.b := by
          rw [Matrix.one_mulVec]
    have hshift'_mat_xStar : (p.A + lam' • 1).mulVec xStar = -p.b := by
      -- After identifying the second witness with `xStar`, both shifts solve a stationarity equation at `xStar`.
      simpa [hx'_eq_xStar] using hshift'_mat
    have hsame_smul : lam • xStar = lam' • xStar := by
      -- Expanding both shifted equations and cancelling the common `A xStar` term isolates the scalar part.
      have hsum :
          p.A.mulVec xStar + lam • xStar = p.A.mulVec xStar + lam' • xStar := by
        calc
          p.A.mulVec xStar + lam • xStar = (p.A + lam • 1).mulVec xStar := by
            simp [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, add_assoc,
              add_left_comm, add_comm]
          _ = -p.b := hshift_mat
          _ = (p.A + lam' • 1).mulVec xStar := hshift'_mat_xStar.symm
          _ = p.A.mulVec xStar + lam' • xStar := by
            simp [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, add_assoc,
              add_left_comm, add_comm]
      exact add_left_cancel hsum
    have hscalar_zero : (lam - lam') • xStar = 0 := by
      -- Rewriting the equality of scalar multiples as a single vanishing scalar action sets up a
      -- coordinatewise cancellation argument.
      have hdiff : lam • xStar - lam' • xStar = 0 := sub_eq_zero.mpr hsame_smul
      simpa [sub_smul] using hdiff
    have hxStar_ne_zero : xStar ≠ 0 := by
      -- The boundary condition `‖xStar‖ = Δ > 0` rules out the zero vector.
      intro hxzero
      have hdelta_zero : 0 = p.Δ := by
        simpa [hxzero, l2Norm] using hxStar_l2
      linarith [p.delta_pos]
    have hcoord_nonzero : ∃ i, xStar i ≠ 0 := by
      -- A nonzero vector has a nonzero coordinate.
      by_contra hnone
      push_neg at hnone
      exact hxStar_ne_zero (funext hnone)
    obtain ⟨i, hi⟩ := hcoord_nonzero
    have hcoord : (lam - lam') * xStar i = 0 := by
      -- Evaluating the vanishing scalar action at a nonzero coordinate isolates the scalar factor.
      simpa using congrFun hscalar_zero i
    have hdiff_zero : lam - lam' = 0 := by
      rcases mul_eq_zero.mp hcoord with hdiff | hxi
      · exact hdiff
      · exact (hi hxi).elim
    exact (sub_eq_zero.mp hdiff_zero).symm

end «problem-181»
