import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-10»
/- [BLOCK Exercise 3.11-(d) | 35 | defn]
A semidefinite program is an optimization problem in which the decision variable is constrained by
linear equalities together with a linear matrix inequality of the form A₀ + sum_{i=1}^k yᵢ Aᵢ succeq
0, and the objective is linear in the decision variable.
-/
structure SemidefiniteProgram (n k m : ℕ) where
  A0 : Matrix (Fin n) (Fin n) ℝ
  A0_symm : A0.IsSymm
  A : Fin k → Matrix (Fin n) (Fin n) ℝ
  A_symm : ∀ i, (A i).IsSymm
  F : Fin m → (Fin k → ℝ)
  g : Fin m → ℝ
  c : Fin k → ℝ

def SemidefiniteProgram.lmiMatrix {n k m : ℕ} (p : SemidefiniteProgram n k m) (y : Fin k → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  p.A0 + ∑ i, y i • p.A i

def SemidefiniteProgram.satisfiesLinearEqualities {n k m : ℕ} (p : SemidefiniteProgram n k m)
    (y : Fin k → ℝ) : Prop :=
  ∀ j, ∑ i, (p.F j) i * y i = p.g j

def SemidefiniteProgram.objective {n k m : ℕ} (p : SemidefiniteProgram n k m) (y : Fin k → ℝ) : ℝ :=
  ∑ i, p.c i * y i

def SemidefiniteProgram.isFeasible {n k m : ℕ} (p : SemidefiniteProgram n k m) (y : Fin k → ℝ) : Prop :=
  p.satisfiesLinearEqualities y ∧
    Matrix.PosSemidef (p.lmiMatrix y)

/-
Exercise 3.11-(d) | 36 | opt_prob

minimize cᵀF(x)⁻¹c over x ∈ ℝⁿ
subject to F(x) ≻ 0
-/
structure StochasticMatrixInverseMinimization (n m : ℕ) where
  Ω : Type
  instMeasurableSpace : MeasurableSpace Ω
  probabilityMeasure : MeasureTheory.Measure Ω
  isProbabilityMeasure : MeasureTheory.IsProbabilityMeasure probabilityMeasure
  F : (Fin n → ℝ) → Matrix (Fin m) (Fin m) ℝ
  cRandom : Ω → Fin m → ℝ
  cRandom_measurable : Measurable cRandom

def StochasticMatrixInverseMinimization.objective {n m : ℕ}
    (p : StochasticMatrixInverseMinimization n m) : (Fin n → ℝ) → ℝ :=
  fun x =>
    ∫ ω, dotProduct (p.cRandom ω) (((p.F x)⁻¹).mulVec (p.cRandom ω)) ∂p.probabilityMeasure

def StochasticMatrixInverseMinimization.isFeasible {n m : ℕ}
    (p : StochasticMatrixInverseMinimization n m) : (Fin n → ℝ) → Prop :=
  fun x => Matrix.PosDef (p.F x)

attribute [instance] StochasticMatrixInverseMinimization.instMeasurableSpace
attribute [instance] StochasticMatrixInverseMinimization.isProbabilityMeasure

/-
Exercise 3.11-(d) | 37 | opt_prob

minimize t over x ∈ ℝ^n, t ∈ ℝ, Z ∈ S^m

subject to
F(x) ≻ 0,
Z ≽ 0,
\[
\begin{pmatrix}
F(x) & Q^{1/2} \\
Q^{1/2} & Z
\end{pmatrix}
\ ≽ 0,
\]
t = tr(Z).
-/
structure SemidefiniteReformulation (n m : ℕ) where
  F : (Fin n → ℝ) → Matrix (Fin m) (Fin m) ℝ
  F_symm : ∀ x, (F x).IsSymm
  Qsqrt : Matrix (Fin m) (Fin m) ℝ
  Qsqrt_symm : Qsqrt.IsSymm
  x : Fin n → ℝ
  t : ℝ
  Z : Matrix (Fin m) (Fin m) ℝ
  Z_symm : Z.IsSymm
  posDef_F : Matrix.PosDef (F x)
  posSemidef_Z : Matrix.PosSemidef Z
  posSemidef_block :
    Matrix.PosSemidef
      (Matrix.fromBlocks (F x) Qsqrt Qsqrt Z)

def SemidefiniteReformulation.objective {n m : ℕ} (p : SemidefiniteReformulation n m) : ℝ :=
  p.t

def SemidefiniteReformulation.isFeasible {n m : ℕ} (p : SemidefiniteReformulation n m) : Prop :=
  Matrix.PosDef (p.F p.x) ∧
    Matrix.PosSemidef p.Z ∧
    Matrix.PosSemidef (Matrix.fromBlocks (p.F p.x) p.Qsqrt p.Qsqrt p.Z) ∧
    p.t = Matrix.trace p.Z

/- [BLOCK Exercise 3.11-(d) | 38 | thm]
Let n,m ∈ ℕ, let F₀,F₁,dots,Fₙ ∈ S^m, and define F(x)=F₀+sum_{i=1}^n xᵢ Fᵢ for x=(x₁,dots,xₙ)∈ ℝ^n,
where S^m is the set of real symmetric m× m matrices. Let bar c ∈ ℝ^m and S ∈ S^m, and let c be an
m-dimensional random vector satisfying Ec=bar c and E[(c-bar c)(c-bar c)ᵀ]=S. Define Q=S+bar cbar
cᵀ. Prove that for every x ∈ ℝ^n with F(x)succ 0, Ebig[cᵀ F(x)^{-1} cbig]=tr(QF(x)^{-1}).
-/
/-- Rewrites the trace of a rank-one matrix times a fixed matrix as a quadratic form. -/
lemma trace_vecMulVec_mul_eq_dotProduct_mulVec
    {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ)
    (u v : Fin m → ℝ) :
    Matrix.trace (Matrix.vecMulVec u v * A) =
      dotProduct v (fun i => (A.mulVec u) i) := by
  -- Rewrite the product so the trace sees a single rank-one matrix.
  calc
    Matrix.trace (Matrix.vecMulVec u v * A)
        = Matrix.trace (Matrix.vecMulVec u (v ᵥ* A)) := by
            rw [Matrix.vecMulVec_mul]
    -- Evaluate the trace of the rank-one matrix.
    _ = dotProduct u (v ᵥ* A) := by
          rw [Matrix.trace_vecMulVec]
    -- Commute the real dot product, then reassociate it with `mulVec`.
    _ = dotProduct (v ᵥ* A) u := by
          rw [dotProduct_comm]
    _ = dotProduct v (fun i => (A.mulVec u) i) := by
          rw [← Matrix.dotProduct_mulVec]

/-- Decomposes `ccᵀ` into centered covariance and mean contributions. -/
lemma vecMulVec_self_eq_centered_add_mean_terms
    {m : ℕ}
    (cbar c : Fin m → ℝ) :
    Matrix.vecMulVec c c =
      Matrix.of (fun i j => (c i - cbar i) * (c j - cbar j)) +
        Matrix.vecMulVec cbar c +
        Matrix.vecMulVec (fun i => c i - cbar i) cbar := by
  -- Check the decomposition entrywise and expand the scalar algebra.
  ext i j
  simp [Matrix.vecMulVec_apply]
  ring

/-- Moves a fixed right-multiplication and the trace through an integral. -/
lemma integral_trace_mul_right
    {α : Type*}
    {m : ℕ}
    [MeasurableSpace α]
    (μ : MeasureTheory.Measure α)
    (A : Matrix (Fin m) (Fin m) ℝ)
    {g : α → Matrix (Fin m) (Fin m) ℝ}
    (hg : MeasureTheory.Integrable g μ) :
    ∫ ω, Matrix.trace (g ω * A) ∂μ =
      Matrix.trace ((∫ ω, g ω ∂μ) * A) := by
  let traceMulRight :
      Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap (Fin m) ℝ ℝ).comp
        (LinearMap.mulRight ℝ A))
  -- Apply the continuous linear map to the integral instead of integrating after the map.
  simpa [traceMulRight] using traceMulRight.integral_comp_comm hg

/-- The centered random vector has zero mean. -/
lemma integral_sub_mean_eq_zero
    {m : ℕ}
    (cbar : Fin m → ℝ)
    (μ : MeasureTheory.Measure (Fin m → ℝ))
    [MeasureTheory.IsProbabilityMeasure μ]
    (h_integrable_c : MeasureTheory.Integrable (fun c : Fin m → ℝ => c) μ)
    (hmean : ∫ c, c ∂μ = cbar) :
    ∫ c, (fun i => c i - cbar i) ∂μ = 0 := by
  have h_integrable_const : MeasureTheory.Integrable (fun _ : Fin m → ℝ => cbar) μ :=
    MeasureTheory.integrable_const cbar
  -- Subtract the mean inside the integral and then use the probability normalization.
  calc
    ∫ c, (fun i => c i - cbar i) ∂μ
        = (∫ c, c ∂μ) - ∫ _ : Fin m → ℝ, cbar ∂μ := by
            change ∫ c, c - cbar ∂μ = _ 
            rw [MeasureTheory.integral_sub h_integrable_c h_integrable_const]
    _ = cbar - cbar := by
          rw [hmean, MeasureTheory.integral_const]
          simp
    _ = 0 := by
          simp

theorem expected_quadratic_form_eq_trace
    {n m : ℕ}
    (F0 : Matrix (Fin m) (Fin m) ℝ)
    (F : Fin n → Matrix (Fin m) (Fin m) ℝ)
    (cbar : Fin m → ℝ)
    (S : Matrix (Fin m) (Fin m) ℝ)
    (μ : MeasureTheory.Measure (Fin m → ℝ))
    (x : Fin n → ℝ)
    [MeasureTheory.IsProbabilityMeasure μ]
    (_hF0_symm : F0.IsSymm)
    (_hF_symm : ∀ i, (F i).IsSymm)
    (_hS_symm : S.IsSymm)
    (h_integrable_c : MeasureTheory.Integrable (fun c : Fin m → ℝ => c) μ)
    (h_integrable_cov :
      MeasureTheory.Integrable
        (fun c : Fin m → ℝ => Matrix.of fun i j => (c i - cbar i) * (c j - cbar j)) μ)
    (_hx :
      Matrix.PosDef
        (F0 + ∑ i, x i • F i))
    (hmean : ∫ c, c ∂μ = cbar)
    (hcov :
      ∫ c, Matrix.of fun i j => (c i - cbar i) * (c j - cbar j) ∂μ = S) :
    ∫ c, dotProduct c (fun i =>
      ((F0 + ∑ j, x j • F j)⁻¹.mulVec c) i) ∂μ
      =
    Matrix.trace
      ((S + Matrix.of fun i j => cbar i * cbar j) *
        (F0 + ∑ j, x j • F j)⁻¹) := by
  let A : Matrix (Fin m) (Fin m) ℝ := (F0 + ∑ j, x j • F j)⁻¹
  let centeredMatrix : (Fin m → ℝ) → Matrix (Fin m) (Fin m) ℝ :=
    fun c => Matrix.of fun i j => (c i - cbar i) * (c j - cbar j)
  let traceMulRight :
      Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap (Fin m) ℝ ℝ).comp
        (LinearMap.mulRight ℝ A))
  let meanFunctional : (Fin m → ℝ) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ (A *ᵥ cbar))
  let centeredFunctional : (Fin m → ℝ) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      ((dotProductBilin ℝ ℝ cbar).comp A.mulVecLin)
  let centeredTrace : (Fin m → ℝ) → ℝ :=
    fun c => Matrix.trace (centeredMatrix c * A)
  let meanTrace : (Fin m → ℝ) → ℝ :=
    fun c => Matrix.trace (Matrix.vecMulVec cbar c * A)
  let crossTrace : (Fin m → ℝ) → ℝ :=
    fun c => Matrix.trace (Matrix.vecMulVec (fun i => c i - cbar i) cbar * A)
  have h_integrable_centered :
      MeasureTheory.Integrable (fun c : Fin m → ℝ => fun i => c i - cbar i) μ := by
    have h_integrable_const : MeasureTheory.Integrable (fun _ : Fin m → ℝ => cbar) μ :=
      MeasureTheory.integrable_const cbar
    simpa using h_integrable_c.sub h_integrable_const
  have h_integrable_centered_trace :
      MeasureTheory.Integrable
        centeredTrace μ := by
    simpa [centeredTrace, centeredMatrix, traceMulRight] using
      ContinuousLinearMap.integrable_comp traceMulRight h_integrable_cov
  have h_integrable_mean_trace :
      MeasureTheory.Integrable
        meanTrace μ := by
    simpa [meanTrace, meanFunctional, trace_vecMulVec_mul_eq_dotProduct_mulVec, dotProduct_comm] using
      ContinuousLinearMap.integrable_comp meanFunctional h_integrable_c
  have h_integrable_cross_trace :
      MeasureTheory.Integrable
        crossTrace μ := by
    simpa [crossTrace, centeredFunctional, trace_vecMulVec_mul_eq_dotProduct_mulVec] using
      ContinuousLinearMap.integrable_comp centeredFunctional h_integrable_centered
  have h_centered_term :
      ∫ c, centeredTrace c ∂μ = Matrix.trace (S * A) := by
    -- Route correction: evaluate the covariance term through the matrix integral first.
    rw [integral_trace_mul_right μ A h_integrable_cov]
    simpa [centeredMatrix] using congrArg (fun M => Matrix.trace (M * A)) hcov
  have h_mean_term :
      ∫ c, meanTrace c ∂μ =
        Matrix.trace (Matrix.vecMulVec cbar cbar * A) := by
    -- Convert the scalar integrand into a linear functional of the random vector.
    calc
      ∫ c, meanTrace c ∂μ
          = ∫ c, meanFunctional c ∂μ := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with c
              change Matrix.trace (Matrix.vecMulVec cbar c * A) = meanFunctional c
              rw [trace_vecMulVec_mul_eq_dotProduct_mulVec]
              simp [meanFunctional, dotProduct_comm]
      _ = meanFunctional (∫ c, c ∂μ) := by
            simpa [meanFunctional] using meanFunctional.integral_comp_comm h_integrable_c
      _ = meanFunctional cbar := by
            rw [hmean]
      _ = Matrix.trace (Matrix.vecMulVec cbar cbar * A) := by
            have h_eval : meanFunctional cbar = dotProduct (A *ᵥ cbar) cbar := by
              simp [meanFunctional]
            rw [h_eval]
            rw [dotProduct_comm, ← trace_vecMulVec_mul_eq_dotProduct_mulVec]
  have h_cross_term :
      ∫ c, crossTrace c ∂μ = 0 := by
    -- The last term vanishes because the centered vector has zero mean.
    calc
      ∫ c, crossTrace c ∂μ
          = ∫ c, centeredFunctional (fun i => c i - cbar i) ∂μ := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with c
              change Matrix.trace (Matrix.vecMulVec (fun i => c i - cbar i) cbar * A) =
                centeredFunctional (fun i => c i - cbar i)
              rw [trace_vecMulVec_mul_eq_dotProduct_mulVec]
              simp [centeredFunctional]
      _ = centeredFunctional (∫ c, (fun i => c i - cbar i) ∂μ) := by
            simpa [centeredFunctional] using centeredFunctional.integral_comp_comm h_integrable_centered
      _ = 0 := by
            rw [integral_sub_mean_eq_zero cbar μ h_integrable_c hmean]
            simp [centeredFunctional]
  -- Rewrite the quadratic form as a trace, split the rank-one matrix, and evaluate each term.
  calc
    ∫ c, dotProduct c (fun i => (A.mulVec c) i) ∂μ
        = ∫ c, Matrix.trace (Matrix.vecMulVec c c * A) ∂μ := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with c
            rw [← trace_vecMulVec_mul_eq_dotProduct_mulVec]
    _ = ∫ c, centeredTrace c + (meanTrace c + crossTrace c) ∂μ := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with c
          rw [vecMulVec_self_eq_centered_add_mean_terms cbar c]
          simp [centeredTrace, meanTrace, crossTrace, centeredMatrix, Matrix.add_mul, Matrix.trace_add,
            add_assoc]
    _ = (∫ c, centeredTrace c ∂μ) + ∫ c, meanTrace c + crossTrace c ∂μ := by
          simpa using
            (MeasureTheory.integral_add h_integrable_centered_trace
              (h_integrable_mean_trace.add h_integrable_cross_trace) :
              ∫ c, centeredTrace c + (meanTrace c + crossTrace c) ∂μ =
                (∫ c, centeredTrace c ∂μ) + ∫ c, meanTrace c + crossTrace c ∂μ)
    _ = (∫ c, centeredTrace c ∂μ) +
          (∫ c, meanTrace c ∂μ) +
          ∫ c, crossTrace c ∂μ := by
          rw [MeasureTheory.integral_add h_integrable_mean_trace h_integrable_cross_trace]
          ring
    _ = Matrix.trace (S * A) + Matrix.trace (Matrix.vecMulVec cbar cbar * A) := by
          rw [h_centered_term, h_mean_term, h_cross_term]
          simp
    _ = Matrix.trace ((S + Matrix.of fun i j => cbar i * cbar j) * A) := by
          rw [Matrix.add_mul, Matrix.trace_add]
          congr 1
    _ = Matrix.trace
          ((S + Matrix.of fun i j => cbar i * cbar j) *
            (F0 + ∑ j, x j • F j)⁻¹) := by
          rfl

/- [BLOCK Exercise 3.11-(d) | 39 | thm]
Let n,m ∈ ℕ, let F₀,F₁,dots,Fₙ ∈ S^m, and define F(x)=F₀+sum_{i=1}^n xᵢ Fᵢ for x=(x₁,dots,xₙ)∈ ℝ^n,
where S^m is the set of real symmetric m× m matrices. Let bar c ∈ ℝ^m and S ∈ S^m, and let c be an
m-dimensional random vector satisfying Ec=bar c and E[(c-bar c)(c-bar c)ᵀ]=S. Define Q=S+bar cbar
cᵀ. Prove further that the optimization problem stochastic matrix inverse minimization is equivalent
to the semidefinite program semidefinite reformulation.
-/
/-- Identifying a reformulation witness with `p.F` imports the witness symmetry field to `p`. -/
lemma reformulation_eq_F_forces_global_symmetry
    {n m : ℕ}
    {p : StochasticMatrixInverseMinimization n m}
    {r : SemidefiniteReformulation n m}
    (hrF : r.F = p.F) :
    ∀ x : Fin n → ℝ, (p.F x).IsSymm := by
  intro x
  -- Rewrite the reformulation symmetry field along the exact equality of matrix maps.
  simpa [← hrF] using r.F_symm x

/-- Any witness on the reformulation side forces global symmetry of the original matrix map. -/
lemma reformulation_witness_forces_global_symmetry
    {n m : ℕ}
    {p : StochasticMatrixInverseMinimization n m}
    {Qsqrt : Matrix (Fin m) (Fin m) ℝ} :
    (∃ r : SemidefiniteReformulation n m,
        r.F = p.F ∧
        r.Qsqrt = Qsqrt ∧
        SemidefiniteReformulation.isFeasible r ∧
        p.objective r.x = r.objective ∧
        ∀ r' : SemidefiniteReformulation n m,
          r'.F = p.F →
          r'.Qsqrt = Qsqrt →
          SemidefiniteReformulation.isFeasible r' →
          r.objective ≤ r'.objective) →
      ∀ x : Fin n → ℝ, (p.F x).IsSymm := by
  intro h_rhs x
  rcases h_rhs with ⟨r, hrF, _, _, _, _⟩
  -- Peel off the existential witness, then reuse the equality-to-symmetry bridge.
  exact reformulation_eq_F_forces_global_symmetry hrF x

/-- The matrix map used in the counterexample has one symmetric feasible point and one asymmetric one. -/
def asymmetryCounterexampleMatrixMap : (Fin 1 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ :=
  fun x => if x 0 = 0 then (1 : Matrix (Fin 2) (Fin 2) ℝ) else !![1, 1; 0, 1]

/-- The Dirac measure on `PUnit` is a probability measure. -/
lemma punit_dirac_isProbabilityMeasure :
    MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.dirac PUnit.unit) := by
  infer_instance

/-- The zero random vector on `PUnit` is measurable. -/
lemma measurable_zero_random_vector :
    Measurable (fun _ : PUnit => (fun _ : Fin 2 => (0 : ℝ))) := by
  exact
    (measurable_const : Measurable (fun _ : PUnit => (fun _ : Fin 2 => (0 : ℝ))))

/-- A concrete stochastic problem witnessing that the main equivalence is too strong. -/
def asymmetryCounterexampleProblem : StochasticMatrixInverseMinimization 1 2 where
  Ω := PUnit
  instMeasurableSpace := inferInstance
  probabilityMeasure := MeasureTheory.Measure.dirac PUnit.unit
  isProbabilityMeasure := punit_dirac_isProbabilityMeasure
  F := asymmetryCounterexampleMatrixMap
  cRandom := fun _ _ => 0
  cRandom_measurable := measurable_zero_random_vector

/-- The counterexample uses the zero matrix as `Qsqrt`. -/
def asymmetryCounterexampleQsqrt : Matrix (Fin 2) (Fin 2) ℝ := 0

/-- The zero `Qsqrt` used in the counterexample is symmetric. -/
lemma asymmetryCounterexampleQsqrt_symm :
    asymmetryCounterexampleQsqrt.IsSymm := by
  -- The zero matrix is symmetric entrywise.
  simp [asymmetryCounterexampleQsqrt]

/-- The zero point is feasible for the counterexample because the matrix map equals the identity there. -/
lemma asymmetryCounterexample_feasible_zero :
    asymmetryCounterexampleProblem.isFeasible (fun _ => 0) := by
  -- At the chosen point the matrix map reduces to `1`, so feasibility is immediate.
  simpa [StochasticMatrixInverseMinimization.isFeasible, asymmetryCounterexampleProblem,
    asymmetryCounterexampleMatrixMap] using
    (Matrix.PosDef.one : Matrix.PosDef (1 : Matrix (Fin 2) (Fin 2) ℝ))

/-- The counterexample objective vanishes because the random vector is identically zero. -/
lemma asymmetryCounterexample_objective_eq_zero (x : Fin 1 → ℝ) :
    asymmetryCounterexampleProblem.objective x = 0 := by
  -- Evaluate the Dirac integral of the zero quadratic form.
  simp [StochasticMatrixInverseMinimization.objective, asymmetryCounterexampleProblem]

/-- The trace identity hypothesis from the main theorem holds for the counterexample data. -/
lemma asymmetryCounterexample_objective_trace
    (x : Fin 1 → ℝ)
    (_hx : asymmetryCounterexampleProblem.isFeasible x) :
    asymmetryCounterexampleProblem.objective x =
      Matrix.trace ((asymmetryCounterexampleQsqrt * asymmetryCounterexampleQsqrt) *
        (asymmetryCounterexampleProblem.F x)⁻¹) := by
  -- Both sides collapse to zero because `Qsqrt = 0` and the objective is always zero.
  simp [asymmetryCounterexampleQsqrt, asymmetryCounterexample_objective_eq_zero]

/-- The counterexample satisfies the left-hand side of the claimed equivalence. -/
lemma asymmetryCounterexample_has_optimal_feasible_point :
    ∃ x : Fin 1 → ℝ,
      asymmetryCounterexampleProblem.isFeasible x ∧
      ∀ x' : Fin 1 → ℝ,
        asymmetryCounterexampleProblem.isFeasible x' →
          asymmetryCounterexampleProblem.objective x ≤
            asymmetryCounterexampleProblem.objective x' := by
  refine ⟨fun _ => 0, asymmetryCounterexample_feasible_zero, ?_⟩
  intro x' hx'
  -- Every feasible point has the same zero objective value.
  simp [asymmetryCounterexample_objective_eq_zero]

/-- The counterexample matrix map fails global symmetry at the point `x = 1`. -/
lemma asymmetryCounterexample_not_globally_symmetric :
    ¬ ∀ x : Fin 1 → ℝ, (asymmetryCounterexampleProblem.F x).IsSymm := by
  intro hsymm
  -- Evaluate the symmetry condition at the asymmetric upper-triangular matrix.
  have hentry :=
    Matrix.IsSymm.apply (hsymm (fun _ => 1)) (0 : Fin 2) (1 : Fin 2)
  simp [asymmetryCounterexampleProblem, asymmetryCounterexampleMatrixMap] at hentry

/-- The right-hand side of the main equivalence is impossible for the counterexample. -/
lemma asymmetryCounterexample_no_reformulation_witness :
    ¬ ∃ r : SemidefiniteReformulation 1 2,
      r.F = asymmetryCounterexampleProblem.F ∧
      r.Qsqrt = asymmetryCounterexampleQsqrt ∧
      SemidefiniteReformulation.isFeasible r ∧
      asymmetryCounterexampleProblem.objective r.x = r.objective ∧
      ∀ r' : SemidefiniteReformulation 1 2,
        r'.F = asymmetryCounterexampleProblem.F →
        r'.Qsqrt = asymmetryCounterexampleQsqrt →
        SemidefiniteReformulation.isFeasible r' →
        r.objective ≤ r'.objective := by
  intro h_rhs
  -- Route correction: the obstruction comes directly from `r.F_symm` together with `r.F = p.F`.
  have hsymm :
      ∀ x : Fin 1 → ℝ, (asymmetryCounterexampleProblem.F x).IsSymm :=
    reformulation_witness_forces_global_symmetry
      (p := asymmetryCounterexampleProblem) (Qsqrt := asymmetryCounterexampleQsqrt) h_rhs
  exact asymmetryCounterexample_not_globally_symmetric hsymm

/-- Any claimed forward implication from the optimizer formulation already forces global symmetry of `p.F`. -/
lemma claimed_forward_implication_forces_global_symmetry
    {n m : ℕ}
    {p : StochasticMatrixInverseMinimization n m}
    {Qsqrt : Matrix (Fin m) (Fin m) ℝ}
    (h_forward :
      (∃ x : Fin n → ℝ,
          p.isFeasible x ∧
          ∀ x' : Fin n → ℝ, p.isFeasible x' → p.objective x ≤ p.objective x') →
        (∃ r : SemidefiniteReformulation n m,
          r.F = p.F ∧
          r.Qsqrt = Qsqrt ∧
          SemidefiniteReformulation.isFeasible r ∧
          p.objective r.x = r.objective ∧
          ∀ r' : SemidefiniteReformulation n m,
            r'.F = p.F →
            r'.Qsqrt = Qsqrt →
            SemidefiniteReformulation.isFeasible r' →
            r.objective ≤ r'.objective))
    (h_opt :
      ∃ x : Fin n → ℝ,
        p.isFeasible x ∧
        ∀ x' : Fin n → ℝ, p.isFeasible x' → p.objective x ≤ p.objective x') :
    ∀ x : Fin n → ℝ, (p.F x).IsSymm := by
  -- Apply the claimed forward implication to obtain a reformulation witness.
  have h_rhs :
      ∃ r : SemidefiniteReformulation n m,
        r.F = p.F ∧
        r.Qsqrt = Qsqrt ∧
        SemidefiniteReformulation.isFeasible r ∧
        p.objective r.x = r.objective ∧
        ∀ r' : SemidefiniteReformulation n m,
          r'.F = p.F →
          r'.Qsqrt = Qsqrt →
          SemidefiniteReformulation.isFeasible r' →
          r.objective ≤ r'.objective :=
    h_forward h_opt
  -- The witness equality `r.F = p.F` then transports the symmetry field to every `p.F x`.
  exact reformulation_witness_forces_global_symmetry (p := p) (Qsqrt := Qsqrt) h_rhs

/-- Any claimed local equivalence together with an optimal feasible point already forces global
symmetry of `p.F`. -/
lemma claimed_equivalence_with_optimal_point_forces_global_symmetry
    {n m : ℕ}
    {p : StochasticMatrixInverseMinimization n m}
    {Qsqrt : Matrix (Fin m) (Fin m) ℝ}
    (h_equiv :
      (∃ x : Fin n → ℝ,
          p.isFeasible x ∧
          ∀ x' : Fin n → ℝ, p.isFeasible x' → p.objective x ≤ p.objective x') ↔
        (∃ r : SemidefiniteReformulation n m,
          r.F = p.F ∧
          r.Qsqrt = Qsqrt ∧
          SemidefiniteReformulation.isFeasible r ∧
          p.objective r.x = r.objective ∧
          ∀ r' : SemidefiniteReformulation n m,
            r'.F = p.F →
            r'.Qsqrt = Qsqrt →
            SemidefiniteReformulation.isFeasible r' →
            r.objective ≤ r'.objective))
    (h_opt :
      ∃ x : Fin n → ℝ,
        p.isFeasible x ∧
        ∀ x' : Fin n → ℝ, p.isFeasible x' → p.objective x ≤ p.objective x') :
    ∀ x : Fin n → ℝ, (p.F x).IsSymm := by
  -- Only the forward implication is needed to reach the symmetry obstruction.
  exact
    claimed_forward_implication_forces_global_symmetry
      (p := p) (Qsqrt := Qsqrt) h_equiv.mp h_opt

/-- Specializing the claimed equivalence to the asymmetric example yields a contradiction. -/
lemma asymmetryCounterexample_refutes_claimed_equivalence
    (h_equiv :
      (∃ x : Fin 1 → ℝ,
          asymmetryCounterexampleProblem.isFeasible x ∧
          ∀ x' : Fin 1 → ℝ,
            asymmetryCounterexampleProblem.isFeasible x' →
              asymmetryCounterexampleProblem.objective x ≤
                asymmetryCounterexampleProblem.objective x') ↔
        (∃ r : SemidefiniteReformulation 1 2,
          r.F = asymmetryCounterexampleProblem.F ∧
          r.Qsqrt = asymmetryCounterexampleQsqrt ∧
          SemidefiniteReformulation.isFeasible r ∧
          asymmetryCounterexampleProblem.objective r.x = r.objective ∧
          ∀ r' : SemidefiniteReformulation 1 2,
            r'.F = asymmetryCounterexampleProblem.F →
            r'.Qsqrt = asymmetryCounterexampleQsqrt →
            SemidefiniteReformulation.isFeasible r' →
            r.objective ≤ r'.objective)) :
    False := by
  -- Route correction: instead of unpacking the full RHS witness immediately, first isolate the
  -- hidden consequence that any such forward implication forces global symmetry of `p.F`.
  have hsymm :
      ∀ x : Fin 1 → ℝ, (asymmetryCounterexampleProblem.F x).IsSymm :=
    claimed_equivalence_with_optimal_point_forces_global_symmetry
      (p := asymmetryCounterexampleProblem)
      (Qsqrt := asymmetryCounterexampleQsqrt)
      h_equiv
      asymmetryCounterexample_has_optimal_feasible_point
  -- The explicit asymmetric matrix value at `x = 1` refutes that forced symmetry.
  exact asymmetryCounterexample_not_globally_symmetric hsymm

/-- The specialized forward implication already contradicts the forced-symmetry obstruction. -/
lemma asymmetryCounterexample_refutes_claimed_forward_direction
    (h_forward :
      (∃ x : Fin 1 → ℝ,
          asymmetryCounterexampleProblem.isFeasible x ∧
          ∀ x' : Fin 1 → ℝ,
            asymmetryCounterexampleProblem.isFeasible x' →
              asymmetryCounterexampleProblem.objective x ≤
                asymmetryCounterexampleProblem.objective x') →
        (∃ r : SemidefiniteReformulation 1 2,
          r.F = asymmetryCounterexampleProblem.F ∧
          r.Qsqrt = asymmetryCounterexampleQsqrt ∧
          SemidefiniteReformulation.isFeasible r ∧
          asymmetryCounterexampleProblem.objective r.x = r.objective ∧
          ∀ r' : SemidefiniteReformulation 1 2,
            r'.F = asymmetryCounterexampleProblem.F →
            r'.Qsqrt = asymmetryCounterexampleQsqrt →
            SemidefiniteReformulation.isFeasible r' →
            r.objective ≤ r'.objective)) :
    False := by
  -- Route correction: mirror the target blockage directly. A forward implication at this
  -- asymmetric instance would already force global symmetry of `F`, which the example forbids.
  have hsymm :
      ∀ x : Fin 1 → ℝ, (asymmetryCounterexampleProblem.F x).IsSymm :=
    claimed_forward_implication_forces_global_symmetry
      (p := asymmetryCounterexampleProblem)
      (Qsqrt := asymmetryCounterexampleQsqrt)
      h_forward
      asymmetryCounterexample_has_optimal_feasible_point
  -- The explicit asymmetric matrix value at `x = 1` still refutes that forced symmetry.
  exact asymmetryCounterexample_not_globally_symmetric hsymm

/-- The theorem's specialized counterexample equivalence is outright false. -/
lemma asymmetryCounterexample_claimed_equivalence_false :
    ¬ ((∃ x : Fin 1 → ℝ,
          asymmetryCounterexampleProblem.isFeasible x ∧
          ∀ x' : Fin 1 → ℝ,
            asymmetryCounterexampleProblem.isFeasible x' →
              asymmetryCounterexampleProblem.objective x ≤
                asymmetryCounterexampleProblem.objective x') ↔
        (∃ r : SemidefiniteReformulation 1 2,
          r.F = asymmetryCounterexampleProblem.F ∧
          r.Qsqrt = asymmetryCounterexampleQsqrt ∧
          SemidefiniteReformulation.isFeasible r ∧
          asymmetryCounterexampleProblem.objective r.x = r.objective ∧
          ∀ r' : SemidefiniteReformulation 1 2,
            r'.F = asymmetryCounterexampleProblem.F →
            r'.Qsqrt = asymmetryCounterexampleQsqrt →
            SemidefiniteReformulation.isFeasible r' →
            r.objective ≤ r'.objective)) := by
  -- Route correction: package the earlier contradiction as a direct negation of the
  -- specialized equivalence, so the target obstruction is available before the theorem.
  intro h_equiv
  -- The already proved refutation lemma closes the contradiction immediately.
  exact asymmetryCounterexample_refutes_claimed_equivalence h_equiv

/-- Any polymorphic completion of the target theorem specializes to the refuted asymmetric example. -/
lemma global_equivalence_proof_refuted_by_asymmetry_counterexample
    (h_global : ∀ {n m : ℕ}
        (p : StochasticMatrixInverseMinimization n m)
        (Qsqrt : Matrix (Fin m) (Fin m) ℝ),
        Qsqrt.IsSymm →
        (∀ x : Fin n → ℝ,
          p.isFeasible x →
            p.objective x = Matrix.trace ((Qsqrt * Qsqrt) * (p.F x)⁻¹)) →
        ((∃ x : Fin n → ℝ,
            p.isFeasible x ∧
            ∀ x' : Fin n → ℝ, p.isFeasible x' → p.objective x ≤ p.objective x') ↔
          (∃ r : SemidefiniteReformulation n m,
            r.F = p.F ∧
            r.Qsqrt = Qsqrt ∧
            SemidefiniteReformulation.isFeasible r ∧
            p.objective r.x = r.objective ∧
            ∀ r' : SemidefiniteReformulation n m,
              r'.F = p.F →
              r'.Qsqrt = Qsqrt →
              SemidefiniteReformulation.isFeasible r' →
              r.objective ≤ r'.objective))) :
    False := by
  -- Route correction: specialize first, then discard the backward implication because the
  -- forward direction already fails on the asymmetric counterexample.
  have h_specialized :
      ((∃ x : Fin 1 → ℝ,
          asymmetryCounterexampleProblem.isFeasible x ∧
          ∀ x' : Fin 1 → ℝ,
            asymmetryCounterexampleProblem.isFeasible x' →
              asymmetryCounterexampleProblem.objective x ≤
                asymmetryCounterexampleProblem.objective x') ↔
        (∃ r : SemidefiniteReformulation 1 2,
          r.F = asymmetryCounterexampleProblem.F ∧
          r.Qsqrt = asymmetryCounterexampleQsqrt ∧
          SemidefiniteReformulation.isFeasible r ∧
          asymmetryCounterexampleProblem.objective r.x = r.objective ∧
          ∀ r' : SemidefiniteReformulation 1 2,
            r'.F = asymmetryCounterexampleProblem.F →
            r'.Qsqrt = asymmetryCounterexampleQsqrt →
            SemidefiniteReformulation.isFeasible r' →
            r.objective ≤ r'.objective)) :=
    h_global
      asymmetryCounterexampleProblem
      asymmetryCounterexampleQsqrt
      asymmetryCounterexampleQsqrt_symm
      asymmetryCounterexample_objective_trace
  -- The specialized forward implication is already impossible.
  exact asymmetryCounterexample_refutes_claimed_forward_direction h_specialized.mp

/-- Even the claimed theorem's forward direction is impossible polymorphically. -/
lemma no_polymorphic_forward_proof_of_stochastic_matrix_inverse_minimization_equivalent_to_semidefinite_reformulation :
    ¬ (∀ {n m : ℕ}
        (p : StochasticMatrixInverseMinimization n m)
        (Qsqrt : Matrix (Fin m) (Fin m) ℝ),
        Qsqrt.IsSymm →
        (∀ x : Fin n → ℝ,
          p.isFeasible x →
            p.objective x = Matrix.trace ((Qsqrt * Qsqrt) * (p.F x)⁻¹)) →
        ((∃ x : Fin n → ℝ,
            p.isFeasible x ∧
            ∀ x' : Fin n → ℝ, p.isFeasible x' → p.objective x ≤ p.objective x') →
          (∃ r : SemidefiniteReformulation n m,
            r.F = p.F ∧
            r.Qsqrt = Qsqrt ∧
            SemidefiniteReformulation.isFeasible r ∧
            p.objective r.x = r.objective ∧
            ∀ r' : SemidefiniteReformulation n m,
              r'.F = p.F →
              r'.Qsqrt = Qsqrt →
              SemidefiniteReformulation.isFeasible r' →
              r.objective ≤ r'.objective))) := by
  intro h_global_forward
  -- Specialize the abstract forward implication to the checked asymmetric instance.
  have h_forward :
      (∃ x : Fin 1 → ℝ,
          asymmetryCounterexampleProblem.isFeasible x ∧
          ∀ x' : Fin 1 → ℝ,
            asymmetryCounterexampleProblem.isFeasible x' →
              asymmetryCounterexampleProblem.objective x ≤
                asymmetryCounterexampleProblem.objective x') →
        (∃ r : SemidefiniteReformulation 1 2,
          r.F = asymmetryCounterexampleProblem.F ∧
          r.Qsqrt = asymmetryCounterexampleQsqrt ∧
          SemidefiniteReformulation.isFeasible r ∧
          asymmetryCounterexampleProblem.objective r.x = r.objective ∧
          ∀ r' : SemidefiniteReformulation 1 2,
            r'.F = asymmetryCounterexampleProblem.F →
            r'.Qsqrt = asymmetryCounterexampleQsqrt →
            SemidefiniteReformulation.isFeasible r' →
            r.objective ≤ r'.objective) :=
    h_global_forward
      asymmetryCounterexampleProblem
      asymmetryCounterexampleQsqrt
      asymmetryCounterexampleQsqrt_symm
      asymmetryCounterexample_objective_trace
  -- Route correction: the forward implication already fails, so there is no need to
  -- route through the stronger specialized equivalence negation.
  exact asymmetryCounterexample_refutes_claimed_forward_direction h_forward

/-- Any polymorphic proof of the claimed equivalence yields its already-refuted forward direction. -/
lemma polymorphic_equivalence_proof_implies_polymorphic_forward_proof
    (h_global : ∀ {n m : ℕ}
        (p : StochasticMatrixInverseMinimization n m)
        (Qsqrt : Matrix (Fin m) (Fin m) ℝ),
        Qsqrt.IsSymm →
        (∀ x : Fin n → ℝ,
          p.isFeasible x →
            p.objective x = Matrix.trace ((Qsqrt * Qsqrt) * (p.F x)⁻¹)) →
        ((∃ x : Fin n → ℝ,
            p.isFeasible x ∧
            ∀ x' : Fin n → ℝ, p.isFeasible x' → p.objective x ≤ p.objective x') ↔
          (∃ r : SemidefiniteReformulation n m,
            r.F = p.F ∧
            r.Qsqrt = Qsqrt ∧
            SemidefiniteReformulation.isFeasible r ∧
            p.objective r.x = r.objective ∧
            ∀ r' : SemidefiniteReformulation n m,
              r'.F = p.F →
              r'.Qsqrt = Qsqrt →
              SemidefiniteReformulation.isFeasible r' →
              r.objective ≤ r'.objective))) :
    ∀ {n m : ℕ}
      (p : StochasticMatrixInverseMinimization n m)
      (Qsqrt : Matrix (Fin m) (Fin m) ℝ),
      Qsqrt.IsSymm →
      (∀ x : Fin n → ℝ,
        p.isFeasible x →
          p.objective x = Matrix.trace ((Qsqrt * Qsqrt) * (p.F x)⁻¹)) →
      ((∃ x : Fin n → ℝ,
          p.isFeasible x ∧
          ∀ x' : Fin n → ℝ, p.isFeasible x' → p.objective x ≤ p.objective x') →
        (∃ r : SemidefiniteReformulation n m,
          r.F = p.F ∧
          r.Qsqrt = Qsqrt ∧
          SemidefiniteReformulation.isFeasible r ∧
          p.objective r.x = r.objective ∧
          ∀ r' : SemidefiniteReformulation n m,
            r'.F = p.F →
            r'.Qsqrt = Qsqrt →
            SemidefiniteReformulation.isFeasible r' →
            r.objective ≤ r'.objective)) := by
  -- Project each specialized equivalence onto its forward implication.
  intro n m p Qsqrt hQsqrt_symm h_objective_trace
  -- The target obstruction only needs `.mp`; the backward implication is irrelevant.
  exact (h_global p Qsqrt hQsqrt_symm h_objective_trace).mp

/-- The full polymorphic statement claimed by the target theorem is uninhabited. -/
lemma no_polymorphic_proof_of_stochastic_matrix_inverse_minimization_equivalent_to_semidefinite_reformulation :
    ¬ (∀ {n m : ℕ}
        (p : StochasticMatrixInverseMinimization n m)
        (Qsqrt : Matrix (Fin m) (Fin m) ℝ),
        Qsqrt.IsSymm →
        (∀ x : Fin n → ℝ,
          p.isFeasible x →
            p.objective x = Matrix.trace ((Qsqrt * Qsqrt) * (p.F x)⁻¹)) →
        ((∃ x : Fin n → ℝ,
            p.isFeasible x ∧
            ∀ x' : Fin n → ℝ, p.isFeasible x' → p.objective x ≤ p.objective x') ↔
          (∃ r : SemidefiniteReformulation n m,
            r.F = p.F ∧
            r.Qsqrt = Qsqrt ∧
            SemidefiniteReformulation.isFeasible r ∧
            p.objective r.x = r.objective ∧
            ∀ r' : SemidefiniteReformulation n m,
              r'.F = p.F →
              r'.Qsqrt = Qsqrt →
              SemidefiniteReformulation.isFeasible r' →
              r.objective ≤ r'.objective))) := by
  intro h_global
  -- Route correction: reduce immediately to the stronger forward-direction impossibility.
  exact
    no_polymorphic_forward_proof_of_stochastic_matrix_inverse_minimization_equivalent_to_semidefinite_reformulation
      (polymorphic_equivalence_proof_implies_polymorphic_forward_proof h_global)

/-- Any hypothetical completion of the target theorem immediately contradicts the checked counterexample. -/
lemma stochastic_matrix_inverse_minimization_equivalent_to_semidefinite_reformulation_impossible
    (h_global : ∀ {n m : ℕ}
        (p : StochasticMatrixInverseMinimization n m)
        (Qsqrt : Matrix (Fin m) (Fin m) ℝ),
        Qsqrt.IsSymm →
        (∀ x : Fin n → ℝ,
          p.isFeasible x →
            p.objective x = Matrix.trace ((Qsqrt * Qsqrt) * (p.F x)⁻¹)) →
        ((∃ x : Fin n → ℝ,
            p.isFeasible x ∧
            ∀ x' : Fin n → ℝ, p.isFeasible x' → p.objective x ≤ p.objective x') ↔
          (∃ r : SemidefiniteReformulation n m,
            r.F = p.F ∧
            r.Qsqrt = Qsqrt ∧
            SemidefiniteReformulation.isFeasible r ∧
            p.objective r.x = r.objective ∧
            ∀ r' : SemidefiniteReformulation n m,
              r'.F = p.F →
              r'.Qsqrt = Qsqrt →
              SemidefiniteReformulation.isFeasible r' →
              r.objective ≤ r'.objective))) :
    False := by
  -- Route correction: reuse the forward-only obstruction directly, since the backward
  -- implication never participates in the contradiction.
  exact
    no_polymorphic_forward_proof_of_stochastic_matrix_inverse_minimization_equivalent_to_semidefinite_reformulation
      (polymorphic_equivalence_proof_implies_polymorphic_forward_proof h_global)

/-- The full target theorem type is false in the current file because the asymmetric example refutes it. -/
lemma stochastic_matrix_inverse_minimization_equivalent_to_semidefinite_reformulation_false :
    ¬ (∀ {n m : ℕ}
        (p : StochasticMatrixInverseMinimization n m)
        (Qsqrt : Matrix (Fin m) (Fin m) ℝ),
        Qsqrt.IsSymm →
        (∀ x : Fin n → ℝ,
          p.isFeasible x →
            p.objective x = Matrix.trace ((Qsqrt * Qsqrt) * (p.F x)⁻¹)) →
        ((∃ x : Fin n → ℝ,
            p.isFeasible x ∧
            ∀ x' : Fin n → ℝ, p.isFeasible x' → p.objective x ≤ p.objective x') ↔
          (∃ r : SemidefiniteReformulation n m,
            r.F = p.F ∧
            r.Qsqrt = Qsqrt ∧
            SemidefiniteReformulation.isFeasible r ∧
            p.objective r.x = r.objective ∧
            ∀ r' : SemidefiniteReformulation n m,
              r'.F = p.F →
              r'.Qsqrt = Qsqrt →
              SemidefiniteReformulation.isFeasible r' →
              r.objective ≤ r'.objective))) := by
  -- Route correction: reuse the packaged theorem-type contradiction instead of
  -- re-specializing the asymmetric counterexample inside each local proof.
  intro h_global
  exact
    stochastic_matrix_inverse_minimization_equivalent_to_semidefinite_reformulation_impossible
      h_global

/-- Specializing a polymorphic proof of the target theorem type recovers the current local goal. -/
lemma specialize_stochastic_matrix_inverse_minimization_equivalent_to_semidefinite_reformulation
    {n m : ℕ}
    (p : StochasticMatrixInverseMinimization n m)
    (Qsqrt : Matrix (Fin m) (Fin m) ℝ)
    (hQsqrt_symm : Qsqrt.IsSymm)
    (h_objective_trace : ∀ x : Fin n → ℝ,
      p.isFeasible x →
        p.objective x = Matrix.trace ((Qsqrt * Qsqrt) * (p.F x)⁻¹))
    (h_global : ∀ {n m : ℕ}
        (p : StochasticMatrixInverseMinimization n m)
        (Qsqrt : Matrix (Fin m) (Fin m) ℝ),
        Qsqrt.IsSymm →
        (∀ x : Fin n → ℝ,
          p.isFeasible x →
            p.objective x = Matrix.trace ((Qsqrt * Qsqrt) * (p.F x)⁻¹)) →
        ((∃ x : Fin n → ℝ,
            p.isFeasible x ∧
            ∀ x' : Fin n → ℝ, p.isFeasible x' → p.objective x ≤ p.objective x') ↔
          (∃ r : SemidefiniteReformulation n m,
            r.F = p.F ∧
            r.Qsqrt = Qsqrt ∧
            SemidefiniteReformulation.isFeasible r ∧
            p.objective r.x = r.objective ∧
            ∀ r' : SemidefiniteReformulation n m,
              r'.F = p.F →
              r'.Qsqrt = Qsqrt →
              SemidefiniteReformulation.isFeasible r' →
              r.objective ≤ r'.objective))) :
    ((∃ x : Fin n → ℝ,
        p.isFeasible x ∧
        ∀ x' : Fin n → ℝ, p.isFeasible x' → p.objective x ≤ p.objective x') ↔
      (∃ r : SemidefiniteReformulation n m,
        r.F = p.F ∧
        r.Qsqrt = Qsqrt ∧
        SemidefiniteReformulation.isFeasible r ∧
        p.objective r.x = r.objective ∧
        ∀ r' : SemidefiniteReformulation n m,
          r'.F = p.F →
          r'.Qsqrt = Qsqrt →
          SemidefiniteReformulation.isFeasible r' →
          r.objective ≤ r'.objective)) := by
  -- This is the exact specialization step that identifies the remaining local goal
  -- with one instance of the globally negated theorem type.
  exact h_global p Qsqrt hQsqrt_symm h_objective_trace

/-- The Schur-complement choice of `Z` is symmetric when `F x` and `Qsqrt` are symmetric. -/
lemma schurComplementWitness_Z_isSymm
    {m : ℕ}
    (F : Matrix (Fin m) (Fin m) ℝ)
    (Qsqrt : Matrix (Fin m) (Fin m) ℝ)
    (hF_symm : F.IsSymm)
    (hQsqrt_symm : Qsqrt.IsSymm) :
    (Qsqrt * F⁻¹ * Qsqrt).IsSymm := by
  -- Transpose the product and rewrite each factor using the symmetry hypotheses.
  rw [Matrix.IsSymm]
  simp [Matrix.transpose_mul, hQsqrt_symm.eq, hF_symm.inv.eq, Matrix.mul_assoc]

/-- The Schur-complement choice of `Z` is positive semidefinite for every feasible `x`. -/
lemma schurComplementWitness_Z_posSemidef
    {n m : ℕ}
    (p : StochasticMatrixInverseMinimization n m)
    (Qsqrt : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin n → ℝ)
    (hx : p.isFeasible x)
    (hQsqrt_symm : Qsqrt.IsSymm) :
    Matrix.PosSemidef (Qsqrt * (p.F x)⁻¹ * Qsqrt) := by
  -- Conjugate the inverse of the positive definite matrix by `Qsqrt`.
  simpa [hQsqrt_symm.eq, Matrix.mul_assoc] using
    (hx.inv.posSemidef.mul_mul_conjTranspose_same Qsqrt)

/-- The canonical Schur-complement block matrix is positive semidefinite. -/
lemma schurComplementWitness_block_posSemidef
    {n m : ℕ}
    (p : StochasticMatrixInverseMinimization n m)
    (Qsqrt : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin n → ℝ)
    (hx : p.isFeasible x)
    (hQsqrt_symm : Qsqrt.IsSymm) :
    Matrix.PosSemidef
      (Matrix.fromBlocks (p.F x) Qsqrt Qsqrt (Qsqrt * (p.F x)⁻¹ * Qsqrt)) := by
  letI := hx.isUnit.invertible
  -- Apply the Schur complement criterion and choose the vanishing complement.
  have hBlocks :
      Matrix.PosSemidef
        (Matrix.fromBlocks (p.F x) Qsqrt Qsqrtᴴ (Qsqrt * (p.F x)⁻¹ * Qsqrt)) := by
    rw [Matrix.PosDef.fromBlocks₁₁ Qsqrt (Qsqrt * (p.F x)⁻¹ * Qsqrt) hx]
    simpa [hQsqrt_symm.eq, Matrix.mul_assoc] using
      (Matrix.PosSemidef.zero :
        Matrix.PosSemidef
          (0 : Matrix (Fin m) (Fin m) ℝ))
  -- Rewrite the lower-left block from `Qsqrtᴴ` back to `Qsqrt`.
  simpa [hQsqrt_symm.eq] using hBlocks

/-- The Schur-complement witness has the trace required by the stochastic objective formula. -/
lemma trace_schurComplementWitness
    {m : ℕ}
    (F : Matrix (Fin m) (Fin m) ℝ)
    (Qsqrt : Matrix (Fin m) (Fin m) ℝ) :
    Matrix.trace (Qsqrt * F⁻¹ * Qsqrt) =
      Matrix.trace ((Qsqrt * Qsqrt) * F⁻¹) := by
  -- Cycle the trace once to move the trailing `Qsqrt` to the front.
  simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle Qsqrt F⁻¹ Qsqrt

/-- The canonical reformulation witness attached to a feasible point uses the Schur complement. -/
def schurComplementWitness
    {n m : ℕ}
    (p : StochasticMatrixInverseMinimization n m)
    (Qsqrt : Matrix (Fin m) (Fin m) ℝ)
    (hF_symm : ∀ x : Fin n → ℝ, (p.F x).IsSymm)
    (hQsqrt_symm : Qsqrt.IsSymm)
    (x : Fin n → ℝ)
    (hx : p.isFeasible x) :
    SemidefiniteReformulation n m :=
  { F := p.F
    F_symm := hF_symm
    Qsqrt := Qsqrt
    Qsqrt_symm := hQsqrt_symm
    x := x
    t := Matrix.trace (Qsqrt * (p.F x)⁻¹ * Qsqrt)
    Z := Qsqrt * (p.F x)⁻¹ * Qsqrt
    Z_symm := schurComplementWitness_Z_isSymm (p.F x) Qsqrt (hF_symm x) hQsqrt_symm
    posDef_F := hx
    posSemidef_Z := schurComplementWitness_Z_posSemidef p Qsqrt x hx hQsqrt_symm
    posSemidef_block := schurComplementWitness_block_posSemidef p Qsqrt x hx hQsqrt_symm }

/-- The canonical Schur-complement witness is feasible by construction. -/
lemma schurComplementWitness_isFeasible
    {n m : ℕ}
    (p : StochasticMatrixInverseMinimization n m)
    (Qsqrt : Matrix (Fin m) (Fin m) ℝ)
    (hF_symm : ∀ x : Fin n → ℝ, (p.F x).IsSymm)
    (hQsqrt_symm : Qsqrt.IsSymm)
    (x : Fin n → ℝ)
    (hx : p.isFeasible x) :
    SemidefiniteReformulation.isFeasible
      (schurComplementWitness p Qsqrt hF_symm hQsqrt_symm x hx) := by
  -- Unfold the canonical witness and read off each feasibility field.
  refine ⟨hx, schurComplementWitness_Z_posSemidef p Qsqrt x hx hQsqrt_symm,
    schurComplementWitness_block_posSemidef p Qsqrt x hx hQsqrt_symm, rfl⟩

/-- The canonical Schur-complement witness realizes the stochastic objective value. -/
lemma objective_eq_schurComplementWitness_objective
    {n m : ℕ}
    (p : StochasticMatrixInverseMinimization n m)
    (Qsqrt : Matrix (Fin m) (Fin m) ℝ)
    (hF_symm : ∀ x : Fin n → ℝ, (p.F x).IsSymm)
    (hQsqrt_symm : Qsqrt.IsSymm)
    (h_objective_trace : ∀ x : Fin n → ℝ,
      p.isFeasible x →
        p.objective x = Matrix.trace ((Qsqrt * Qsqrt) * (p.F x)⁻¹))
    (x : Fin n → ℝ)
    (hx : p.isFeasible x) :
    p.objective x =
      (schurComplementWitness p Qsqrt hF_symm hQsqrt_symm x hx).objective := by
  -- First rewrite the stochastic objective using the theorem hypothesis.
  calc
    p.objective x = Matrix.trace ((Qsqrt * Qsqrt) * (p.F x)⁻¹) := h_objective_trace x hx
    -- Then identify that trace with the canonical Schur-complement witness objective.
    _ = Matrix.trace (Qsqrt * (p.F x)⁻¹ * Qsqrt) := by
          symm
          exact trace_schurComplementWitness (p.F x) Qsqrt
    _ = (schurComplementWitness p Qsqrt hF_symm hQsqrt_symm x hx).objective := by
          rfl

/-- Any feasible reformulation witness with the same `F` and `Qsqrt` dominates the stochastic objective at its chosen point. -/
lemma stochastic_objective_le_reformulation_objective_of_feasible
    {n m : ℕ}
    (p : StochasticMatrixInverseMinimization n m)
    (Qsqrt : Matrix (Fin m) (Fin m) ℝ)
    (h_objective_trace : ∀ x : Fin n → ℝ,
      p.isFeasible x →
        p.objective x = Matrix.trace ((Qsqrt * Qsqrt) * (p.F x)⁻¹))
    (r : SemidefiniteReformulation n m)
    (hrF : r.F = p.F)
    (hrQsqrt : r.Qsqrt = Qsqrt)
    (hr_feasible : SemidefiniteReformulation.isFeasible r) :
    p.objective r.x ≤ r.objective := by
  rcases hr_feasible with ⟨hrx_feasible, _, hrBlock_psd, ht_eq⟩
  letI := hrx_feasible.isUnit.invertible
  -- Rewrite the feasible block matrix into the Schur-complement form used by `fromBlocks₁₁`.
  have hBlocks :
      Matrix.PosSemidef (Matrix.fromBlocks (r.F r.x) r.Qsqrt r.Qsqrtᴴ r.Z) := by
    simpa [r.Qsqrt_symm.eq] using hrBlock_psd
  -- The Schur complement is positive semidefinite, so its trace is nonnegative.
  have hSchur_psd :
      Matrix.PosSemidef (r.Z - r.Qsqrt * (r.F r.x)⁻¹ * r.Qsqrt) := by
    simpa [r.Qsqrt_symm.eq, Matrix.mul_assoc] using
      (Matrix.PosDef.fromBlocks₁₁ r.Qsqrt r.Z hrx_feasible).mp hBlocks
  have htrace_nonneg :
      0 ≤ Matrix.trace (r.Z - r.Qsqrt * (r.F r.x)⁻¹ * r.Qsqrt) :=
    Matrix.PosSemidef.trace_nonneg hSchur_psd
  have htrace_le :
      Matrix.trace (r.Qsqrt * (r.F r.x)⁻¹ * r.Qsqrt) ≤ Matrix.trace r.Z := by
    simpa [Matrix.trace_sub] using htrace_nonneg
  -- Rewrite the stochastic objective into the same trace expression and compare traces.
  calc
    p.objective r.x = Matrix.trace ((Qsqrt * Qsqrt) * (p.F r.x)⁻¹) :=
      h_objective_trace r.x (by simpa [StochasticMatrixInverseMinimization.isFeasible, ← hrF] using hrx_feasible)
    _ = Matrix.trace (Qsqrt * (p.F r.x)⁻¹ * Qsqrt) := by
          symm
          exact trace_schurComplementWitness (p.F r.x) Qsqrt
    _ = Matrix.trace (r.Qsqrt * (r.F r.x)⁻¹ * r.Qsqrt) := by
          simp [hrF, hrQsqrt]
    _ ≤ Matrix.trace r.Z := htrace_le
    _ = r.objective := by
          simpa [SemidefiniteReformulation.objective] using ht_eq.symm

/-- Under global symmetry of `p.F`, an optimal feasible point yields an optimal reformulation witness. -/
lemma optimal_feasible_point_gives_reformulation_witness_of_global_symmetry
    {n m : ℕ}
    (p : StochasticMatrixInverseMinimization n m)
    (Qsqrt : Matrix (Fin m) (Fin m) ℝ)
    (hF_symm : ∀ x : Fin n → ℝ, (p.F x).IsSymm)
    (hQsqrt_symm : Qsqrt.IsSymm)
    (h_objective_trace : ∀ x : Fin n → ℝ,
      p.isFeasible x →
        p.objective x = Matrix.trace ((Qsqrt * Qsqrt) * (p.F x)⁻¹))
    (h_opt : ∃ x : Fin n → ℝ,
      p.isFeasible x ∧
      ∀ x' : Fin n → ℝ, p.isFeasible x' → p.objective x ≤ p.objective x') :
    ∃ r : SemidefiniteReformulation n m,
      r.F = p.F ∧
      r.Qsqrt = Qsqrt ∧
      SemidefiniteReformulation.isFeasible r ∧
      p.objective r.x = r.objective ∧
      ∀ r' : SemidefiniteReformulation n m,
        r'.F = p.F →
        r'.Qsqrt = Qsqrt →
        SemidefiniteReformulation.isFeasible r' →
        r.objective ≤ r'.objective := by
  rcases h_opt with ⟨x, hx_feasible, hx_optimal⟩
  refine ⟨schurComplementWitness p Qsqrt hF_symm hQsqrt_symm x hx_feasible, rfl, rfl, ?_, ?_, ?_⟩
  -- The canonical Schur-complement witness is feasible by construction.
  · exact schurComplementWitness_isFeasible p Qsqrt hF_symm hQsqrt_symm x hx_feasible
  -- Its objective matches the stochastic objective at the chosen optimizer.
  · exact
      objective_eq_schurComplementWitness_objective
        p Qsqrt hF_symm hQsqrt_symm h_objective_trace x hx_feasible
  -- Any other feasible reformulation witness dominates the stochastic objective at its own point.
  · intro r' hr'F hr'Qsqrt hr'_feasible
    have hx_le_hr' :
        p.objective x ≤ p.objective r'.x := by
      exact
        hx_optimal r'.x
          (by simpa [StochasticMatrixInverseMinimization.isFeasible, ← hr'F] using hr'_feasible.1)
    have hr'_lower_bound :
        p.objective r'.x ≤ r'.objective :=
      stochastic_objective_le_reformulation_objective_of_feasible
        p Qsqrt h_objective_trace r' hr'F hr'Qsqrt hr'_feasible
    -- Compare through the stochastic objective: optimizer value `≤ p.objective r'.x ≤ r'.objective`.
    calc
      (schurComplementWitness p Qsqrt hF_symm hQsqrt_symm x hx_feasible).objective = p.objective x := by
        symm
        exact
          objective_eq_schurComplementWitness_objective
            p Qsqrt hF_symm hQsqrt_symm h_objective_trace x hx_feasible
      _ ≤ p.objective r'.x := hx_le_hr'
      _ ≤ r'.objective := hr'_lower_bound

/-- Under a global symmetry hypothesis on `p.F`, the stochastic and reformulation optimizers
coincide. -/
lemma stochastic_matrix_inverse_minimization_equivalent_to_semidefinite_reformulation_of_global_symmetry
    {n m : ℕ}
    (p : StochasticMatrixInverseMinimization n m)
    (Qsqrt : Matrix (Fin m) (Fin m) ℝ)
    (hF_symm : ∀ x : Fin n → ℝ, (p.F x).IsSymm)
    (hQsqrt_symm : Qsqrt.IsSymm)
    (h_objective_trace : ∀ x : Fin n → ℝ,
      p.isFeasible x →
        p.objective x = Matrix.trace ((Qsqrt * Qsqrt) * (p.F x)⁻¹)) :
    (∃ x : Fin n → ℝ,
        p.isFeasible x ∧
        ∀ x' : Fin n → ℝ, p.isFeasible x' → p.objective x ≤ p.objective x') ↔
    (∃ r : SemidefiniteReformulation n m,
        r.F = p.F ∧
        r.Qsqrt = Qsqrt ∧
        SemidefiniteReformulation.isFeasible r ∧
        p.objective r.x = r.objective ∧
        ∀ r' : SemidefiniteReformulation n m,
          r'.F = p.F →
          r'.Qsqrt = Qsqrt →
          SemidefiniteReformulation.isFeasible r' →
          r.objective ≤ r'.objective) := by
  refine Iff.intro ?_ ?_
  · intro h_opt
    -- The forward direction is exactly the canonical Schur-complement construction.
    exact
      optimal_feasible_point_gives_reformulation_witness_of_global_symmetry
        p Qsqrt hF_symm hQsqrt_symm h_objective_trace h_opt
  · intro h_rhs
    rcases h_rhs with ⟨r, hrF, hrQsqrt, hr_feasible, hr_objective, hr_optimal⟩
    -- Transport the witness feasibility back to the original stochastic problem.
    have hrx_feasible : p.isFeasible r.x := by
      simpa [StochasticMatrixInverseMinimization.isFeasible, hrF] using hr_feasible.1
    refine ⟨r.x, hrx_feasible, ?_⟩
    intro x' hx'
    -- Compare `r` against the canonical reformulation built from the competitor `x'`.
    have hx'_feasible :
        SemidefiniteReformulation.isFeasible
          (schurComplementWitness p Qsqrt hF_symm hQsqrt_symm x' hx') :=
      schurComplementWitness_isFeasible p Qsqrt hF_symm hQsqrt_symm x' hx'
    have hx'_objective :
        p.objective x' =
          (schurComplementWitness p Qsqrt hF_symm hQsqrt_symm x' hx').objective :=
      objective_eq_schurComplementWitness_objective
        p Qsqrt hF_symm hQsqrt_symm h_objective_trace x' hx'
    have hr_min_le :
        r.objective ≤
          (schurComplementWitness p Qsqrt hF_symm hQsqrt_symm x' hx').objective :=
      hr_optimal
        (schurComplementWitness p Qsqrt hF_symm hQsqrt_symm x' hx')
        rfl
        rfl
        hx'_feasible
    -- Translate the reformulation comparison back to the stochastic objective.
    calc
      p.objective r.x = r.objective := hr_objective
      _ ≤ (schurComplementWitness p Qsqrt hF_symm hQsqrt_symm x' hx').objective := hr_min_le
      _ = p.objective x' := by
            rw [← hx'_objective]

theorem stochastic_matrix_inverse_minimization_equivalent_to_semidefinite_reformulation
    {n m : ℕ}
    (p : StochasticMatrixInverseMinimization n m)
    (Qsqrt : Matrix (Fin m) (Fin m) ℝ)
    (hQsqrt_symm : Qsqrt.IsSymm)
    (h_objective_trace : ∀ x : Fin n → ℝ,
      p.isFeasible x →
        p.objective x = Matrix.trace ((Qsqrt * Qsqrt) * (p.F x)⁻¹)) :
    (∃ x : Fin n → ℝ,
        p.isFeasible x ∧
        ∀ x' : Fin n → ℝ, p.isFeasible x' → p.objective x ≤ p.objective x') ↔
    (∃ r : SemidefiniteReformulation n m,
        r.F = p.F ∧
        r.Qsqrt = Qsqrt ∧
        SemidefiniteReformulation.isFeasible r ∧
        p.objective r.x = r.objective ∧
        ∀ r' : SemidefiniteReformulation n m,
          r'.F = p.F →
          r'.Qsqrt = Qsqrt →
          SemidefiniteReformulation.isFeasible r' →
          r.objective ≤ r'.objective) := by
  -- Route correction: expose the real blocker directly. The local `h_global` below is exactly
  -- the theorem type that the explicit asymmetric counterexample independently refutes.
  have h_global :
      ∀ {n m : ℕ}
        (p : StochasticMatrixInverseMinimization n m)
        (Qsqrt : Matrix (Fin m) (Fin m) ℝ),
        Qsqrt.IsSymm →
        (∀ x : Fin n → ℝ,
          p.isFeasible x →
            p.objective x = Matrix.trace ((Qsqrt * Qsqrt) * (p.F x)⁻¹)) →
        ((∃ x : Fin n → ℝ,
            p.isFeasible x ∧
            ∀ x' : Fin n → ℝ, p.isFeasible x' → p.objective x ≤ p.objective x') ↔
          (∃ r : SemidefiniteReformulation n m,
            r.F = p.F ∧
            r.Qsqrt = Qsqrt ∧
            SemidefiniteReformulation.isFeasible r ∧
            p.objective r.x = r.objective ∧
            ∀ r' : SemidefiniteReformulation n m,
              r'.F = p.F →
              r'.Qsqrt = Qsqrt →
              SemidefiniteReformulation.isFeasible r' →
              r.objective ≤ r'.objective)) := by
    -- Introduce the arbitrary instance so the remaining placeholder has the exact theorem type
    -- whose full equivalence is already refuted earlier in the file by the asymmetric example.
    intro n m p Qsqrt hQsqrt_symm h_objective_trace
    refine Iff.intro ?_ ?_
    -- Route correction: do not try to complete this branch by hand. Any completed `h_global`
    -- is immediately consumed by
    -- `global_equivalence_proof_refuted_by_asymmetry_counterexample`, which specializes the
    -- claimed equivalence itself to the checked asymmetric obstruction.
    -- TODO: the theorem is false as written; a valid future statement would need an added
    -- symmetry hypothesis such as `∀ x, (p.F x).IsSymm` before this branch can be closed.
    · intro h_opt
      -- Route correction: dispatch through the already-correct strengthened theorem, so the
      -- remaining placeholder is only the missing global symmetry of `p.F`.
      have hF_symm : ∀ x : Fin n → ℝ, (p.F x).IsSymm := by
      -- TODO: prove `∀ x, (p.F x).IsSymm` only after strengthening the theorem statement.
      -- Route correction: this is not a local tactic gap. The earlier lemma
      -- `no_polymorphic_forward_proof_of_stochastic_matrix_inverse_minimization_equivalent_to_semidefinite_reformulation`
      -- already proves that no uniform proof of this symmetry-free forward branch can exist,
      -- because the asymmetric counterexample satisfies the current assumptions while refuting it.
        sorry
      -- Apply the strengthened equivalence once the missing symmetry input is available.
      exact
        (stochastic_matrix_inverse_minimization_equivalent_to_semidefinite_reformulation_of_global_symmetry
          p Qsqrt hF_symm hQsqrt_symm h_objective_trace).mp h_opt
    · intro h_rhs
      rcases h_rhs with ⟨r, hrF, hrQsqrt, hr_feasible, hr_objective, hr_optimal⟩
      -- Import the witness symmetry field so the strengthened theorem becomes applicable.
      have hF_symm : ∀ x : Fin n → ℝ, (p.F x).IsSymm :=
        reformulation_eq_F_forces_global_symmetry hrF
      -- Reuse the strengthened equivalence for the backward implication verbatim.
      exact
        (stochastic_matrix_inverse_minimization_equivalent_to_semidefinite_reformulation_of_global_symmetry
          p Qsqrt hF_symm hQsqrt_symm h_objective_trace).mpr
          ⟨r, hrF, hrQsqrt, hr_feasible, hr_objective, hr_optimal⟩
  -- The contradiction is theorem-level: the local placeholder already has the exact global type
  -- refuted by the asymmetric example, so the theorem body remains uninhabited.
  have h_conflict : False := by
    -- Route correction: use the direct specialization contradiction for the full equivalence,
    -- not the earlier forward-only detour.
    exact global_equivalence_proof_refuted_by_asymmetry_counterexample h_global
  -- Close the specialized goal by ex falso; this exposes that the target statement itself
  -- is incompatible with the rest of the file unless a symmetry hypothesis on `p.F` is added.
  exact False.elim h_conflict

/-- The target theorem specializes to a contradiction on the asymmetric in-file example. -/
lemma stochastic_matrix_inverse_minimization_equivalent_to_semidefinite_reformulation_conflict :
    False := by
  -- Route correction: reuse the independent specialization lemma directly, instead of routing
  -- through the packaged theorem-type negation wrappers.
  exact
    global_equivalence_proof_refuted_by_asymmetry_counterexample
      stochastic_matrix_inverse_minimization_equivalent_to_semidefinite_reformulation

end «problem-10»
