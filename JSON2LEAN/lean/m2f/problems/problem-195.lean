import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-195»

/- [BLOCK chapter5 Ex.11 | 13 | opt_prob]
Let A∈S^n, i.e. A is an n× n real symmetric matrix. Consider the optimization problem on the
unit sphere
S^n-1={x∈ℝ^n:‖x‖_2=1}
given by
min_x∈ℝ^n x^→p A x quadsubject toquad ‖x‖_2=1.
On the unit sphere, x^→p A x is the Rayleigh quotient of A. Denote the smallest and largest
eigenvalues of A by λ_min and λ_max, respectively.
-/
structure RayleighQuotientMinimization (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  symmetric : A.IsSymm

def RayleighQuotientMinimization.feasibleSet {n : ℕ} (_P : RayleighQuotientMinimization n) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ‖x‖ = 1}

def RayleighQuotientMinimization.objective {n : ℕ} (P : RayleighQuotientMinimization n) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => dotProduct x (P.A.mulVec x)

def RayleighQuotientMinimization.isFeasible {n : ℕ} (P : RayleighQuotientMinimization n)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ P.feasibleSet

def RayleighQuotientMinimization.isMinimizer {n : ℕ} (P : RayleighQuotientMinimization n)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  P.isFeasible x ∧ ∀ y, P.isFeasible y → P.objective x ≤ P.objective y

def RayleighQuotientMinimization.isMaximizer {n : ℕ} (P : RayleighQuotientMinimization n)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  P.isFeasible x ∧ ∀ y, P.isFeasible y → P.objective y ≤ P.objective x

/-- A real symmetric matrix is Hermitian. -/
lemma isHermitian_of_isSymm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    A.IsHermitian := by
  -- Over `ℝ`, symmetry is exactly the conjugate-transpose identity.
  rw [Matrix.IsHermitian]
  ext i j
  simp [Matrix.conjTranspose, hA.eq]

/-- The quadratic objective is the self-adjoint quadratic form of the Euclidean operator. -/
lemma objective_eq_reApplyInnerSelf {n : ℕ} (P : RayleighQuotientMinimization n)
    (x : EuclideanSpace ℝ (Fin n)) :
    P.objective x =
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P.A).reApplyInnerSelf x := by
  -- Expand both sides until they become the same coordinate dot product.
  rw [RayleighQuotientMinimization.objective, ContinuousLinearMap.reApplyInnerSelf_apply,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp [Matrix.ofLp_toEuclideanCLM]

/-- The coordinate dot product of a vector with itself is its squared Euclidean norm. -/
lemma dotProduct_self_eq_norm_sq {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    x.ofLp ⬝ᵥ x.ofLp = ‖x‖ ^ 2 := by
  -- Rewrite the real inner product in coordinates and use the standard norm identity.
  have hinner := real_inner_self_eq_norm_sq x
  rw [EuclideanSpace.inner_eq_star_dotProduct] at hinner
  simpa using hinner

/-- On the unit sphere, the Rayleigh quotient is exactly the original quadratic objective. -/
lemma rayleighQuotient_eq_objective_of_norm_eq_one {n : ℕ} (P : RayleighQuotientMinimization n)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ = 1) :
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P.A).rayleighQuotient x = P.objective x := by
  -- The Rayleigh denominator is `1`, so only the quadratic form remains.
  rw [ContinuousLinearMap.rayleighQuotient, hx, one_pow, div_one]
  simpa using (objective_eq_reApplyInnerSelf P x).symm

/-- A unit eigenvector evaluates the quadratic objective to its eigenvalue. -/
lemma objective_eq_eigenvalue_of_unit_eigenvector {n : ℕ} (P : RayleighQuotientMinimization n)
    {μ : ℝ} {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ = 1)
    (hμ : Module.End.HasEigenvector P.A.toLin' μ x) :
    P.objective x = μ := by
  -- Translate the eigenvector equation to coordinates and then collapse the norm factor.
  have hxμ : P.A.mulVec x.ofLp = μ • x.ofLp := by
    simpa [Matrix.toLin'_apply] using hμ.apply_eq_smul
  rw [RayleighQuotientMinimization.objective, hxμ, dotProduct_smul,
    dotProduct_self_eq_norm_sq, hx]
  norm_num

/-- An eigenvector for the Euclidean operator view is also one for the raw matrix linear map. -/
lemma hasEigenvector_toLin'_of_toEuclideanLin {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {μ : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (h : Module.End.HasEigenvector A.toEuclideanLin μ x) :
    Module.End.HasEigenvector A.toLin' μ x := by
  rcases h with ⟨hx, hx0⟩
  refine ⟨?_, ?_⟩
  -- Apply `ofLp` to move from the Euclidean operator equation back to coordinates.
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  · simpa using congrArg WithLp.ofLp hx
  · simpa using hx0

/-- An eigenvalue for the Euclidean operator view is also one for the raw matrix linear map. -/
lemma hasEigenvalue_toLin'_of_toEuclideanLin {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {μ : ℝ} (h : Module.End.HasEigenvalue A.toEuclideanLin μ) :
    Module.End.HasEigenvalue A.toLin' μ := by
  -- Choose a Euclidean eigenvector and convert it back to the coordinate presentation.
  rcases h.exists_hasEigenvector with ⟨x, hx⟩
  exact Module.End.hasEigenvalue_of_hasEigenvector
    (hasEigenvector_toLin'_of_toEuclideanLin hx)

/-- An eigenvector for the bundled Euclidean continuous operator view is also one for the raw
matrix linear map. -/
lemma hasEigenvector_toLin'_of_toEuclideanCLM {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {μ : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (h : Module.End.HasEigenvector
      ((↑(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) μ x) :
    Module.End.HasEigenvector A.toLin' μ x := by
  rcases h with ⟨hx, hx0⟩
  refine ⟨?_, ?_⟩
  -- Apply `ofLp` to move from the bundled Euclidean operator equation back to coordinates.
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  · simpa using congrArg WithLp.ofLp hx
  · simpa using hx0

/-- The Rayleigh quotient of a nonzero eigenvector is its eigenvalue. -/
lemma rayleighQuotient_eq_eigenvalue_of_hasEigenvector {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {μ : ℝ} {x : Fin n → ℝ}
    (hx : x ≠ 0) (hμ : Module.End.HasEigenvector A.toLin' μ x) :
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A).rayleighQuotient (WithLp.toLp 2 x) = μ := by
  -- Expand the Rayleigh quotient and cancel the common squared norm of the eigenvector.
  have hxμ : A.mulVec x = μ • x := by
    simpa [Matrix.toLin'_apply] using hμ.apply_eq_smul
  have hxx :
      x ⬝ᵥ x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
    simpa using dotProduct_self_eq_norm_sq (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))
  have hnorm : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ≠ 0 := by
    simpa using hx
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp [hxμ, dotProduct_smul, hxx]
  field_simp [hnorm]

/-- The Rayleigh quotient of a continuous linear map is bounded below on nonzero vectors. -/
lemma bddBelow_range_rayleighQuotient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) :
    BddBelow (Set.range fun z : {z : E // z ≠ 0} => T.rayleighQuotient z) := by
  -- The norm bound on the Rayleigh quotient gives a uniform lower bound.
  refine ⟨-‖T‖, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact (abs_le.mp (T.rayleighQuotient_le_norm z)).1

/-- The Rayleigh quotient of a continuous linear map is bounded above on nonzero vectors. -/
lemma bddAbove_range_rayleighQuotient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) :
    BddAbove (Set.range fun z : {z : E // z ≠ 0} => T.rayleighQuotient z) := by
  -- The norm bound on the Rayleigh quotient gives a uniform upper bound.
  refine ⟨‖T‖, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact (abs_le.mp (T.rayleighQuotient_le_norm z)).2

/-- A global minimizer of the original problem is a minimizer of the Euclidean quadratic form on
the unit sphere. -/
lemma isMinOn_reApplyInnerSelf_of_isMinimizer {n : ℕ} (P : RayleighQuotientMinimization n)
    {x : EuclideanSpace ℝ (Fin n)} (hx : P.isMinimizer x) :
    IsMinOn
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P.A).reApplyInnerSelf
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) x := by
  rcases hx with ⟨hx_feas, hx_min⟩
  rw [isMinOn_iff]
  -- Rewrite the objective comparison in terms of the self-adjoint quadratic form.
  intro y hy
  rw [← objective_eq_reApplyInnerSelf P x, ← objective_eq_reApplyInnerSelf P y]
  exact hx_min y <| by
    simpa [RayleighQuotientMinimization.isFeasible, RayleighQuotientMinimization.feasibleSet]
      using hy

/-- A global maximizer of the original problem is a maximizer of the Euclidean quadratic form on
the unit sphere. -/
lemma isMaxOn_reApplyInnerSelf_of_isMaximizer {n : ℕ} (P : RayleighQuotientMinimization n)
    {x : EuclideanSpace ℝ (Fin n)} (hx : P.isMaximizer x) :
    IsMaxOn
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P.A).reApplyInnerSelf
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) x := by
  rcases hx with ⟨hx_feas, hx_max⟩
  rw [isMaxOn_iff]
  -- Rewrite the objective comparison in terms of the self-adjoint quadratic form.
  intro y hy
  rw [← objective_eq_reApplyInnerSelf P y, ← objective_eq_reApplyInnerSelf P x]
  exact hx_max y <| by
    simpa [RayleighQuotientMinimization.isFeasible, RayleighQuotientMinimization.feasibleSet]
      using hy

/- [BLOCK chapter5 Ex.11 | 14 | thm]
Let A ∈ S^n, that is, A is an n × n real symmetric matrix. Consider the constrained optimization
problem on the unit sphere S^{n-1} = {x ∈ ℝ^n : ‖x‖_2 = 1} given by min_{x ∈ ℝ^n} x^→p A x, s.t.
‖x‖_2 = 1. Here, x^→p A x is the value of the Rayleigh quotient of the matrix A on the unit sphere.
Denote the smallest and largest eigenvalues of A by λ_{min} and λ_{max}, respectively. Prove that
the set of global minimizers of Rayleigh quotient minimization is exactly the set of all unit
eigenvectors satisfying Ax = λ_{min} x, ‖x‖_2 = 1, and, under the same constraint, the set of global
maximizers of the function x^→p A x is exactly the set of all unit eigenvectors satisfying Ax =
λ_{max} x, ‖x‖_2 = 1.
-/
set_option maxHeartbeats 800000 in
theorem rayleigh_quotient_minimizers_and_maximizers_are_unit_extreme_eigenvectors
    (n : ℕ) (hn : 0 < n) (P : RayleighQuotientMinimization n) :
    ∃ lmin lmax : ℝ,
      (Module.End.HasEigenvalue P.A.toLin' lmin ∧
        ∀ ν : ℝ, Module.End.HasEigenvalue P.A.toLin' ν → lmin ≤ ν) ∧
      (Module.End.HasEigenvalue P.A.toLin' lmax ∧
        ∀ ν : ℝ, Module.End.HasEigenvalue P.A.toLin' ν → ν ≤ lmax) ∧
      (∀ x : EuclideanSpace ℝ (Fin n),
        P.isMinimizer x ↔ ‖x‖ = 1 ∧ Module.End.HasEigenvector P.A.toLin' lmin x) ∧
      (∀ x : EuclideanSpace ℝ (Fin n),
        P.isMaximizer x ↔ ‖x‖ = 1 ∧ Module.End.HasEigenvector P.A.toLin' lmax x) := by
  let Tlin : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := P.A.toEuclideanLin
  let T :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P.A
  -- Convert the matrix symmetry hypothesis into the symmetric/self-adjoint operator package.
  have hTlin : Tlin.IsSymmetric := by
    dsimp [Tlin]
    exact (Matrix.isHermitian_iff_isSymmetric (A := P.A)).mp (isHermitian_of_isSymm P.symmetric)
  have hT : IsSelfAdjoint T := by
    dsimp [T, Tlin] at *
    simpa [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using hTlin.isSelfAdjoint
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    let i : Fin n := ⟨0, hn⟩
    let v : Fin n → ℝ := fun j => if j = i then 1 else 0
    refine ⟨⟨WithLp.toLp 2 v, 0, ?_⟩⟩
    intro h
    have : v = 0 := by
      simpa using congrArg WithLp.ofLp h
    have hi0 : v i = 0 := by simpa using congrArg (fun f => f i) this
    simp [v] at hi0
  let lmin : ℝ := ⨅ x : {x : EuclideanSpace ℝ (Fin n) // x ≠ 0}, T.rayleighQuotient x
  let lmax : ℝ := ⨆ x : {x : EuclideanSpace ℝ (Fin n) // x ≠ 0}, T.rayleighQuotient x
  -- The extreme Rayleigh values are eigenvalues in finite dimension.
  have hlmin_eu : Module.End.HasEigenvalue Tlin lmin := by
    dsimp [lmin, Tlin, T]
    simpa using hTlin.hasEigenvalue_iInf_of_finiteDimensional
  have hlmax_eu : Module.End.HasEigenvalue Tlin lmax := by
    dsimp [lmax, Tlin, T]
    simpa using hTlin.hasEigenvalue_iSup_of_finiteDimensional
  have hlmin : Module.End.HasEigenvalue P.A.toLin' lmin :=
    hasEigenvalue_toLin'_of_toEuclideanLin hlmin_eu
  have hlmax : Module.End.HasEigenvalue P.A.toLin' lmax :=
    hasEigenvalue_toLin'_of_toEuclideanLin hlmax_eu
  refine ⟨lmin, lmax, ?_, ?_, ?_, ?_⟩
  · refine ⟨hlmin, ?_⟩
    intro ν hν
    -- Evaluate the infimum at an arbitrary eigenvector of eigenvalue `ν`.
    rcases hν.exists_hasEigenvector with ⟨x, hx⟩
    have hx_rq : T.rayleighQuotient (WithLp.toLp 2 x) = ν := by
      dsimp [T]
      exact rayleighQuotient_eq_eigenvalue_of_hasEigenvector hx.2 hx
    have hx0 : (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
      simpa using hx.2
    calc
      lmin ≤ T.rayleighQuotient (WithLp.toLp 2 x) := by
        dsimp [lmin]
        exact ciInf_le (bddBelow_range_rayleighQuotient T) ⟨WithLp.toLp 2 x, hx0⟩
      _ = ν := hx_rq
  · refine ⟨hlmax, ?_⟩
    intro ν hν
    -- Evaluate the supremum at an arbitrary eigenvector of eigenvalue `ν`.
    rcases hν.exists_hasEigenvector with ⟨x, hx⟩
    have hx_rq : T.rayleighQuotient (WithLp.toLp 2 x) = ν := by
      dsimp [T]
      exact rayleighQuotient_eq_eigenvalue_of_hasEigenvector hx.2 hx
    have hx0 : (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
      simpa using hx.2
    calc
      ν = T.rayleighQuotient (WithLp.toLp 2 x) := hx_rq.symm
      _ ≤ lmax := by
        dsimp [lmax]
        exact le_ciSup (bddAbove_range_rayleighQuotient T) ⟨WithLp.toLp 2 x, hx0⟩
  · intro x
    constructor
    · intro hx_min
      -- A minimizer on the sphere is an eigenvector for the minimal Rayleigh value.
      have hx_unit : ‖x‖ = 1 := by
        exact hx_min.1
      have hx0 : x ≠ 0 := by
        have hx_norm_ne : ‖x‖ ≠ 0 := by
          rw [hx_unit]
          norm_num
        exact fun hx_zero => hx_norm_ne (by rw [hx_zero, norm_zero])
      have hminOn := isMinOn_reApplyInnerSelf_of_isMinimizer P hx_min
      have hminOn' :
          IsMinOn T.reApplyInnerSelf (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) ‖x‖) x := by
        rw [isMinOn_iff] at hminOn ⊢
        intro y hy
        exact hminOn y (by simpa [hx_unit] using hy)
      have hx_eu' : Module.End.HasEigenvector ((↑T) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin n)) lmin x := by
        dsimp [lmin]
        exact hT.hasEigenvector_of_isMinOn hx0 hminOn'
      refine And.intro hx_unit ?_
      exact hasEigenvector_toLin'_of_toEuclideanCLM hx_eu'
    · rintro ⟨hx_unit, hx_eig⟩
      refine ⟨?_, ?_⟩
      · -- Unit eigenvectors are feasible.
        simpa [RayleighQuotientMinimization.isFeasible, RayleighQuotientMinimization.feasibleSet]
          using hx_unit
      · intro y hy
        -- Compare the objective with the global Rayleigh infimum on the sphere.
        have hy_unit : ‖y‖ = 1 := by
          simpa [RayleighQuotientMinimization.isFeasible, RayleighQuotientMinimization.feasibleSet]
            using hy
        have hy0 : y ≠ 0 := by
          have hy_norm_ne : ‖y‖ ≠ 0 := by
            rw [hy_unit]
            norm_num
          exact fun hy_zero => hy_norm_ne (by rw [hy_zero, norm_zero])
        have hx_obj : P.objective x = lmin :=
          objective_eq_eigenvalue_of_unit_eigenvector P hx_unit hx_eig
        have hy_rq : T.rayleighQuotient y = P.objective y :=
          rayleighQuotient_eq_objective_of_norm_eq_one P hy_unit
        rw [hx_obj, ← hy_rq]
        dsimp [lmin]
        exact ciInf_le (bddBelow_range_rayleighQuotient T) ⟨y, hy0⟩
  · intro x
    constructor
    · intro hx_max
      -- A maximizer on the sphere is an eigenvector for the maximal Rayleigh value.
      have hx_unit : ‖x‖ = 1 := by
        exact hx_max.1
      have hx0 : x ≠ 0 := by
        have hx_norm_ne : ‖x‖ ≠ 0 := by
          rw [hx_unit]
          norm_num
        exact fun hx_zero => hx_norm_ne (by rw [hx_zero, norm_zero])
      have hmaxOn := isMaxOn_reApplyInnerSelf_of_isMaximizer P hx_max
      have hmaxOn' :
          IsMaxOn T.reApplyInnerSelf (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) ‖x‖) x := by
        rw [isMaxOn_iff] at hmaxOn ⊢
        intro y hy
        exact hmaxOn y (by simpa [hx_unit] using hy)
      have hx_eu' : Module.End.HasEigenvector ((↑T) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin n)) lmax x := by
        dsimp [lmax]
        exact hT.hasEigenvector_of_isMaxOn hx0 hmaxOn'
      refine And.intro hx_unit ?_
      exact hasEigenvector_toLin'_of_toEuclideanCLM hx_eu'
    · rintro ⟨hx_unit, hx_eig⟩
      refine ⟨?_, ?_⟩
      · -- Unit eigenvectors are feasible.
        simpa [RayleighQuotientMinimization.isFeasible, RayleighQuotientMinimization.feasibleSet]
          using hx_unit
      · intro y hy
        -- Compare the objective with the global Rayleigh supremum on the sphere.
        have hy_unit : ‖y‖ = 1 := by
          simpa [RayleighQuotientMinimization.isFeasible, RayleighQuotientMinimization.feasibleSet]
            using hy
        have hy0 : y ≠ 0 := by
          have hy_norm_ne : ‖y‖ ≠ 0 := by
            rw [hy_unit]
            norm_num
          exact fun hy_zero => hy_norm_ne (by rw [hy_zero, norm_zero])
        have hy_rq : P.objective y = T.rayleighQuotient y :=
          (rayleighQuotient_eq_objective_of_norm_eq_one P hy_unit).symm
        have hx_obj : P.objective x = lmax :=
          objective_eq_eigenvalue_of_unit_eigenvector P hx_unit hx_eig
        rw [hy_rq, hx_obj]
        dsimp [lmax]
        exact le_ciSup (bddAbove_range_rayleighQuotient T) ⟨y, hy0⟩

/- [BLOCK chapter5 Ex.11 | 15 | thm]
Let A ∈ S^n, that is, A is an n × n real symmetric matrix. Consider the constrained optimization
problem on the unit sphere S^{n-1} = {x ∈ ℝ^n : ‖x‖_2 = 1} given by min_{x ∈ ℝ^n} x^→p A x, s.t.
‖x‖_2 = 1. Here, x^→p A x is the value of the Rayleigh quotient of the matrix A on the unit sphere.
Denote the smallest and largest eigenvalues of A by λ_{min} and λ_{max}, respectively. Let λ be an
eigenvalue of A. If λ is strictly minimal in the eigenvalue sequence, that is, it is an isolated
smallest eigenvalue (equivalently, there are no other eigenvalues smaller than it in some
neighborhood), prove that any unit eigenvector corresponding to λ is a strict local minimizer of
this constrained optimization problem; and explain that such points are in fact also global
minimizers.
-/
theorem isolated_smallest_eigenvalue_unit_eigenvector_is_strict_local_and_global_minimizer
    (n : ℕ) (hn : 0 < n) (P : RayleighQuotientMinimization n) (lam : ℝ)
    (hlam : Module.End.HasEigenvalue P.A.toLin' lam)
    (hiso : ∀ μ : ℝ, Module.End.HasEigenvalue P.A.toLin' μ → μ ≠ lam → lam < μ)
    (hsimple :
      ∀ x y : EuclideanSpace ℝ (Fin n),
        Module.End.HasEigenvector P.A.toLin' lam x →
        Module.End.HasEigenvector P.A.toLin' lam y →
        ∃ a : ℝ, y = a • x) :
    ∀ x : EuclideanSpace ℝ (Fin n),
      Module.End.HasEigenvector P.A.toLin' lam x ∧ ‖x‖ = 1 →
        (∃ r > 0, ∀ y : EuclideanSpace ℝ (Fin n),
          ‖y‖ = 1 → 0 < ‖y - x‖ → ‖y - x‖ < r → P.objective x < P.objective y) ∧
        P.isMinimizer x := by
  intro x hx
  rcases hx with ⟨hx_eig, hx_unit⟩
  -- First recover the extreme-eigenvalue characterization from the previous theorem.
  obtain ⟨lmin, lmax, hlmin_data, hlmax_data, hmins, _hmaxs⟩ :=
    rayleigh_quotient_minimizers_and_maximizers_are_unit_extreme_eigenvectors n hn P
  rcases hlmin_data with ⟨hlmin, hlmin_le⟩
  rcases hlmax_data with ⟨_hlmax, _hlmax_ge⟩
  have hlmin_eq_lam : lmin = lam := by
    -- The isolated minimal eigenvalue must coincide with the global minimum eigenvalue.
    by_contra hne
    have hlt : lam < lmin := hiso lmin hlmin (by simpa [eq_comm] using hne)
    have hle : lmin ≤ lam := hlmin_le lam hlam
    linarith
  have hx_min : P.isMinimizer x := by
    -- A unit eigenvector for the minimal eigenvalue is a global minimizer.
    exact (hmins x).2 ⟨hx_unit, by simpa [hlmin_eq_lam] using hx_eig⟩
  refine ⟨?_, hx_min⟩
  refine ⟨2, by norm_num, ?_⟩
  intro y hy_unit hy_ne hy_dist
  have hy_feas : P.isFeasible y := by
    simpa [RayleighQuotientMinimization.isFeasible, RayleighQuotientMinimization.feasibleSet]
      using hy_unit
  have hx_le_y : P.objective x ≤ P.objective y := hx_min.2 y hy_feas
  have hy_not_min : ¬ P.isMinimizer y := by
    intro hy_min
    have hy_lmin : Module.End.HasEigenvector P.A.toLin' lmin y := (hmins y).1 hy_min |>.2
    have hy_lam : Module.End.HasEigenvector P.A.toLin' lam y := by
      simpa [hlmin_eq_lam] using hy_lmin
    -- Simplicity of the eigenspace forces any other minimizer to be `x` or `-x`.
    obtain ⟨a, rfl⟩ := hsimple x y hx_eig hy_lam
    have ha_abs : |a| = 1 := by
      simpa [Real.norm_eq_abs, hx_unit, norm_smul] using hy_unit
    have ha_sq : a ^ 2 = 1 := by
      have hsquare := congrArg (fun t : ℝ => t ^ 2) ha_abs
      nlinarith [sq_abs a]
    have ha_cases : a = 1 ∨ a = -1 := by
      exact sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa using ha_sq)
    rcases ha_cases with ha | ha
    · have hy_ne' : 0 < ‖x - x‖ := by
        simpa [ha] using hy_ne
      have : False := by
        simpa using hy_ne'
      exact this.elim
    · have hdist_two : ‖((-1 : ℝ) • x) - x‖ = 2 := by
        calc
          ‖((-1 : ℝ) • x) - x‖ = ‖(-2 : ℝ) • x‖ := by simp [sub_eq_add_neg, two_smul]
          _ = |(-2 : ℝ)| * ‖x‖ := norm_smul _ _
          _ = 2 := by simp [hx_unit]
      have : ¬ ‖((-1 : ℝ) • x) - x‖ < 2 := by
        rw [hdist_two]
        norm_num
      exact this (by simpa [ha] using hy_dist)
  have hobj_ne : P.objective y ≠ P.objective x := by
    intro hEq
    have hy_min : P.isMinimizer y := by
      refine ⟨hy_feas, ?_⟩
      intro z hz
      calc
        P.objective y = P.objective x := hEq
        _ ≤ P.objective z := hx_min.2 z hz
    exact hy_not_min hy_min
  exact lt_of_le_of_ne hx_le_y hobj_ne.symm

end «problem-195»
