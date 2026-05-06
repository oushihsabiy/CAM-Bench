import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-179»

/- [BLOCK Exercise 16.15 | 18 | opt_prob]
Consider the problem
min_{x ∈ ℝ^n} q(x) = (1)/(2)xᵀ G x + xᵀ c
subject to
Ax = b,
where G ∈ ℝ^{n×n}, c ∈ ℝ^n, A ∈ ℝ^{m × n}, and b ∈ ℝ^m. Assume that A has full row rank, that there
exists at least one x ∈ ℝ^n such that Ax=b, and that Z ∈ ℝ^{n × (n-m)} has columns forming a basis
for the null space of A, so that
N(A)={d ∈ ℝ^n : Ad=0}={Zp : p ∈ ℝ^{n-m}}.
-/
structure EqualityConstrainedQuadraticProgram where
  n : ℕ
  m : ℕ
  G : Matrix (Fin n) (Fin n) ℝ
  c : Fin n → ℝ
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  Z : Matrix (Fin n) (Fin (n - m)) ℝ
  full_row_rank : Function.Surjective A.toLin'
  feasible : ∃ x : Fin n → ℝ, A.mulVec x = b
  nullspace_parametrization : ∀ d : Fin n → ℝ, A.mulVec d = 0 ↔ ∃ p : Fin (n - m) → ℝ, Z.mulVec p = d

def EqualityConstrainedQuadraticProgram.objective
    (P : EqualityConstrainedQuadraticProgram) (x : Fin P.n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * dotProduct x (P.G.mulVec x) + dotProduct x P.c

def EqualityConstrainedQuadraticProgram.isFeasible
    (P : EqualityConstrainedQuadraticProgram) (x : Fin P.n → ℝ) : Prop :=
  P.A.mulVec x = P.b

/-- A vector of the form `Z * p` is feasible for the homogeneous constraint, and the reduced
negative curvature inequality rewrites to the ambient quadratic form along that direction. -/
lemma EqualityConstrainedQuadraticProgram.negativeCurvatureDirection
    (P : EqualityConstrainedQuadraticProgram)
    {p : Fin (P.n - P.m) → ℝ}
    (hp :
      dotProduct p ((P.Z.transpose.mulVec) (P.G.mulVec (P.Z.mulVec p))) < 0) :
    P.A.mulVec (P.Z.mulVec p) = 0 ∧
      dotProduct (P.Z.mulVec p) (P.G.mulVec (P.Z.mulVec p)) < 0 := by
  constructor
  · -- The nullspace parametrization says every vector `Z * p` lies in `ker A`.
    exact (P.nullspace_parametrization (P.Z.mulVec p)).2 ⟨p, rfl⟩
  · -- Rewrite the reduced quadratic form back into ambient coordinates along `d = Z * p`.
    have hneg₁ :
        Matrix.vecMul p P.Z.transpose ⬝ᵥ (P.G.mulVec (P.Z.mulVec p)) < 0 := by
      simpa [Matrix.dotProduct_mulVec] using hp
    simpa [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose] using hneg₁

/-- Moving along a direction in the nullspace of `A` preserves feasibility for the equality
constraints. -/
lemma EqualityConstrainedQuadraticProgram.feasibleAlongNullspaceRay
    (P : EqualityConstrainedQuadraticProgram)
    {x d : Fin P.n → ℝ} {t : ℝ}
    (hx : P.isFeasible x)
    (hd : P.A.mulVec d = 0) :
    P.isFeasible (x + t • d) := by
  -- Expand the affine constraint and use that the direction is annihilated by `A`.
  unfold EqualityConstrainedQuadraticProgram.isFeasible at *
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, hx, hd]
  simp

/-- The quadratic objective along the affine ray `x + t d` is a scalar quadratic in `t`. -/
lemma EqualityConstrainedQuadraticProgram.objectiveAlongDirection
    (P : EqualityConstrainedQuadraticProgram)
    (x d : Fin P.n → ℝ) (t : ℝ) :
    P.objective (x + t • d) =
      P.objective x +
        t *
          ((1 / 2 : ℝ) * (dotProduct x (P.G.mulVec d) + dotProduct d (P.G.mulVec x)) +
            dotProduct d P.c) +
        (1 / 2 : ℝ) * t ^ 2 * dotProduct d (P.G.mulVec d) := by
  -- Expand the quadratic form and collect the constant, linear, and quadratic terms in `t`.
  unfold EqualityConstrainedQuadraticProgram.objective
  rw [Matrix.mulVec_add, Matrix.mulVec_smul]
  simp_rw [add_dotProduct, dotProduct_add, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring_nf

/-- A real quadratic with negative leading coefficient takes a negative value somewhere. -/
lemma exists_scalar_making_negative_quadratic
    (ℓ q : ℝ) (hq : q < 0) :
    ∃ t : ℝ, t * ℓ + (1 / 2 : ℝ) * t ^ 2 * q < 0 := by
  -- Choose an explicit positive step whose quadratic term dominates any linear contribution.
  let a : ℝ := |ℓ| + 1
  let t : ℝ := 2 * a / (-q)
  refine ⟨t, ?_⟩
  have hqneg : 0 < -q := by linarith
  have ha_pos : 0 < a := by
    -- The buffer `+ 1` ensures strict positivity.
    dsimp [a]
    positivity
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have hlin_le : t * ℓ ≤ t * |ℓ| := by
    -- The nonnegative step size lets us bound the linear term by its absolute-value version.
    exact mul_le_mul_of_nonneg_left (le_abs_self ℓ) ht_nonneg
  have habs_eq :
      t * |ℓ| + (1 / 2 : ℝ) * t ^ 2 * q = -2 * a / (-q) := by
    -- After substituting the explicit step, the upper bound collapses to a manifestly negative term.
    dsimp [t]
    field_simp [hqneg.ne']
    ring
  have hstrict_abs : t * |ℓ| + (1 / 2 : ℝ) * t ^ 2 * q < 0 := by
    rw [habs_eq]
    have hpos_rhs : 0 < 2 * a / (-q) := by
      positivity
    have hrewrite : -2 * a / (-q) = -(2 * a / (-q)) := by
      ring
    rw [hrewrite]
    linarith
  have hcompare : t * ℓ + (1 / 2 : ℝ) * t ^ 2 * q ≤
      t * |ℓ| + (1 / 2 : ℝ) * t ^ 2 * q := by
    linarith
  linarith

/- [BLOCK Exercise 16.15 | 19 | thm]
Consider the equality-constrained quadratic program. Prove that this optimization problem has no
finite solution if the matrix Zᵀ G Z has a negative eigenvalue.
-/
theorem EqualityConstrainedQuadraticProgram.no_finite_solution_of_exists_negative_direction
    (P : EqualityConstrainedQuadraticProgram)
    (hneg :
      ∃ p : Fin (P.n - P.m) → ℝ,
        dotProduct p ((P.Z.transpose.mulVec) (P.G.mulVec (P.Z.mulVec p))) < 0) :
    ∀ x : Fin P.n → ℝ, P.isFeasible x →
      ∃ y : Fin P.n → ℝ, P.isFeasible y ∧ P.objective y < P.objective x := by
  rcases hneg with ⟨p, hp⟩
  -- Extract a feasible nullspace direction with strictly negative quadratic curvature.
  have hdirection := P.negativeCurvatureDirection hp
  let d : Fin P.n → ℝ := P.Z.mulVec p
  have hd_null : P.A.mulVec d = 0 := by
    simpa [d] using hdirection.1
  have hd_neg : dotProduct d (P.G.mulVec d) < 0 := by
    simpa [d] using hdirection.2
  intro x hx
  -- Measure the linear coefficient of the objective restricted to the feasible ray `x + t d`.
  let ℓ : ℝ :=
    (1 / 2 : ℝ) * (dotProduct x (P.G.mulVec d) + dotProduct d (P.G.mulVec x)) +
      dotProduct d P.c
  obtain ⟨t, ht⟩ := exists_scalar_making_negative_quadratic ℓ
    (dotProduct d (P.G.mulVec d)) hd_neg
  let y : Fin P.n → ℝ := x + t • d
  have hy_feasible : P.isFeasible y := by
    -- The equality constraints are unchanged because `d` lies in the nullspace of `A`.
    simpa [y] using P.feasibleAlongNullspaceRay (x := x) (d := d) (t := t) hx hd_null
  have hobjective_eq :
      P.objective y =
        P.objective x +
          t * ℓ +
          (1 / 2 : ℝ) * t ^ 2 * dotProduct d (P.G.mulVec d) := by
    -- Route correction: instead of seeking a special stationarity relation, expand the objective
    -- directly along the feasible ray and keep both mixed terms because `G` need not be symmetric.
    simpa [y, ℓ] using P.objectiveAlongDirection x d t
  have hobjective_lt : P.objective y < P.objective x := by
    rw [hobjective_eq]
    linarith
  refine ⟨y, hy_feasible, hobjective_lt⟩

end «problem-179»
