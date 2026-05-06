import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-148»
/-
The robust quadratic program minimize & sup_{P ∈ E} ((1)/(2) xᵀ P x + qᵀ x + r); ;
subject to & Ax preceq b array is exactly equivalent to the quadratic program minimize &
(1)/(2) xᵀ (P₀ + γ I) x + qᵀ x + r; ; subject to & Ax preceq b. array
-/
structure RobustQuadraticProgram
    (m : Type*)
    (n : Type*)
    [Fintype m]
    [DecidableEq m]
    [Fintype n]
    [DecidableEq n] where
  uncertaintySet : Set (Matrix n n ℝ)
  P0 : Matrix n n ℝ
  γ : ℝ
  q : n → ℝ
  r : ℝ
  A : Matrix m n ℝ
  b : m → ℝ

def RobustQuadraticProgram.feasible
    {m n : Type*}
    [Fintype m]
    [DecidableEq m]
    [Fintype n]
    [DecidableEq n]
    (p : RobustQuadraticProgram m n)
    (x : n → ℝ) : Prop :=
  ∀ i, (p.A.mulVec x) i ≤ p.b i

def RobustQuadraticProgram.quadraticValue
    {m n : Type*}
    [Fintype m]
    [DecidableEq m]
    [Fintype n]
    [DecidableEq n]
    (p : RobustQuadraticProgram m n)
    (P : Matrix n n ℝ)
    (x : n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * dotProduct x (P.mulVec x) + dotProduct p.q x + p.r

def RobustQuadraticProgram.robustObjective
    {m n : Type*}
    [Fintype m]
    [DecidableEq m]
    [Fintype n]
    [DecidableEq n]
    (p : RobustQuadraticProgram m n)
    (x : n → ℝ) : ℝ :=
  sSup ((fun P : Matrix n n ℝ => p.quadraticValue P x) '' p.uncertaintySet)

def RobustQuadraticProgram.equivalentObjective
    {m n : Type*}
    [Fintype m]
    [DecidableEq m]
    [Fintype n]
    [DecidableEq n]
    (p : RobustQuadraticProgram m n)
    (x : n → ℝ) : ℝ :=
  p.quadraticValue (p.P0 + p.γ • (1 : Matrix n n ℝ)) x

/-- The candidate residual saturates the uncertainty bound pointwise. -/
lemma candidate_residual_quadratic_form
    {m n : Type*}
    [Fintype m]
    [DecidableEq m]
    [Fintype n]
    [DecidableEq n]
    (p : RobustQuadraticProgram m n)
    (y : n → ℝ) :
    dotProduct y (((p.P0 + p.γ • (1 : Matrix n n ℝ) - p.P0).mulVec y)) =
      p.γ * dotProduct y y := by
  -- Expand the residual action; the `P0` terms cancel and the identity acts as the vector itself.
  simp [Matrix.smul_mulVec, dotProduct_smul]

/-- Rewriting `quadraticValue` around `P0` isolates the uncertain residual term. -/
lemma quadraticValue_eq_base_plus_residual
    {m n : Type*}
    [Fintype m]
    [DecidableEq m]
    [Fintype n]
    [DecidableEq n]
    (p : RobustQuadraticProgram m n)
    (P : Matrix n n ℝ)
    (y : n → ℝ) :
    p.quadraticValue P y =
      p.quadraticValue p.P0 y + (1 / 2 : ℝ) * dotProduct y ((P - p.P0).mulVec y) := by
  -- First rewrite `P` as `P0 + (P - P0)` at the matrix level.
  have hmat : p.P0 + (P - p.P0) = P := by
    ext i j
    simp [sub_eq_add_neg, add_left_comm]
  have hmul : p.P0.mulVec y + (P - p.P0).mulVec y = P.mulVec y := by
    rw [← Matrix.add_mulVec, hmat]
  -- Then distribute the dot product and collect the scalar terms.
  rw [RobustQuadraticProgram.quadraticValue, RobustQuadraticProgram.quadraticValue, ← hmul, dotProduct_add]
  ring

/-- The candidate matrix belongs to the uncertainty set. -/
lemma candidate_matrix_mem_uncertaintySet
    {m n : Type*}
    [Fintype m]
    [DecidableEq m]
    [Fintype n]
    [DecidableEq n]
    (p : RobustQuadraticProgram m n)
    [Nonempty n]
    (hP0symm : p.P0.IsSymm)
    (hγ : 0 ≤ p.γ)
    (hunc :
      p.uncertaintySet =
        {P : Matrix n n ℝ |
          P.IsSymm ∧
          ∀ y : n → ℝ,
            -p.γ * dotProduct y y ≤ dotProduct y ((P - p.P0).mulVec y) ∧
            dotProduct y ((P - p.P0).mulVec y) ≤ p.γ * dotProduct y y}) :
    p.P0 + p.γ • (1 : Matrix n n ℝ) ∈ p.uncertaintySet := by
  rw [hunc]
  constructor
  · -- Symmetry is preserved by adding the symmetric scalar multiple of the identity.
    exact hP0symm.add ((Matrix.isSymm_one).smul p.γ)
  · intro y
    -- The Euclidean square `dotProduct y y` is nonnegative over `ℝ`.
    have hy_nonneg : 0 ≤ dotProduct y y := by
      simpa using (dotProduct_star_self_nonneg y : 0 ≤ dotProduct y y)
    constructor
    · -- The lower uncertainty bound follows from `γ ≥ 0` and the explicit residual formula.
      rw [candidate_residual_quadratic_form]
      nlinarith
    · -- The upper uncertainty bound is attained with equality by the candidate.
      rw [candidate_residual_quadratic_form]

/-- Every admissible matrix is dominated by the candidate in quadratic value at a fixed vector. -/
lemma quadraticValue_le_candidate
    {m n : Type*}
    [Fintype m]
    [DecidableEq m]
    [Fintype n]
    [DecidableEq n]
    (p : RobustQuadraticProgram m n)
    [Nonempty n]
    (hunc :
      p.uncertaintySet =
        {P : Matrix n n ℝ |
          P.IsSymm ∧
          ∀ y : n → ℝ,
            -p.γ * dotProduct y y ≤ dotProduct y ((P - p.P0).mulVec y) ∧
            dotProduct y ((P - p.P0).mulVec y) ≤ p.γ * dotProduct y y})
    (x : n → ℝ)
    (P : Matrix n n ℝ)
    (hP : P ∈ p.uncertaintySet) :
    p.quadraticValue P x ≤ p.quadraticValue (p.P0 + p.γ • (1 : Matrix n n ℝ)) x := by
  rw [hunc] at hP
  rcases hP with ⟨_, hP_bounds⟩
  -- Use the uncertainty bound exactly at the vector `x`.
  have hbound : dotProduct x ((P - p.P0).mulVec x) ≤ p.γ * dotProduct x x := (hP_bounds x).2
  -- Rewrite both quadratic values into the same base term plus their residual contributions.
  rw [quadraticValue_eq_base_plus_residual p P x,
    quadraticValue_eq_base_plus_residual p (p.P0 + p.γ • (1 : Matrix n n ℝ)) x]
  rw [candidate_residual_quadratic_form]
  nlinarith

/-
Let x ∈ ℝ^n be the decision variable. Given q ∈ ℝ^n, r ∈ ℝ, A ∈ ℝ^{m \times n}, b ∈ ℝ^m, P₀ ∈ S_ +
^n,
and γ ≥ 0, consider the uncertainty set E = {P ∈ S^n | - γ I preceq P - P₀ preceq γ I}, where S^n is
the set of n \times n real symmetric matrices, S_ + ^n is the cone of symmetric positive
semidefinite
matrices, I is the n \times n identity matrix, and for symmetric matrices X preceq Y means Y - X ∈
S_ + ^n. The inequality Ax preceq b means a_iᵀ x ≤ bᵢ for i = 1, ..., m. Prove that for every x ∈
ℝ^n,
sup_{P ∈ E} (\frac{1}{2} xᵀ P x + qᵀ x + r ight) = \frac{1}{2} xᵀ (P₀ + γ I) x + qᵀ x + r.
-/
theorem robust_quadratic_objective_eq_equivalentObjective
    {m n : Type*}
    [Fintype m]
    [DecidableEq m]
    [Fintype n]
    [DecidableEq n]
    (p : RobustQuadraticProgram m n)
    [Nonempty n]
    (hP0symm : p.P0.IsSymm)
    (hP0psd : ∀ y : n → ℝ, 0 ≤ dotProduct y (p.P0.mulVec y))
    (hγ : 0 ≤ p.γ)
    (hunc :
      p.uncertaintySet =
        {P : Matrix n n ℝ |
          P.IsSymm ∧
          ∀ y : n → ℝ,
            -p.γ * dotProduct y y ≤ dotProduct y ((P - p.P0).mulVec y) ∧
            dotProduct y ((P - p.P0).mulVec y) ≤ p.γ * dotProduct y y})
    (x : n → ℝ) :
    p.robustObjective x = p.equivalentObjective x := by
  let Pstar : Matrix n n ℝ := p.P0 + p.γ • (1 : Matrix n n ℝ)
  have hPstar_mem : Pstar ∈ p.uncertaintySet := by
    simpa [Pstar] using candidate_matrix_mem_uncertaintySet p hP0symm hγ hunc
  have h_bdd : BddAbove ((fun P : Matrix n n ℝ => p.quadraticValue P x) '' p.uncertaintySet) := by
    -- The candidate value is a uniform upper bound on the image of the uncertainty set.
    refine ⟨p.quadraticValue Pstar x, ?_⟩
    intro z hz
    rcases hz with ⟨P, hP, rfl⟩
    simpa [Pstar] using quadraticValue_le_candidate p hunc x P hP
  rw [RobustQuadraticProgram.robustObjective, RobustQuadraticProgram.equivalentObjective]
  change sSup ((fun P : Matrix n n ℝ => p.quadraticValue P x) '' p.uncertaintySet) =
      p.quadraticValue Pstar x
  apply le_antisymm
  · -- The supremum cannot exceed the candidate value because every point in the image is bounded by it.
    apply csSup_le
    · exact ⟨p.quadraticValue Pstar x, Set.mem_image_of_mem _ hPstar_mem⟩
    · intro z hz
      rcases hz with ⟨P, hP, rfl⟩
      simpa [Pstar] using quadraticValue_le_candidate p hunc x P hP
  · -- The candidate itself lies in the image set, so its value is below the supremum.
    exact le_csSup h_bdd (Set.mem_image_of_mem _ hPstar_mem)

/-
Let x ∈ ℝ^n be the decision variable. Given q ∈ ℝ^n, r ∈ ℝ, A ∈ ℝ^{m \times n}, b ∈ ℝ^m, P₀ ∈ S_ +
^n,
and γ ≥ 0, consider the uncertainty set E = {P ∈ S^n | - γ I preceq P - P₀ preceq γ I}, where S^n is
the set of n \times n real symmetric matrices, S_ + ^n is the cone of symmetric positive
semidefinite
matrices, I is the n \times n identity matrix, and for symmetric matrices X preceq Y means Y - X ∈
S_ + ^n. The inequality Ax preceq b means a_iᵀ x ≤ bᵢ for i = 1, ..., m. Hence prove that robust
quadratic program so in particular it is a convex QP.
-/
theorem robust_quadratic_program_equivalent_on_feasible_set
    {m n : Type*}
    [Fintype m]
    [DecidableEq m]
    [Fintype n]
    [DecidableEq n]
    (p : RobustQuadraticProgram m n)
    [Nonempty n]
    (hP0symm : p.P0.IsSymm)
    (hP0psd : ∀ y : n → ℝ, 0 ≤ dotProduct y (p.P0.mulVec y))
    (hγ : 0 ≤ p.γ)
    (hunc :
      p.uncertaintySet =
        {P : Matrix n n ℝ |
          P.IsSymm ∧
          ∀ y : n → ℝ,
            -p.γ * dotProduct y y ≤ dotProduct y ((P - p.P0).mulVec y) ∧
            dotProduct y ((P - p.P0).mulVec y) ≤ p.γ * dotProduct y y}) :
    (∀ x : n → ℝ, p.feasible x → p.robustObjective x = p.equivalentObjective x) ∧
    (∀ y : n → ℝ,
      0 ≤ dotProduct y (((p.P0 + p.γ • (1 : Matrix n n ℝ)).mulVec y))) := by
  constructor
  · intro x _
    -- Feasibility does not affect the robust-objective identity, so reuse the first theorem directly.
    exact robust_quadratic_objective_eq_equivalentObjective p hP0symm hP0psd hγ hunc x
  · intro y
    -- The identity contribution is nonnegative because both `γ` and `dotProduct y y` are nonnegative.
    have hy_nonneg : 0 ≤ dotProduct y y := by
      simpa using (dotProduct_star_self_nonneg y : 0 ≤ dotProduct y y)
    have h_expand :
        dotProduct y (((p.P0 + p.γ • (1 : Matrix n n ℝ)).mulVec y)) =
          dotProduct y (p.P0.mulVec y) + p.γ * dotProduct y y := by
      -- Expand the candidate matrix action into the base quadratic form plus the identity contribution.
      simp [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul]
    rw [h_expand]
    nlinarith [hP0psd y, hγ, hy_nonneg]

end «problem-148»
