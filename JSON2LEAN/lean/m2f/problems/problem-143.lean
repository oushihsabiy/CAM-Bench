import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-143»

def l2Norm {K : ℕ} (u : Fin K → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin K, (u i) ^ 2)

/-
Let x ∈ ℝ^n be the decision variable. Let q ∈ ℝ^n, r ∈ ℝ, A ∈ ℝ^{m× n}, b ∈ ℝ^m, and let Pᵢ ∈ S_ +
^n
for i = 0, ..., K, where S_ + ^n denotes the set of symmetric positive semidefinite n× n matrices.
Define mathcal E = {P₀ + \sum_{i = 1}^K uᵢ Pᵢ | u = (u₁, ..., u_K)∈R^K, ‖u‖_2 ≤ 1}. Consider the
robust quadratic program minimize & sup_{P∈mathcal E}(frac12 xᵀ P x + qᵀ x + r); subject to
& Ax ≤ b, array where Ax ≤ b is interpreted componentwise.
-/
structure RobustQuadraticProgram (n m K : ℕ) where
  q : Fin n → ℝ
  r : ℝ
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  P0 : Matrix (Fin n) (Fin n) ℝ
  Pi : Fin K → Matrix (Fin n) (Fin n) ℝ
  P0_symm : P0.IsSymm
  P0_psd : ∀ x : Fin n → ℝ, 0 ≤ dotProduct x (P0.mulVec x)
  Pi_symm : ∀ i : Fin K, (Pi i).IsSymm
  Pi_psd : ∀ i : Fin K, ∀ x : Fin n → ℝ, 0 ≤ dotProduct x ((Pi i).mulVec x)

def RobustQuadraticProgram.uncertainMatrix
    {n m K : ℕ} (p : RobustQuadraticProgram n m K) (u : Fin K → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  p.P0 + ∑ i : Fin K, (u i) • p.Pi i

def RobustQuadraticProgram.uncertaintySet
    {n m K : ℕ} (p : RobustQuadraticProgram n m K) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  {P | ∃ u : Fin K → ℝ, l2Norm u ≤ 1 ∧ P = p.uncertainMatrix u}

def RobustQuadraticProgram.isFeasible
    {n m K : ℕ} (p : RobustQuadraticProgram n m K) (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin m, (p.A.mulVec x) i ≤ p.b i

def RobustQuadraticProgram.pointObjective
    {n m K : ℕ} (p : RobustQuadraticProgram n m K)
    (P : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * dotProduct x (P.mulVec x) + dotProduct p.q x + p.r

def RobustQuadraticProgram.robustObjective
    {n m K : ℕ} (p : RobustQuadraticProgram n m K) (x : Fin n → ℝ) : ℝ :=
  sSup {y : ℝ | ∃ P ∈ p.uncertaintySet, y = RobustQuadraticProgram.pointObjective p P x}

/-
minimize & frac12 xᵀ P₀ x + frac12(\sum_{i = 1}^K (xᵀ Pᵢ x)^2)^{1/2} + qᵀ x + r; subject to &
Ax ≤ b, array
-/
structure ConvexQuadraticReformulation (n m K : ℕ) where
  base : RobustQuadraticProgram n m K

def ConvexQuadraticReformulation.quadraticTerms
    {n m K : ℕ} (p : ConvexQuadraticReformulation n m K) (x : Fin n → ℝ) :
    Fin K → ℝ :=
  fun i => dotProduct x ((p.base.Pi i).mulVec x)

def ConvexQuadraticReformulation.isFeasible
    {n m K : ℕ} (p : ConvexQuadraticReformulation n m K) (x : Fin n → ℝ) : Prop :=
  RobustQuadraticProgram.isFeasible p.base x

def ConvexQuadraticReformulation.objective
    {n m K : ℕ} (p : ConvexQuadraticReformulation n m K) (x : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * dotProduct x (p.base.P0.mulVec x) +
    (1 / 2 : ℝ) * l2Norm (p.quadraticTerms x) +
    dotProduct p.base.q x + p.base.r

/-
minimize & frac12 xᵀ P₀ x + ‖y‖_2 + qᵀ x + r; subject to & frac12 xᵀ Pᵢ x ≤ yᵢ,
i = 1, ..., K,; & Ax ≤ b, array with variables x∈mathbf ℝ^n and y∈R^K.
-/
structure SecondOrderConeReformulation (n m K : ℕ) where
  base : RobustQuadraticProgram n m K

def SecondOrderConeReformulation.objective
    {n m K : ℕ} (p : SecondOrderConeReformulation n m K)
    (x : Fin n → ℝ) (y : Fin K → ℝ) : ℝ :=
  (1 / 2 : ℝ) * dotProduct x (p.base.P0.mulVec x) + l2Norm y + dotProduct p.base.q x + p.base.r

def SecondOrderConeReformulation.quadraticConstraint
    {n m K : ℕ} (p : SecondOrderConeReformulation n m K)
    (x : Fin n → ℝ) (y : Fin K → ℝ) (i : Fin K) : Prop :=
  (1 / 2 : ℝ) * dotProduct x ((p.base.Pi i).mulVec x) ≤ y i

def SecondOrderConeReformulation.isFeasible
    {n m K : ℕ} (p : SecondOrderConeReformulation n m K)
    (x : Fin n → ℝ) (y : Fin K → ℝ) : Prop :=
  (∀ i : Fin K, p.quadraticConstraint x y i) ∧
    RobustQuadraticProgram.isFeasible p.base x

def SecondOrderConeReformulation.canonicalY
    {n m K : ℕ} (p : SecondOrderConeReformulation n m K)
    (x : Fin n → ℝ) : Fin K → ℝ :=
  fun i => (1 / 2 : ℝ) * dotProduct x ((p.base.Pi i).mulVec x)

/-
Let x ∈ ℝ^n be the decision variable. Let q ∈ ℝ^n, r ∈ ℝ, A ∈ ℝ^{m× n}, b ∈ ℝ^m, and let Pᵢ ∈ S_ +
^n
for i = 0, ..., K, where S_ + ^n is the set of symmetric positive semidefinite n× n matrices. Define
mathcal E = {P₀ + \sum_{i = 1}^K uᵢ Pᵢ | u = (u₁, ..., u_K)∈R^K, ‖u‖_2 ≤ 1}. Consider the robust
quadratic program minimize & sup_{P∈mathcal E}(frac12 xᵀ P x + qᵀ x + r); subject to & Ax ≤
b, array where Ax ≤ b is componentwise. Prove that this problem is equivalent to the convex
optimization problem minimize & frac12 xᵀ P₀ x + frac12(\sum_{i = 1}^K (xᵀ Pᵢ
x)^2)^{1/2} + qᵀ x + r; subject to & Ax ≤ b, array
-/
/-- Squaring the custom `l2Norm` recovers the defining sum of squares. -/
lemma l2Norm_sq {K : ℕ} (a : Fin K → ℝ) :
    (l2Norm a) ^ 2 = ∑ i : Fin K, (a i) ^ 2 := by
  -- Unfold the definition and square the outer square root.
  rw [l2Norm, Real.sq_sqrt]
  positivity

/-- The custom `l2Norm` is always nonnegative. -/
lemma l2Norm_nonneg {K : ℕ} (a : Fin K → ℝ) : 0 ≤ l2Norm a := by
  -- The norm is a square root, so positivity closes the goal.
  rw [l2Norm]
  positivity

/-- Cauchy-Schwarz for the custom `l2Norm`. -/
lemma dotProduct_le_l2Norm_mul_l2Norm {K : ℕ} (u a : Fin K → ℝ) :
    dotProduct u a ≤ l2Norm u * l2Norm a := by
  -- This is exactly the finite-dimensional real Cauchy-Schwarz inequality.
  simpa [dotProduct, l2Norm] using Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ) u a

/-- Normalizing by `l2Norm` lands in the closed `l2` unit ball. -/
lemma normalized_l2Norm_le_one {K : ℕ} (a : Fin K → ℝ) :
    l2Norm (fun i => a i / l2Norm a) ≤ 1 := by
  -- Split into the zero-norm and nonzero-norm cases.
  by_cases ha0 : l2Norm a = 0
  · -- In the zero case, division by zero in `ℝ` makes the normalized vector vanish.
    have hsqrt : Real.sqrt (∑ i : Fin K, (a i) ^ 2) = 0 := by
      simpa [l2Norm] using ha0
    simp [l2Norm, hsqrt]
  · -- In the nonzero case, compute the squared norm of the normalized vector.
    have hu_sq : (l2Norm (fun i => a i / l2Norm a)) ^ 2 = 1 := by
      calc
        (l2Norm (fun i => a i / l2Norm a)) ^ 2
            = ∑ i : Fin K, ((a i / l2Norm a)) ^ 2 := by
                rw [l2Norm_sq]
        _ = ∑ i : Fin K, (a i) ^ 2 / (l2Norm a) ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              field_simp [ha0]
        _ = (∑ i : Fin K, (a i) ^ 2) / (l2Norm a) ^ 2 := by
              rw [Finset.sum_div]
        _ = (l2Norm a) ^ 2 / (l2Norm a) ^ 2 := by rw [← l2Norm_sq]
        _ = 1 := by
              field_simp [ha0]
    have hu_nonneg : 0 ≤ l2Norm (fun i => a i / l2Norm a) := l2Norm_nonneg _
    nlinarith

/-- The normalized vector attains the support value `l2Norm a`. -/
lemma normalized_dotProduct_eq_l2Norm {K : ℕ} (a : Fin K → ℝ) :
    dotProduct (fun i => a i / l2Norm a) a = l2Norm a := by
  -- Again split into the zero and nonzero cases for the denominator.
  by_cases ha0 : l2Norm a = 0
  · simp [dotProduct, ha0]
  · -- Rewrite the dot product as the sum of squared coordinates divided by `l2Norm a`.
    calc
      dotProduct (fun i => a i / l2Norm a) a = ∑ i : Fin K, (a i / l2Norm a) * a i := by
        simp [dotProduct]
      _ = ∑ i : Fin K, (a i)^2 / l2Norm a := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        field_simp [ha0]
      _ = (∑ i : Fin K, (a i)^2) / l2Norm a := by
        rw [Finset.sum_div]
      _ = (l2Norm a)^2 / l2Norm a := by rw [← l2Norm_sq]
      _ = l2Norm a := by
        field_simp [ha0]

/-- The support function of the closed `l2Norm` unit ball is the `l2Norm`. -/
lemma sSup_unit_ball_dotProduct_eq_l2Norm {K : ℕ} (a : Fin K → ℝ) :
    sSup {t : ℝ | ∃ u : Fin K → ℝ, l2Norm u ≤ 1 ∧ t = dotProduct u a} = l2Norm a := by
  let S : Set ℝ := {t : ℝ | ∃ u : Fin K → ℝ, l2Norm u ≤ 1 ∧ t = dotProduct u a}
  -- First record a simple element of the set so that `csSup_le` applies.
  have h_nonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨0, ?_, by simp [dotProduct]⟩
    simp [l2Norm]
  -- Cauchy-Schwarz bounds every element of the set by `l2Norm a`.
  have h_bdd : BddAbove S := by
    refine ⟨l2Norm a, ?_⟩
    intro t ht
    rcases ht with ⟨u, hu, rfl⟩
    have h_cs := dotProduct_le_l2Norm_mul_l2Norm u a
    have h_mul : l2Norm u * l2Norm a ≤ 1 * l2Norm a := by
      gcongr
      exact l2Norm_nonneg a
    simpa using h_cs.trans h_mul
  apply le_antisymm
  · -- The supremum cannot exceed the universal Cauchy-Schwarz upper bound.
    refine csSup_le h_nonempty ?_
    intro t ht
    rcases ht with ⟨u, hu, rfl⟩
    have h_cs := dotProduct_le_l2Norm_mul_l2Norm u a
    have h_mul : l2Norm u * l2Norm a ≤ 1 * l2Norm a := by
      gcongr
      exact l2Norm_nonneg a
    simpa using h_cs.trans h_mul
  · -- The normalized vector realizes the bound, so the supremum is exactly `l2Norm a`.
    refine le_csSup h_bdd ?_
    refine ⟨fun i => a i / l2Norm a, normalized_l2Norm_le_one a, ?_⟩
    exact (normalized_dotProduct_eq_l2Norm a).symm

/-- Expanding an uncertain matrix isolates the `u`-dependent support-function term. -/
lemma pointObjective_uncertainMatrix_eq
    {n m K : ℕ} (p : RobustQuadraticProgram n m K) (x : Fin n → ℝ) (u : Fin K → ℝ) :
    RobustQuadraticProgram.pointObjective p (p.uncertainMatrix u) x =
      ((1 / 2 : ℝ) * dotProduct x (p.P0.mulVec x) + dotProduct p.q x + p.r) +
        (1 / 2 : ℝ) *
          dotProduct u (({ base := p } : ConvexQuadraticReformulation n m K).quadraticTerms x) := by
  -- Unfold the matrix perturbation and distribute the quadratic form across the finite sum.
  unfold RobustQuadraticProgram.pointObjective RobustQuadraticProgram.uncertainMatrix
  unfold ConvexQuadraticReformulation.quadraticTerms
  rw [Matrix.add_mulVec, Matrix.sum_mulVec, dotProduct_add, dotProduct_sum]
  simp_rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, dotProduct]
  ring

/-- Adding a constant and the half-scaled support term preserves the `sSup` value. -/
lemma sSup_affine_unit_ball_dotProduct_eq
    {K : ℕ} (a : Fin K → ℝ) (c : ℝ) :
    sSup {t : ℝ | ∃ u : Fin K → ℝ, l2Norm u ≤ 1 ∧ t = c + (1 / 2 : ℝ) * dotProduct u a} =
      c + (1 / 2 : ℝ) * l2Norm a := by
  let S : Set ℝ := {t : ℝ | ∃ u : Fin K → ℝ, l2Norm u ≤ 1 ∧ t = c + (1 / 2 : ℝ) * dotProduct u a}
  -- The zero vector gives the base point `c`.
  have h_nonempty : S.Nonempty := by
    refine ⟨c, ?_⟩
    refine ⟨0, ?_, by simp [dotProduct]⟩
    simp [l2Norm]
  -- The same Cauchy-Schwarz estimate bounds every affine translate.
  have h_bdd : BddAbove S := by
    refine ⟨c + (1 / 2 : ℝ) * l2Norm a, ?_⟩
    intro t ht
    rcases ht with ⟨u, hu, rfl⟩
    have h_cs := dotProduct_le_l2Norm_mul_l2Norm u a
    have h_mul : dotProduct u a ≤ l2Norm a := by
      calc
        dotProduct u a ≤ l2Norm u * l2Norm a := h_cs
        _ ≤ 1 * l2Norm a := by
          gcongr
          exact l2Norm_nonneg a
        _ = l2Norm a := by ring
    linarith
  apply le_antisymm
  · -- The affine supremum inherits the same upper bound.
    refine csSup_le h_nonempty ?_
    intro t ht
    rcases ht with ⟨u, hu, rfl⟩
    have h_cs := dotProduct_le_l2Norm_mul_l2Norm u a
    have h_mul : dotProduct u a ≤ l2Norm a := by
      calc
        dotProduct u a ≤ l2Norm u * l2Norm a := h_cs
        _ ≤ 1 * l2Norm a := by
          gcongr
          exact l2Norm_nonneg a
        _ = l2Norm a := by ring
    linarith
  · -- The normalized witness still attains the supremum after adding the constant term.
    refine le_csSup h_bdd ?_
    refine ⟨fun i => a i / l2Norm a, normalized_l2Norm_le_one a, ?_⟩
    rw [normalized_dotProduct_eq_l2Norm]

theorem robust_quadratic_program_equiv_convex_reformulation
    {n m K : ℕ} (p : RobustQuadraticProgram n m K) :
    ∀ x : Fin n → ℝ,
      (RobustQuadraticProgram.isFeasible p x ↔
        ConvexQuadraticReformulation.isFeasible ({ base := p } : ConvexQuadraticReformulation n m K) x) ∧
      RobustQuadraticProgram.robustObjective p x =
        ConvexQuadraticReformulation.objective ({ base := p } : ConvexQuadraticReformulation n m K) x := by
  intro x
  constructor
  · -- The convex reformulation reuses exactly the original feasibility system.
    rfl
  · -- Route correction: compute the robust supremum directly as a support function over the `l2` unit ball.
    let pc : ConvexQuadraticReformulation n m K := { base := p }
    let c : ℝ := (1 / 2 : ℝ) * dotProduct x (p.P0.mulVec x) + dotProduct p.q x + p.r
    let a : Fin K → ℝ := pc.quadraticTerms x
    -- Re-express the robust objective set using the perturbation parameter `u`.
    have h_set_eq :
        {y : ℝ | ∃ P ∈ p.uncertaintySet, y = RobustQuadraticProgram.pointObjective p P x} =
          {t : ℝ | ∃ u : Fin K → ℝ, l2Norm u ≤ 1 ∧ t = c + (1 / 2 : ℝ) * dotProduct u a} := by
      ext t
      constructor
      · intro ht
        rcases ht with ⟨P, ⟨u, hu, rfl⟩, rfl⟩
        refine ⟨u, hu, ?_⟩
        simp [c, a, pc, pointObjective_uncertainMatrix_eq, add_assoc, add_comm]
      · intro ht
        rcases ht with ⟨u, hu, rfl⟩
        refine ⟨p.uncertainMatrix u, ?_, ?_⟩
        · exact ⟨u, hu, rfl⟩
        · simp [c, a, pc, pointObjective_uncertainMatrix_eq, add_assoc, add_comm]
    rw [RobustQuadraticProgram.robustObjective, h_set_eq, sSup_affine_unit_ball_dotProduct_eq]
    simp [ConvexQuadraticReformulation.objective, c, a, pc, add_assoc, add_comm]

/-
Let x ∈ ℝ^n be the decision variable. Let q ∈ ℝ^n, r ∈ ℝ, A ∈ ℝ^{m× n}, b ∈ ℝ^m, and let Pᵢ ∈ S_ +
^n
for i = 0, ..., K, where S_ + ^n is the set of symmetric positive semidefinite n× n matrices. Define
mathcal E = {P₀ + \sum_{i = 1}^K uᵢ Pᵢ | u = (u₁, ..., u_K)∈R^K, ‖u‖_2 ≤ 1}. Consider the robust
quadratic program minimize & sup_{P∈mathcal E}(frac12 xᵀ P x + qᵀ x + r); subject to & Ax ≤
b, array where Ax ≤ b is componentwise. Prove that this problem is also equivalent to minimize &
frac12 xᵀ P₀ x + ‖y‖_2 + qᵀ x + r; subject to & frac12 xᵀ Pᵢ x ≤ yᵢ, i = 1, ...,
K,; & Ax ≤ b, array with variables x∈mathbf ℝ^n and y∈R^K. In particular, prove that the
robust problem can be formulated as a second - order cone program.
-/
/-- Scaling every coordinate by `1 / 2` scales the custom `l2Norm` by `1 / 2`. -/
lemma l2Norm_half_mul {K : ℕ} (a : Fin K → ℝ) :
    l2Norm (fun i => (1 / 2 : ℝ) * a i) = (1 / 2 : ℝ) * l2Norm a := by
  -- Compare the two nonnegative quantities via their squares.
  have hsq :
      (l2Norm (fun i => (1 / 2 : ℝ) * a i)) ^ 2 = ((1 / 2 : ℝ) * l2Norm a) ^ 2 := by
    calc
      (l2Norm (fun i => (1 / 2 : ℝ) * a i)) ^ 2
          = ∑ i : Fin K, (((1 / 2 : ℝ) * a i) ^ 2) := by
              rw [l2Norm_sq]
      _ = ∑ i : Fin K, ((1 / 2 : ℝ) ^ 2 * (a i) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = (1 / 2 : ℝ) ^ 2 * ∑ i : Fin K, (a i) ^ 2 := by
            rw [Finset.mul_sum]
      _ = (1 / 2 : ℝ) ^ 2 * (l2Norm a) ^ 2 := by
            rw [← l2Norm_sq]
      _ = ((1 / 2 : ℝ) * l2Norm a) ^ 2 := by
            ring
  have hleft_nonneg : 0 ≤ l2Norm (fun i => (1 / 2 : ℝ) * a i) := l2Norm_nonneg _
  have hright_nonneg : 0 ≤ (1 / 2 : ℝ) * l2Norm a := by
    nlinarith [l2Norm_nonneg a]
  nlinarith

/-- The custom `l2Norm` is monotone on vectors with nonnegative coordinates. -/
lemma l2Norm_le_of_nonneg_le {K : ℕ} {a b : Fin K → ℝ}
    (ha_nonneg : ∀ i : Fin K, 0 ≤ a i) (hab : ∀ i : Fin K, a i ≤ b i) :
    l2Norm a ≤ l2Norm b := by
  -- Unfold the norm and compare the sums of squares termwise.
  rw [l2Norm, l2Norm]
  refine Real.sqrt_le_sqrt ?_
  refine Finset.sum_le_sum ?_
  intro i hi
  have hai : 0 ≤ a i := ha_nonneg i
  have hbi : 0 ≤ b i := le_trans hai (hab i)
  have hsq : a i * a i ≤ b i * b i := by
    exact mul_le_mul (hab i) (hab i) hai hbi
  simpa [pow_two] using hsq

/-- The canonical SOC slack reproduces the convex reformulation objective. -/
lemma objective_canonicalY_eq_convex_objective
    {n m K : ℕ} (p : RobustQuadraticProgram n m K) (x : Fin n → ℝ) :
    SecondOrderConeReformulation.objective
      ({ base := p } : SecondOrderConeReformulation n m K) x
      (SecondOrderConeReformulation.canonicalY
        ({ base := p } : SecondOrderConeReformulation n m K) x) =
    ConvexQuadraticReformulation.objective
      ({ base := p } : ConvexQuadraticReformulation n m K) x := by
  -- After unfolding, the only real work is the half-scaling identity for `l2Norm`.
  change
    (1 / 2 : ℝ) * dotProduct x (p.P0.mulVec x) +
        l2Norm (fun i : Fin K => (1 / 2 : ℝ) * dotProduct x ((p.Pi i).mulVec x)) +
        dotProduct p.q x + p.r
      =
    (1 / 2 : ℝ) * dotProduct x (p.P0.mulVec x) +
        (1 / 2 : ℝ) * l2Norm (fun i : Fin K => dotProduct x ((p.Pi i).mulVec x)) +
        dotProduct p.q x + p.r
  rw [l2Norm_half_mul]

/-- A feasible original point yields a feasible SOC point with the canonical slack. -/
lemma canonicalY_feasible_of_feasible
    {n m K : ℕ} (p : RobustQuadraticProgram n m K) (x : Fin n → ℝ)
    (hx : RobustQuadraticProgram.isFeasible p x) :
    SecondOrderConeReformulation.isFeasible
      ({ base := p } : SecondOrderConeReformulation n m K) x
      (SecondOrderConeReformulation.canonicalY
        ({ base := p } : SecondOrderConeReformulation n m K) x) := by
  constructor
  · -- The canonical slack saturates each quadratic inequality.
    intro i
    simp [SecondOrderConeReformulation.quadraticConstraint,
      SecondOrderConeReformulation.canonicalY]
  · -- The linear feasibility constraints are unchanged.
    exact hx

/-- Every feasible SOC slack has objective at least the canonical one. -/
lemma canonical_objective_le_of_feasible
    {n m K : ℕ} (p : RobustQuadraticProgram n m K) (x : Fin n → ℝ)
    {y : Fin K → ℝ}
    (hy : SecondOrderConeReformulation.isFeasible
      ({ base := p } : SecondOrderConeReformulation n m K) x y) :
    SecondOrderConeReformulation.objective
      ({ base := p } : SecondOrderConeReformulation n m K) x
      (SecondOrderConeReformulation.canonicalY
        ({ base := p } : SecondOrderConeReformulation n m K) x) ≤
    SecondOrderConeReformulation.objective
      ({ base := p } : SecondOrderConeReformulation n m K) x y := by
  let psoc : SecondOrderConeReformulation n m K := { base := p }
  -- The SOC inequalities say that every feasible slack dominates the canonical one.
  have hcan_le : ∀ i : Fin K, psoc.canonicalY x i ≤ y i := by
    intro i
    simpa [psoc, SecondOrderConeReformulation.canonicalY,
      SecondOrderConeReformulation.quadraticConstraint] using hy.1 i
  -- Positive semidefiniteness forces every canonical slack coordinate to be nonnegative.
  have hcan_nonneg : ∀ i : Fin K, 0 ≤ psoc.canonicalY x i := by
    intro i
    have hpsd : 0 ≤ dotProduct x ((p.Pi i).mulVec x) := p.Pi_psd i x
    simpa [psoc, SecondOrderConeReformulation.canonicalY] using
      (show 0 ≤ (1 / 2 : ℝ) * dotProduct x ((p.Pi i).mulVec x) by
        nlinarith)
  -- Monotonicity of `l2Norm` on the nonnegative orthant gives the objective comparison.
  have hnorm_le : l2Norm (psoc.canonicalY x) ≤ l2Norm y :=
    l2Norm_le_of_nonneg_le hcan_nonneg hcan_le
  have hobj :
      (1 / 2 : ℝ) * dotProduct x (p.P0.mulVec x) + l2Norm (psoc.canonicalY x) +
          dotProduct p.q x + p.r
        ≤
      (1 / 2 : ℝ) * dotProduct x (p.P0.mulVec x) + l2Norm y + dotProduct p.q x + p.r := by
    linarith
  simpa [psoc, SecondOrderConeReformulation.objective, add_assoc, add_left_comm, add_comm] using
    hobj

theorem robust_quadratic_program_equiv_second_order_cone_reformulation
    {n m K : ℕ} (p : RobustQuadraticProgram n m K) :
    ∀ x : Fin n → ℝ,
      (RobustQuadraticProgram.isFeasible p x ↔
        ∃ y : Fin K → ℝ,
          SecondOrderConeReformulation.isFeasible
            ({ base := p } : SecondOrderConeReformulation n m K) x y) ∧
      (RobustQuadraticProgram.isFeasible p x →
        SecondOrderConeReformulation.isFeasible
          ({ base := p } : SecondOrderConeReformulation n m K) x
          (SecondOrderConeReformulation.canonicalY
            ({ base := p } : SecondOrderConeReformulation n m K) x) ∧
        RobustQuadraticProgram.robustObjective p x =
          SecondOrderConeReformulation.objective
            ({ base := p } : SecondOrderConeReformulation n m K) x
            (SecondOrderConeReformulation.canonicalY
              ({ base := p } : SecondOrderConeReformulation n m K) x) ∧
        RobustQuadraticProgram.robustObjective p x =
          sInf {z : ℝ | ∃ y : Fin K → ℝ,
            SecondOrderConeReformulation.isFeasible
              ({ base := p } : SecondOrderConeReformulation n m K) x y ∧
            z =
              SecondOrderConeReformulation.objective
                ({ base := p } : SecondOrderConeReformulation n m K) x y}) := by
  intro x
  let pc : ConvexQuadraticReformulation n m K := { base := p }
  let psoc : SecondOrderConeReformulation n m K := { base := p }
  constructor
  · constructor
    · -- Use the canonical slack to pass from original feasibility to SOC feasibility.
      intro hx
      refine ⟨psoc.canonicalY x, ?_⟩
      simpa [psoc] using canonicalY_feasible_of_feasible p x hx
    · -- Forgetting the slack variables recovers the original feasibility system.
      intro hsoc
      rcases hsoc with ⟨y, hy⟩
      exact hy.2
  · intro hx
    -- First certify the canonical SOC point.
    have hcanonical_feasible : psoc.isFeasible x (psoc.canonicalY x) := by
      simpa [psoc] using canonicalY_feasible_of_feasible p x hx
    -- Then identify the canonical SOC objective with the already solved convex one.
    have hrobust_eq_convex :
        RobustQuadraticProgram.robustObjective p x = ConvexQuadraticReformulation.objective pc x :=
      (robust_quadratic_program_equiv_convex_reformulation p x).2
    have hconvex_eq_soc :
        ConvexQuadraticReformulation.objective pc x =
          SecondOrderConeReformulation.objective psoc x (psoc.canonicalY x) := by
      simpa [pc, psoc] using (objective_canonicalY_eq_convex_objective p x).symm
    have hrobust_eq_soc :
        RobustQuadraticProgram.robustObjective p x =
          SecondOrderConeReformulation.objective psoc x (psoc.canonicalY x) := by
      exact hrobust_eq_convex.trans hconvex_eq_soc
    let S : Set ℝ := {z : ℝ | ∃ y : Fin K → ℝ, psoc.isFeasible x y ∧ z = psoc.objective x y}
    -- The canonical objective value is feasible and is a lower bound for all feasible SOC values.
    have hnonempty : S.Nonempty := by
      refine ⟨psoc.objective x (psoc.canonicalY x), ?_⟩
      exact ⟨psoc.canonicalY x, hcanonical_feasible, rfl⟩
    have hlower : ∀ z ∈ S, psoc.objective x (psoc.canonicalY x) ≤ z := by
      intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      exact canonical_objective_le_of_feasible p x hy
    have hbddBelow : BddBelow S := by
      exact ⟨psoc.objective x (psoc.canonicalY x), hlower⟩
    have hsInf :
        sInf S = psoc.objective x (psoc.canonicalY x) := by
      -- The canonical value lies in `S`, so the infimum is squeezed from both sides.
      refine le_antisymm (csInf_le hbddBelow ?_) (le_csInf hnonempty hlower)
      exact ⟨psoc.canonicalY x, hcanonical_feasible, rfl⟩
    refine ⟨hcanonical_feasible, hrobust_eq_soc, ?_⟩
    -- Rewrite the infimum characterization back in the original statement's form.
    change RobustQuadraticProgram.robustObjective p x = sInf S
    calc
      RobustQuadraticProgram.robustObjective p x
          = SecondOrderConeReformulation.objective psoc x (psoc.canonicalY x) := hrobust_eq_soc
      _ = sInf S := hsInf.symm

end «problem-143»
