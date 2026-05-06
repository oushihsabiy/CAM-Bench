import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-89»

-- Exercise_2_10__b_

/-- The rank-one matrix `ggᵀ` is symmetric. -/
lemma rank_one_matrix_isSymm
    {n : Type*} [Fintype n] [DecidableEq n] (g : n → ℝ) :
    (Matrix.of fun i j => g i * g j).IsSymm := by
  -- The entries are symmetric because real multiplication is commutative.
  refine Matrix.IsSymm.ext ?_
  intro i j
  simp [mul_comm]

/-- Evaluating the rank-one quadratic form gives the square of the linear form. -/
lemma rank_one_quadratic_eval
    {n : Type*} [Fintype n] [DecidableEq n] (g x : n → ℝ) :
    x ⬝ᵥ (((Matrix.of fun i j => g i * g j) *ᵥ x)) = (g ⬝ᵥ x)^2 := by
  -- Rewrite the matrix as `ggᵀ`, then collapse the resulting matrix-vector product.
  have hgg :
      (Matrix.of fun i j => g i * g j) = Matrix.vecMulVec g g := by
    ext i j
    simp [Matrix.vecMulVec]
  rw [hgg, Matrix.vecMulVec_mulVec]
  simp [pow_two, dotProduct_comm]

/-- On the affine hyperplane, the original quadratic agrees with the shifted PSD quadratic. -/
lemma quadratic_eqOn_shifted_hyperplane
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (b g : n → ℝ) (c h lam : ℝ) :
    Set.EqOn
      (fun x => x ⬝ᵥ (A *ᵥ x) + b ⬝ᵥ x + c)
      (fun x =>
        x ⬝ᵥ (((A + lam • Matrix.of fun i j => g i * g j) *ᵥ x)) + b ⬝ᵥ x + (c - lam * h ^ 2))
      {x : n → ℝ | g ⬝ᵥ x + h = 0} := by
  intro x hx
  -- The hyperplane equation turns the rank-one correction into the constant `lam * h^2`.
  have hgx : g ⬝ᵥ x = -h := by
    exact eq_neg_of_add_eq_zero_left hx
  have hrank : x ⬝ᵥ (((Matrix.of fun i j => g i * g j) *ᵥ x)) = h ^ 2 := by
    rw [rank_one_quadratic_eval, hgx]
    ring
  change x ⬝ᵥ (A *ᵥ x) + b ⬝ᵥ x + c =
      x ⬝ᵥ (((A + lam • Matrix.of fun i j => g i * g j) *ᵥ x)) + b ⬝ᵥ x + (c - lam * h ^ 2)
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, hrank, smul_eq_mul]
  ring

/-- A symmetric matrix has equal mixed quadratic cross terms. -/
lemma symmetric_cross_term_swap
    {n : Type*} [Fintype n] [DecidableEq n]
    {B : Matrix n n ℝ} (hB : B.IsSymm) (x y : n → ℝ) :
    x ⬝ᵥ (B *ᵥ y) = y ⬝ᵥ (B *ᵥ x) := by
  -- Move one copy of `B` across the dot product using the transpose.
  calc
    x ⬝ᵥ (B *ᵥ y) = x ᵥ* B ⬝ᵥ y := by rw [Matrix.dotProduct_mulVec]
    _ = (Bᵀ *ᵥ x) ⬝ᵥ y := by rw [Matrix.mulVec_transpose]
    _ = y ⬝ᵥ (Bᵀ *ᵥ x) := by rw [dotProduct_comm]
    _ = y ⬝ᵥ (B *ᵥ x) := by rw [hB.eq]

/-- A PSD quadratic plus an affine term satisfies the convexity inequality for convex combinations. -/
lemma shifted_quadratic_le
    {n : Type*} [Fintype n] [DecidableEq n]
    {B : Matrix n n ℝ} (hB : B.IsSymm)
    (hB_nonneg : ∀ x : n → ℝ, 0 ≤ x ⬝ᵥ (B *ᵥ x))
    (d : n → ℝ) (k : ℝ)
    {x y : n → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • x + b • y) ⬝ᵥ (B *ᵥ (a • x + b • y)) + d ⬝ᵥ (a • x + b • y) + k
      ≤ a * (x ⬝ᵥ (B *ᵥ x) + d ⬝ᵥ x + k) + b * (y ⬝ᵥ (B *ᵥ y) + d ⬝ᵥ y + k) := by
  -- Expand the quadratic term at the convex combination.
  have hcross : x ⬝ᵥ (B *ᵥ y) = y ⬝ᵥ (B *ᵥ x) := symmetric_cross_term_swap hB x y
  have hcombo :
      (a • x + b • y) ⬝ᵥ (B *ᵥ (a • x + b • y))
        = a ^ 2 * (x ⬝ᵥ (B *ᵥ x))
          + a * b * (x ⬝ᵥ (B *ᵥ y))
          + b * a * (y ⬝ᵥ (B *ᵥ x))
          + b ^ 2 * (y ⬝ᵥ (B *ᵥ y)) := by
    calc
      (a • x + b • y) ⬝ᵥ (B *ᵥ (a • x + b • y))
          = (a • x + b • y) ⬝ᵥ (a • (B *ᵥ x) + b • (B *ᵥ y)) := by
              rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
      _ = (a • x) ⬝ᵥ (a • (B *ᵥ x) + b • (B *ᵥ y))
            + (b • y) ⬝ᵥ (a • (B *ᵥ x) + b • (B *ᵥ y)) := by
              rw [add_dotProduct]
      _ = (a • x ⬝ᵥ a • (B *ᵥ x) + a • x ⬝ᵥ b • (B *ᵥ y))
            + ((b • y) ⬝ᵥ a • (B *ᵥ x) + (b • y) ⬝ᵥ b • (B *ᵥ y)) := by
              rw [dotProduct_add, dotProduct_add]
      _ = a ^ 2 * (x ⬝ᵥ (B *ᵥ x))
            + a * b * (x ⬝ᵥ (B *ᵥ y))
            + b * a * (y ⬝ᵥ (B *ᵥ x))
            + b ^ 2 * (y ⬝ᵥ (B *ᵥ y)) := by
              simp [smul_dotProduct, dotProduct_smul, smul_eq_mul, pow_two]
              ring
  -- Expand the quadratic remainder for `x - y`.
  have hdiff :
      (x - y) ⬝ᵥ (B *ᵥ (x - y))
        = (x ⬝ᵥ (B *ᵥ x))
          - (x ⬝ᵥ (B *ᵥ y))
          - (y ⬝ᵥ (B *ᵥ x))
          + (y ⬝ᵥ (B *ᵥ y)) := by
    calc
      (x - y) ⬝ᵥ (B *ᵥ (x - y)) = (x - y) ⬝ᵥ (B *ᵥ x - B *ᵥ y) := by
        rw [Matrix.mulVec_sub]
      _ = x ⬝ᵥ (B *ᵥ x - B *ᵥ y) - y ⬝ᵥ (B *ᵥ x - B *ᵥ y) := by
        rw [sub_dotProduct]
      _ = (x ⬝ᵥ (B *ᵥ x) - x ⬝ᵥ (B *ᵥ y)) - (y ⬝ᵥ (B *ᵥ x) - y ⬝ᵥ (B *ᵥ y)) := by
        rw [dotProduct_sub, dotProduct_sub]
      _ = (x ⬝ᵥ (B *ᵥ x))
            - (x ⬝ᵥ (B *ᵥ y))
            - (y ⬝ᵥ (B *ᵥ x))
            + (y ⬝ᵥ (B *ᵥ y)) := by
              ring
  -- The linear term is exactly affine in the convex combination.
  have hlin :
      d ⬝ᵥ (a • x + b • y) = a * (d ⬝ᵥ x) + b * (d ⬝ᵥ y) := by
    simp [dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hnonneg : 0 ≤ (x - y) ⬝ᵥ (B *ᵥ (x - y)) := hB_nonneg (x - y)
  rw [hcross] at hcombo hdiff
  have hrem : 0 ≤ a * b * ((x - y) ⬝ᵥ (B *ᵥ (x - y))) := by
    exact mul_nonneg (mul_nonneg ha hb) hnonneg
  have hmain :
      a * (x ⬝ᵥ (B *ᵥ x) + d ⬝ᵥ x + k) + b * (y ⬝ᵥ (B *ᵥ y) + d ⬝ᵥ y + k)
        - ((a • x + b • y) ⬝ᵥ (B *ᵥ (a • x + b • y)) + d ⬝ᵥ (a • x + b • y) + k)
        = a * b * ((x - y) ⬝ᵥ (B *ᵥ (x - y))) := by
    rw [hcombo, hdiff, hlin]
    have hb1 : b = 1 - a := by linarith
    rw [hb1]
    ring
  linarith

/- [BLOCK Exercise 2.10-(b) | 5 | thm]
Let C be the quadratic sublevel set {x ∈ ℝ^n | xᵀ A x + bᵀ x + c ≤ 0}, and let H be the affine
hyperplane {x ∈ ℝ^n | gᵀ x + h = 0}, with g ≠ 0. Assume there exists λ ∈ ℝ such that A + λ g gᵀ is
positive semidefinite. Prove that C ∩ H is convex.
-/
theorem quadratic_sublevel_inter_affine_hyperplane_convex
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (b g : n → ℝ) (c h : ℝ)
    (hA_symm : A.IsSymm)
    (hg : g ≠ 0)
    (hlam : ∃ lam : ℝ,
      ∀ x : n → ℝ,
        0 ≤ x ⬝ᵥ (((A + lam • Matrix.of fun i j => g i * g j) *ᵥ x))) :
    Convex ℝ
      ({x : n → ℝ |
          x ⬝ᵥ (A *ᵥ x) + b ⬝ᵥ x + c ≤ 0} ∩
        {x : n → ℝ | g ⬝ᵥ x + h = 0}) := by
  rcases hlam with ⟨lam, hlam⟩
  let B : Matrix n n ℝ := A + lam • Matrix.of (fun i j => g i * g j)
  let q : (n → ℝ) → ℝ := fun x => x ⬝ᵥ (A *ᵥ x) + b ⬝ᵥ x + c
  let qShift : (n → ℝ) → ℝ := fun x => x ⬝ᵥ (B *ᵥ x) + b ⬝ᵥ x + (c - lam * h ^ 2)
  have hB_symm : B.IsSymm := by
    -- The shifted matrix stays symmetric because both summands are symmetric.
    dsimp [B]
    exact hA_symm.add ((rank_one_matrix_isSymm g).smul lam)
  have hEqOn :
      Set.EqOn q qShift {x : n → ℝ | g ⬝ᵥ x + h = 0} := by
    -- On the hyperplane, the rank-one correction evaluates to the constant `lam * h^2`.
    simpa [q, qShift, B] using quadratic_eqOn_shifted_hyperplane A b g c h lam
  -- Prove convexity directly by checking closure under convex combinations.
  intro x hx y hy a b' ha hb hab
  refine ⟨?_, ?_⟩
  · let z : n → ℝ := a • x + b' • y
    have hxH : g ⬝ᵥ x + h = 0 := hx.2
    have hyH : g ⬝ᵥ y + h = 0 := hy.2
    have hzH : g ⬝ᵥ z + h = 0 := by
      -- The affine hyperplane is stable under convex combinations.
      dsimp [z]
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      have hgx : g ⬝ᵥ x = -h := eq_neg_of_add_eq_zero_left hxH
      have hgy : g ⬝ᵥ y = -h := eq_neg_of_add_eq_zero_left hyH
      rw [hgx, hgy]
      have hb1 : b' = 1 - a := by linarith
      rw [hb1]
      ring
    have hB_nonneg : ∀ u : n → ℝ, 0 ≤ u ⬝ᵥ (B *ᵥ u) := by
      intro u
      simpa [B] using hlam u
    have hconv :
        qShift z ≤ a * qShift x + b' * qShift y := by
      -- The shifted quadratic is convex because `B` is PSD.
      dsimp [qShift, z]
      exact shifted_quadratic_le hB_symm hB_nonneg b (c - lam * h ^ 2) ha hb hab
    have hxEq : q x = qShift x := hEqOn hxH
    have hyEq : q y = qShift y := hEqOn hyH
    have hzEq : q z = qShift z := hEqOn hzH
    have hxq : q x ≤ 0 := hx.1
    have hyq : q y ≤ 0 := hy.1
    calc
      q z = qShift z := hzEq
      _ ≤ a * qShift x + b' * qShift y := hconv
      _ = a * q x + b' * q y := by rw [← hxEq, ← hyEq]
      _ ≤ 0 := by nlinarith
  · -- The hyperplane equation is preserved by convex combinations.
    show g ⬝ᵥ (a • x + b' • y) + h = 0
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have hgx : g ⬝ᵥ x = -h := eq_neg_of_add_eq_zero_left hx.2
    have hgy : g ⬝ᵥ y = -h := eq_neg_of_add_eq_zero_left hy.2
    rw [hgx, hgy]
    have hb1 : b' = 1 - a := by linarith
    rw [hb1]
    ring

/- [BLOCK Exercise 2.10-(b) | 6 | thm]
Show that the converse of the preceding statement is false in general. That is, give data n, A, b,
c, g, and h with g ≠ 0 such that C ∩ H is convex, but A + λ g gᵀ is not positive semidefinite for
every λ ∈ ℝ.
-/
theorem converse_quadratic_hyperplane_convexity_false :
    ∃ (n : Type*) (_ : Fintype n) (_ : DecidableEq n)
      (A : Matrix n n ℝ) (b g : n → ℝ) (c h : ℝ),
      A.IsSymm ∧
      g ≠ 0 ∧
      Convex ℝ
        ({x : n → ℝ |
            x ⬝ᵥ (A *ᵥ x) + b ⬝ᵥ x + c ≤ 0} ∩
          {x : n → ℝ | g ⬝ᵥ x + h = 0}) ∧
      ∀ lam : ℝ,
        ¬ ∀ x : n → ℝ,
            0 ≤ x ⬝ᵥ (((A + lam • Matrix.of fun i j => g i * g j) *ᵥ x)) := by
  let n : Type _ := ULift (Fin 2)
  let e0 : n := ⟨0⟩
  let e1 : n := ⟨1⟩
  let A : Matrix n n ℝ := Matrix.diagonal fun i => if i = e0 then 0 else -1
  let g : n → ℝ := fun i => if i = e0 then 1 else 0
  let e₂ : n → ℝ := fun i => if i = e1 then 1 else 0
  -- Route correction: use the lifted two-point type locally so the witness matches the theorem's
  -- universe, then carry out the same concrete `diag(0,-1)` and `e₁/e₂` computation.
  have hquad : ∀ x : n → ℝ, x ⬝ᵥ (A *ᵥ x) = -(x e1) ^ 2 := by
    intro x
    -- Rewrite the lifted finite sum back to `Fin 2` and evaluate the diagonal quadratic form.
    calc
      x ⬝ᵥ (A *ᵥ x) = ∑ i : n, x i * ((A *ᵥ x) i) := by
        rw [dotProduct]
      _ = ∑ j : Fin 2, x ⟨j⟩ * ((A *ᵥ x) ⟨j⟩) := by
            simpa [n] using
              (Equiv.sum_comp (Equiv.ulift.symm : Fin 2 ≃ n)
                (fun i : n => x i * ((A *ᵥ x) i))).symm
      _ = x e0 * (0 * x e0) + x e1 * (-1 * x e1) := by
            simp [A, e0, e1, n, Matrix.mulVec_diagonal, Fin.sum_univ_two]
      _ = -(x e1) ^ 2 := by
            ring
  have hnormal : ∀ x : n → ℝ, g ⬝ᵥ x = x e0 := by
    intro x
    -- The chosen normal keeps only the first coordinate.
    calc
      g ⬝ᵥ x = ∑ i : n, g i * x i := by
        rw [dotProduct]
      _ = ∑ j : Fin 2, g ⟨j⟩ * x ⟨j⟩ := by
            simpa [n] using
              (Equiv.sum_comp (Equiv.ulift.symm : Fin 2 ≃ n)
                (fun i : n => g i * x i)).symm
      _ = x e0 := by
            simp [g, e0, n]
  have hinter :
      ({x : n → ℝ | x ⬝ᵥ (A *ᵥ x) + (0 : n → ℝ) ⬝ᵥ x + 0 ≤ 0} ∩
        {x : n → ℝ | g ⬝ᵥ x + 0 = 0})
        = {x : n → ℝ | x e0 = 0} := by
    -- The quadratic constraint is automatic, while the hyperplane equation is exactly `x e0 = 0`.
    ext x
    constructor
    · intro hx
      have hxH : g ⬝ᵥ x + 0 = 0 := hx.2
      rw [hnormal x] at hxH
      simpa using hxH
    · intro hx0
      refine ⟨?_, ?_⟩
      · have hneg : -(x e1) ^ 2 ≤ 0 := by
          nlinarith [sq_nonneg (x e1)]
        change x ⬝ᵥ (A *ᵥ x) + (0 : n → ℝ) ⬝ᵥ x + 0 ≤ 0
        rw [hquad x]
        simpa using hneg
      · change g ⬝ᵥ x + 0 = 0
        rw [hnormal x]
        simpa using hx0
  have hhyper_convex : Convex ℝ {x : n → ℝ | x e0 = 0} := by
    -- Only the first coordinate matters, and affine combinations preserve its vanishing.
    intro x hx y hy a b ha hb hab
    have hx0 : x e0 = 0 := by simpa using hx
    have hy0 : y e0 = 0 := by simpa using hy
    change a * x e0 + b * y e0 = 0
    rw [hx0, hy0]
    ring
  have hnegdir :
      ∀ lam : ℝ,
        e₂ ⬝ᵥ (((A + lam • Matrix.of fun i j => g i * g j) *ᵥ e₂)) = -1 := by
    intro lam
    -- The diagonal part contributes `-1`, and the rank-one correction vanishes on `e₂`.
    have hdiag : e₂ ⬝ᵥ (A *ᵥ e₂) = -1 := by
      simpa [e₂, e1] using hquad e₂
    have horth : g ⬝ᵥ e₂ = 0 := by
      rw [hnormal e₂]
      have h01 : e0 ≠ e1 := by
        intro h
        have : (0 : Fin 2) = 1 := by
          simpa [e0, e1] using congrArg ULift.down h
        exact (by decide : (0 : Fin 2) ≠ 1) this
      simp [e₂, e0, e1, h01]
    calc
      e₂ ⬝ᵥ (((A + lam • Matrix.of fun i j => g i * g j) *ᵥ e₂))
          = e₂ ⬝ᵥ (A *ᵥ e₂)
            + e₂ ⬝ᵥ (((lam • Matrix.of fun i j => g i * g j) *ᵥ e₂)) := by
                rw [Matrix.add_mulVec, dotProduct_add]
      _ = -1 + lam * (g ⬝ᵥ e₂) ^ 2 := by
            rw [hdiag, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, rank_one_quadratic_eval]
      _ = -1 := by
            rw [horth]
            ring
  refine ⟨n, inferInstance, inferInstance, A, 0, g, 0, 0, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The chosen diagonal matrix is symmetric.
    simp [A]
  · -- The normal vector is nonzero because its first coordinate is `1`.
    intro hg
    have hcoord := congrFun hg e0
    simp [g, e0] at hcoord
  · -- Rewrite the intersection to the coordinate hyperplane and use its direct convexity proof.
    change Convex ℝ
      ({x : n → ℝ | x ⬝ᵥ (A *ᵥ x) + (0 : n → ℝ) ⬝ᵥ x + 0 ≤ 0} ∩
        {x : n → ℝ | g ⬝ᵥ x + 0 = 0})
    rw [hinter]
    exact hhyper_convex
  · intro lam hpsd
    -- Testing the shifted matrix on `e₂` yields the contradiction `0 ≤ -1`.
    have htest : 0 ≤ e₂ ⬝ᵥ (((A + lam • Matrix.of fun i j => g i * g j) *ᵥ e₂)) := hpsd e₂
    rw [hnegdir lam] at htest
    linarith

end «problem-89»
