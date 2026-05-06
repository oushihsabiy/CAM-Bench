import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-146»

def l2Norm {m : ℕ} (y : Fin m → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin m, (y i) ^ 2)

/-- Squaring the custom `l2Norm` recovers the sum of squared coordinates. -/
lemma l2Norm_sq_eq_sum_sq {m : ℕ} (y : Fin m → ℝ) :
    l2Norm y ^ 2 = ∑ i : Fin m, (y i) ^ 2 := by
  -- Unfold the definition and use that a sum of squares is nonnegative.
  rw [l2Norm]
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (y i))

/-- The scalar quadratic-over-affine perspective inequality. -/
lemma quadratic_over_affine_coordinate
    {a t α β u v : ℝ} (ha : 0 < a) (ht : 0 < t) (hα : 0 < α) (hβ : 0 < β) :
    (a * u + t * v) ^ 2 / (a * α + t * β) ≤ a * u ^ 2 / α + t * v ^ 2 / β := by
  -- The denominator stays positive on the strict affine half-space.
  have hγ : 0 < a * α + t * β := add_pos (mul_pos ha hα) (mul_pos ht hβ)
  -- The proof reduces to the nonnegativity of a square after clearing denominators.
  have hsquare : 0 ≤ a * t * (β * u - α * v) ^ 2 := by positivity
  field_simp [hα.ne', hβ.ne', hγ.ne'] at hsquare ⊢
  nlinarith

/-- Summing the scalar perspective inequality coordinatewise yields the vector inequality. -/
lemma quadratic_over_affine_l2
    {m : ℕ} (u v : Fin m → ℝ) {a t α β : ℝ}
    (ha : 0 < a) (ht : 0 < t) (hα : 0 < α) (hβ : 0 < β) :
    l2Norm (a • u + t • v) ^ 2 / (a * α + t * β) ≤
      a * l2Norm u ^ 2 / α + t * l2Norm v ^ 2 / β := by
  -- First rewrite the left-hand side as a sum of coordinatewise quadratic-over-affine terms.
  have hsum :
      ∑ i : Fin m, ((a * u i + t * v i) ^ 2 / (a * α + t * β)) ≤
        ∑ i : Fin m, (a * (u i) ^ 2 / α + t * (v i) ^ 2 / β) := by
    -- Each coordinate satisfies the scalar perspective inequality.
    refine Finset.sum_le_sum ?_
    intro i hi
    exact quadratic_over_affine_coordinate (u := u i) (v := v i) ha ht hα hβ
  calc
    l2Norm (a • u + t • v) ^ 2 / (a * α + t * β)
        = ∑ i : Fin m, ((a * u i + t * v i) ^ 2 / (a * α + t * β)) := by
            -- Expand the custom norm and distribute the common denominator across the sum.
            rw [l2Norm_sq_eq_sum_sq, div_eq_mul_inv, Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [Pi.smul_apply, div_eq_mul_inv]
    _ ≤ ∑ i : Fin m, (a * (u i) ^ 2 / α + t * (v i) ^ 2 / β) := hsum
    _ = a * l2Norm u ^ 2 / α + t * l2Norm v ^ 2 / β := by
          -- Pull the constants back out of the coordinate sums.
          rw [l2Norm_sq_eq_sum_sq, l2Norm_sq_eq_sum_sq, Finset.sum_add_distrib]
          congr 1
          · calc
              ∑ i : Fin m, a * (u i) ^ 2 / α = ∑ i : Fin m, a * (u i) ^ 2 * α⁻¹ := by
                simp [div_eq_mul_inv]
              _ = (∑ i : Fin m, a * (u i) ^ 2) * α⁻¹ := by
                rw [Finset.sum_mul]
              _ = a * (∑ i : Fin m, (u i) ^ 2) / α := by
                rw [← Finset.mul_sum]
                simp [div_eq_mul_inv, mul_assoc]
          · calc
              ∑ i : Fin m, t * (v i) ^ 2 / β = ∑ i : Fin m, t * (v i) ^ 2 * β⁻¹ := by
                simp [div_eq_mul_inv]
              _ = (∑ i : Fin m, t * (v i) ^ 2) * β⁻¹ := by
                rw [Finset.sum_mul]
              _ = t * (∑ i : Fin m, (v i) ^ 2) / β := by
                rw [← Finset.mul_sum]
                simp [div_eq_mul_inv, mul_assoc]

/-- The strict affine half-space cut out by `dotProduct c x + d` is convex. -/
lemma convex_dotProduct_add_gt_zero {n : ℕ} (c : Fin n → ℝ) (d : ℝ) :
    Convex ℝ {x : Fin n → ℝ | dotProduct c x + d > 0} := by
  -- Rewrite the affine inequality as a linear strict half-space.
  have hset :
      {x : Fin n → ℝ | dotProduct c x + d > 0} = {x : Fin n → ℝ | -d < dotProduct c x} := by
    ext x
    constructor <;> intro hx <;> simp only [Set.mem_setOf_eq] at hx ⊢ <;> linarith
  rw [hset]
  -- Then invoke the standard convexity result for strict linear half-spaces.
  exact convex_halfSpace_gt
    (𝕜 := ℝ)
    (f := fun x : Fin n → ℝ => dotProduct c x)
    { map_add := fun x y => dotProduct_add c x y
      map_smul := fun a x => dotProduct_smul a c x }
    (-d)

/-- The affine map `x ↦ A.mulVec x + b` preserves convex combinations. -/
lemma mulVec_add_const_smul_add
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    {x y : Fin n → ℝ} {a t : ℝ} (hab : a + t = 1) :
    A.mulVec (a • x + t • y) + b = a • (A.mulVec x + b) + t • (A.mulVec y + b) := by
  -- Expand the matrix action on the convex combination.
  calc
    A.mulVec (a • x + t • y) + b = a • A.mulVec x + t • A.mulVec y + b := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    _ = a • A.mulVec x + t • A.mulVec y + (a + t) • b := by
      rw [hab, one_smul]
    _ = a • (A.mulVec x + b) + t • (A.mulVec y + b) := by
      simp [smul_add, add_smul, add_assoc, add_left_comm, add_comm]

/-- The affine functional `x ↦ dotProduct c x + d` preserves convex combinations. -/
lemma dotProduct_add_const_smul_add
    {n : ℕ} (c : Fin n → ℝ) (d : ℝ)
    {x y : Fin n → ℝ} {a t : ℝ} (hab : a + t = 1) :
    dotProduct c (a • x + t • y) + d =
      a * (dotProduct c x + d) + t * (dotProduct c y + d) := by
  -- Expand the linear part and then fold the constant term back using `a + t = 1`.
  calc
    dotProduct c (a • x + t • y) + d = a * dotProduct c x + t * dotProduct c y + d := by
      simp [dotProduct_add, dotProduct_smul]
    _ = a * dotProduct c x + t * dotProduct c y + (a + t) * d := by
      rw [hab, one_mul]
    _ = a * (dotProduct c x + d) + t * (dotProduct c y + d) := by
      ring

/-
Let A ∈ ℝ^{m × n}, b ∈ ℝ^m, c ∈ ℝ^n, and d ∈ ℝ. Define f: {x ∈ ℝ^n | cᵀ x + d > 0} → ℝ, f(x) =
(‖Ax + b‖_2^2)/(cᵀ x + d), where ‖y‖_2 = (\sum_{i = 1}^m yᵢ^2)^{1/2} is the Euclidean norm on ℝ^m.
Show
that f is convex on {x ∈ ℝ^n | cᵀ x + d > 0}.
-/
theorem quadratic_over_affine_isConvexOn
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (d : ℝ) :
    ConvexOn ℝ
      {x : Fin n → ℝ | dotProduct c x + d > 0}
      (fun x => l2Norm (A.mulVec x + b) ^ 2 / (dotProduct c x + d)) := by
  -- Use the positive-coefficient characterization of convexity on a convex domain.
  refine (convexOn_iff_forall_pos).2 ?_
  refine ⟨convex_dotProduct_add_gt_zero c d, ?_⟩
  intro x hx y hy a t ha ht hab
  -- Rewrite the affine numerator and denominator into the perspective form.
  rw [mulVec_add_const_smul_add A b hab, dotProduct_add_const_smul_add c d hab]
  -- The vector perspective inequality now applies directly.
  simpa [smul_eq_mul, mul_div_assoc] using
    quadratic_over_affine_l2
      (u := A.mulVec x + b) (v := A.mulVec y + b)
      (α := dotProduct c x + d) (β := dotProduct c y + d)
      ha ht hx hy
end «problem-146»
