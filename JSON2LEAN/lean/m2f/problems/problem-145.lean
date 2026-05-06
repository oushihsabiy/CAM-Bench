import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-145»

def l2Norm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i) ^ 2)

/-- The custom `l2Norm` squares to the sum of the coordinate squares. -/
lemma l2Norm_sq_eq_sum_sq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    l2Norm x ^ 2 = ∑ i, x i ^ 2 := by
  -- Rewrite the square of the square root back to the original nonnegative sum.
  unfold l2Norm
  rw [Real.sq_sqrt]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The custom `l2Norm` is always nonnegative. -/
lemma l2Norm_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) : 0 ≤ l2Norm x := by
  -- This is immediate from the nonnegativity of the real square root.
  unfold l2Norm
  exact Real.sqrt_nonneg _

/-- The squared `l2Norm` is convex along affine combinations. -/
lemma l2Norm_sq_affine_le {ι : Type*} [Fintype ι] (x y : ι → ℝ) {a c : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a + c = 1) :
    l2Norm (a • x + c • y) ^ 2 ≤ a * l2Norm x ^ 2 + c * l2Norm y ^ 2 := by
  -- Expand every squared norm into a finite sum to reduce to a scalar inequality.
  rw [l2Norm_sq_eq_sum_sq, l2Norm_sq_eq_sum_sq, l2Norm_sq_eq_sum_sq,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  -- Each coordinate is controlled by the nonnegativity of `(x i - y i)^2`.
  simp only [Pi.add_apply, Pi.smul_apply]
  show (a * x i + c * y i) ^ 2 ≤ a * x i ^ 2 + c * y i ^ 2
  have hidentity :
      a * x i ^ 2 + c * y i ^ 2 - (a * x i + c * y i) ^ 2 = a * c * (x i - y i) ^ 2 := by
    have hc_eq : c = 1 - a := by linarith [hac]
    rw [hc_eq]
    ring
  have hnonneg : 0 ≤ a * c * (x i - y i) ^ 2 := by positivity
  nlinarith [hidentity, hnonneg]

/-- The open unit ball for `l2Norm` is convex. -/
lemma convex_l2Norm_lt_one {ι : Type*} [Fintype ι] :
    Convex ℝ {x : ι → ℝ | l2Norm x < 1} := by
  intro x hx y hy a c ha hc hac
  change l2Norm x < 1 at hx
  change l2Norm y < 1 at hy
  -- Route correction: instead of working with square roots directly, we first control the squares.
  have hxsq : l2Norm x ^ 2 < 1 := by
    have hxnonneg : 0 ≤ l2Norm x := l2Norm_nonneg x
    exact (sq_lt_one_iff₀ hxnonneg).2 hx
  have hysq : l2Norm y ^ 2 < 1 := by
    have hynonneg : 0 ≤ l2Norm y := l2Norm_nonneg y
    exact (sq_lt_one_iff₀ hynonneg).2 hy
  have hcomb_sq :
      l2Norm (a • x + c • y) ^ 2 < 1 := by
    -- Convexity of the squared norm keeps the affine combination strictly inside the unit ball.
    have hsq := l2Norm_sq_affine_le x y ha hc hac
    have hlt : a * l2Norm x ^ 2 + c * l2Norm y ^ 2 < 1 := by
      by_cases ha0 : a = 0
      · have hc1 : c = 1 := by nlinarith [hac, ha0]
        nlinarith [hysq, hc1]
      · have ha_pos : 0 < a := by
          have hne : 0 ≠ a := by simpa [eq_comm] using ha0
          exact lt_of_le_of_ne ha hne
        have hxterm : a * l2Norm x ^ 2 < a * 1 := by
          nlinarith [hxsq, ha_pos]
        have hyterm : c * l2Norm y ^ 2 ≤ c * 1 := by
          nlinarith [hysq.le, hc]
        nlinarith [hxterm, hyterm, hac]
    exact lt_of_le_of_lt hsq hlt
  have hcomb_nonneg : 0 ≤ l2Norm (a • x + c • y) := l2Norm_nonneg _
  -- Convert the strict bound on the square back to a strict bound on the norm itself.
  exact (sq_lt_one_iff₀ hcomb_nonneg).1 hcomb_sq

/-- A scalar quadratic-over-linear inequality for two affine pieces. -/
lemma weighted_sq_div_le (u v a c α β : ℝ)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hα : 0 < α) (hβ : 0 < β) (hden : 0 < a * α + c * β) :
    (a * u + c * v) ^ 2 / (a * α + c * β) ≤ a * (u ^ 2 / α) + c * (v ^ 2 / β) := by
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  have hden0 : a * α + c * β ≠ 0 := ne_of_gt hden
  have hnonneg :
      0 ≤ a * c * (β * u - α * v) ^ 2 / (α * β * (a * α + c * β)) := by
    positivity
  -- After clearing denominators, the gap is exactly a nonnegative square.
  have hidentity :
      a * (u ^ 2 / α) + c * (v ^ 2 / β) - (a * u + c * v) ^ 2 / (a * α + c * β) =
        a * c * (β * u - α * v) ^ 2 / (α * β * (a * α + c * β)) := by
    field_simp [hα0, hβ0, hden0]
    ring
  nlinarith [hnonneg, hidentity]

/-- The quadratic-over-linear inequality summed over all coordinates. -/
lemma weighted_l2Norm_sq_div_le {ι : Type*} [Fintype ι] (u v : ι → ℝ) {a c α β : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hα : 0 < α) (hβ : 0 < β) (hden : 0 < a * α + c * β) :
    l2Norm (a • u + c • v) ^ 2 / (a * α + c * β) ≤
      a * (l2Norm u ^ 2 / α) + c * (l2Norm v ^ 2 / β) := by
  -- Expand the vector inequality into a sum of the scalar inequality on each coordinate.
  rw [l2Norm_sq_eq_sum_sq, l2Norm_sq_eq_sum_sq, l2Norm_sq_eq_sum_sq, Finset.sum_div]
  calc
    ∑ i, (a * u i + c * v i) ^ 2 / (a * α + c * β)
      ≤ ∑ i, (a * (u i ^ 2 / α) + c * (v i ^ 2 / β)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        -- Apply the scalar quadratic-over-linear inequality coordinatewise.
        simpa [Pi.smul_apply, mul_assoc] using
          weighted_sq_div_le (u i) (v i) a c α β ha hc hα hβ hden
    _ = a * ((∑ i, u i ^ 2) / α) + c * ((∑ i, v i ^ 2) / β) := by
      -- Pull the scalar weights back outside the sums.
      calc
        ∑ i, (a * (u i ^ 2 / α) + c * (v i ^ 2 / β))
          = ∑ i, a * (u i ^ 2 / α) + ∑ i, c * (v i ^ 2 / β) := by
              rw [Finset.sum_add_distrib]
        _ = a * (∑ i, u i ^ 2 / α) + c * (∑ i, v i ^ 2 / β) := by
              rw [← Finset.mul_sum, ← Finset.mul_sum]
        _ = a * ((∑ i, u i ^ 2) / α) + c * ((∑ i, v i ^ 2) / β) := by
              rw [Finset.sum_div, Finset.sum_div]

/-
Let A ∈ ℝ^{m \times n} and b ∈ ℝ^m be fixed. Define D = {x ∈ ℝ^n | ‖x‖_2 < 1} and, for x ∈ D, f(x) =
\frac{‖Ax - b‖_2^2}{1 - xᵀ x}. Show that the function f: D o ℝ is convex on D.
-/
theorem ratio_squared_norm_affine_over_one_sub_normSq_convexOn
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (b : m → ℝ) :
    ConvexOn ℝ {x : n → ℝ | l2Norm x < 1}
      (fun x : n → ℝ => l2Norm (A.mulVec x - b) ^ 2 / (1 - l2Norm x ^ 2)) := by
  refine ⟨convex_l2Norm_lt_one, ?_⟩
  intro x hx y hy a c ha hc hac
  change l2Norm x < 1 at hx
  change l2Norm y < 1 at hy
  -- Route correction: we compare a sharper denominator first, then apply the quadratic-over-linear bound.
  have hxnonneg : 0 ≤ l2Norm x := l2Norm_nonneg x
  have hynonneg : 0 ≤ l2Norm y := l2Norm_nonneg y
  have hxsq : l2Norm x ^ 2 < 1 := (sq_lt_one_iff₀ hxnonneg).2 hx
  have hysq : l2Norm y ^ 2 < 1 := (sq_lt_one_iff₀ hynonneg).2 hy
  have hα : 0 < 1 - l2Norm x ^ 2 := by
    exact sub_pos.mpr hxsq
  have hβ : 0 < 1 - l2Norm y ^ 2 := by
    exact sub_pos.mpr hysq
  have hz : l2Norm (a • x + c • y) < 1 := convex_l2Norm_lt_one hx hy ha hc hac
  have hznonneg : 0 ≤ l2Norm (a • x + c • y) := l2Norm_nonneg _
  have hγ : 0 < 1 - l2Norm (a • x + c • y) ^ 2 := by
    exact sub_pos.mpr ((sq_lt_one_iff₀ hznonneg).2 hz)
  have hδ :
      0 < a * (1 - l2Norm x ^ 2) + c * (1 - l2Norm y ^ 2) := by
    by_cases ha0 : a = 0
    · have hc1 : c = 1 := by nlinarith [hac, ha0]
      nlinarith [hβ, hc1]
    · have ha_pos : 0 < a := by
        have hne : 0 ≠ a := by simpa [eq_comm] using ha0
        exact lt_of_le_of_ne ha hne
      have hleft : 0 < a * (1 - l2Norm x ^ 2) := mul_pos ha_pos hα
      have hright : 0 ≤ c * (1 - l2Norm y ^ 2) := mul_nonneg hc hβ.le
      nlinarith
  have hsq :=
    l2Norm_sq_affine_le x y ha hc hac
  have hden_le :
      a * (1 - l2Norm x ^ 2) + c * (1 - l2Norm y ^ 2) ≤
        1 - l2Norm (a • x + c • y) ^ 2 := by
    -- Convexity of the squared norm gives the needed lower bound on the denominator.
    nlinarith [hsq, hac]
  have hmul :
      A.mulVec (a • x + c • y) - b = a • (A.mulVec x - b) + c • (A.mulVec y - b) := by
    -- Rewrite the affine image through linearity of `mulVec`, then absorb the translation.
    rw [show a • x + c • y = (a • x) + (c • y) by rfl]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, sub_eq_add_neg]
    have hc_eq : c = 1 - a := by linarith [hac]
    rw [hc_eq]
    simp only [smul_eq_mul]
    ring
  have hweighted :=
    weighted_l2Norm_sq_div_le (u := A.mulVec x - b) (v := A.mulVec y - b)
      (a := a) (c := c) (α := 1 - l2Norm x ^ 2) (β := 1 - l2Norm y ^ 2) ha hc hα hβ hδ
  calc
    l2Norm (A.mulVec (a • x + c • y) - b) ^ 2 / (1 - l2Norm (a • x + c • y) ^ 2)
      = l2Norm (a • (A.mulVec x - b) + c • (A.mulVec y - b)) ^ 2 /
          (1 - l2Norm (a • x + c • y) ^ 2) := by
            rw [hmul]
    _ ≤ l2Norm (a • (A.mulVec x - b) + c • (A.mulVec y - b)) ^ 2 /
          (a * (1 - l2Norm x ^ 2) + c * (1 - l2Norm y ^ 2)) := by
            -- Enlarging the denominator can only decrease the quotient because the numerator is nonnegative.
            exact div_le_div_of_nonneg_left (sq_nonneg _ ) hδ hden_le
    _ ≤ a * (l2Norm (A.mulVec x - b) ^ 2 / (1 - l2Norm x ^ 2)) +
          c * (l2Norm (A.mulVec y - b) ^ 2 / (1 - l2Norm y ^ 2)) := by
            -- This is exactly the vector quadratic-over-linear inequality.
            simpa [mul_assoc, mul_left_comm, mul_comm] using hweighted

end «problem-145»
