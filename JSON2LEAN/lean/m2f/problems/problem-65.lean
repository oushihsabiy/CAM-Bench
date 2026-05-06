import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-65»
/- [BLOCK Exercise 2.30 | 45 | defn]
For functions f,g: ℝ^n → ℝ+∞, their infimal convolution is the function (fsquare g):ℝ^n→ℝ+∞
defined by
(fsquare g)(x)=∈f_y∈ℝ^n(f(y)+g(x-y))
for all x∈ℝ^n.
-/
def infimalConvolution {n : ℕ} (f g : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun x => sInf {r : EReal | ∃ y : Fin n → ℝ, r = f y + g (x - y)}

/- [BLOCK Exercise 2.30 | 46 | defn]
The Huber penalty is the separable function h:ℝ^n→ℝ given by
h(x)=sum_i=1^n φ(xᵢ),
where
φ(u)=casesu^2{2}, & |u|≤ 1,; |u|-1{2}, & |u|>1.cases
-/
def huberScalar {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, if |x i| ≤ 1 then (x i) ^ 2 / 2 else |x i| - 1 / 2

def huberPenalty {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, if |x i| ≤ 1 then (x i) ^ 2 / 2 else |x i| - 1 / 2

/-- The scalar soft-thresholding map that attains the Huber infimal convolution. -/
def softThresholdScalar (u : ℝ) : ℝ :=
  if 1 < u then u - 1 else if u < -1 then u + 1 else 0

/-- The scalar Huber penalty is bounded by every scalar `ℓ¹ + quadratic` objective. -/
lemma scalar_huber_le_objective (u v : ℝ) :
    (if |u| ≤ 1 then u ^ 2 / 2 else |u| - 1 / 2) ≤ |v| + (u - v) ^ 2 / 2 := by
  -- Split into the quadratic and linear Huber branches.
  by_cases hu : |u| ≤ 1
  · -- In the quadratic regime, the cross term is controlled by `|v|`.
    have huv_abs : |u * v| ≤ |v| := by
      calc
        |u * v| = |u| * |v| := by rw [abs_mul]
        _ ≤ 1 * |v| := by
          exact mul_le_mul_of_nonneg_right hu (abs_nonneg v)
        _ = |v| := by ring
    have huv : u * v ≤ |v| := le_trans (le_abs_self _) huv_abs
    have hsq : 0 ≤ v ^ 2 := sq_nonneg v
    simp [hu]
    calc
      u ^ 2 / 2 ≤ u * v + (u - v) ^ 2 / 2 := by
        nlinarith [hsq]
      _ ≤ |v| + (u - v) ^ 2 / 2 := by
        linarith
  · -- In the linear regime, the triangle inequality and a scalar square lower bound suffice.
    have hu_triangle : |u| ≤ |v| + |u - v| := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using abs_add_le (u - v) v
    have hquad : |u - v| - 1 / 2 ≤ (u - v) ^ 2 / 2 := by
      nlinarith [sq_nonneg (|u - v| - 1), sq_abs (u - v)]
    rw [if_neg hu]
    calc
      |u| - 1 / 2 ≤ |v| + (|u - v| - 1 / 2) := by
        linarith
      _ ≤ |v| + (u - v) ^ 2 / 2 := by
        linarith

/-- Soft-thresholding attains the scalar Huber infimal convolution exactly. -/
lemma scalar_huber_eq_softThreshold (u : ℝ) :
    |softThresholdScalar u| + (u - softThresholdScalar u) ^ 2 / 2 =
      if |u| ≤ 1 then u ^ 2 / 2 else |u| - 1 / 2 := by
  -- Split according to the same piecewise cases as the soft-thresholding map.
  by_cases h_pos : 1 < u
  · -- For `u > 1`, the minimizer is `u - 1`, so the residual is exactly `1`.
    have hu_pos : 0 < u := lt_trans zero_lt_one h_pos
    have habs_u : |u| = u := abs_of_pos hu_pos
    have hnot : ¬ |u| ≤ 1 := by
      rw [habs_u]
      linarith
    have habs_shift : |u - 1| = u - 1 := abs_of_nonneg (sub_nonneg.mpr (le_of_lt h_pos))
    rw [if_neg hnot]
    simp [softThresholdScalar, h_pos, habs_u, habs_shift]
    ring
  · by_cases h_neg : u < -1
    · -- For `u < -1`, the minimizer is `u + 1`, so the residual is exactly `-1`.
      have hu_neg : u < 0 := lt_trans h_neg (by norm_num)
      have habs_u : |u| = -u := abs_of_neg hu_neg
      have hnot : ¬ |u| ≤ 1 := by
        rw [habs_u]
        linarith
      have habs_shift : |u + 1| = -(u + 1) := by
        exact abs_of_neg (by linarith)
      rw [if_neg hnot]
      simp [softThresholdScalar, h_pos, h_neg, habs_u, habs_shift]
      ring
    · -- In the central region, soft-thresholding returns `0`, leaving the quadratic branch.
      have hu_upper : u ≤ 1 := le_of_not_gt h_pos
      have hu_lower : -1 ≤ u := le_of_not_gt h_neg
      have habs : |u| ≤ 1 := abs_le.mpr ⟨by linarith, hu_upper⟩
      rw [if_pos habs]
      simp [softThresholdScalar, h_pos, h_neg]

/-- Summing the scalar lower bound yields the coordinatewise lower bound for the Huber penalty. -/
lemma huberPenalty_le_coordinateObjective {n : ℕ} (x y : Fin n → ℝ) :
    huberPenalty x ≤ ∑ i, (|y i| + (x i - y i) ^ 2 / 2 : ℝ) := by
  -- Sum the scalar inequality over coordinates.
  unfold huberPenalty
  exact Finset.sum_le_sum fun i _ => scalar_huber_le_objective (x i) (y i)

/-- The coordinatewise soft-thresholding witness realizes the Huber penalty exactly. -/
lemma huberPenalty_eq_coordinateObjective_softThreshold {n : ℕ} (x : Fin n → ℝ) :
    huberPenalty x =
      ∑ i, (|softThresholdScalar (x i)| + (x i - softThresholdScalar (x i)) ^ 2 / 2 : ℝ) := by
  -- Rewrite each Huber summand using the scalar attainment lemma.
  unfold huberPenalty
  refine Finset.sum_congr rfl ?_
  intro i hi
  symm
  exact scalar_huber_eq_softThreshold (x i)

/-- The infimal-convolution witness value rewrites as a single coordinatewise real sum. -/
lemma infimalObjective_eq_coordinateSum {n : ℕ} (x y : Fin n → ℝ) :
    (((∑ i, |y i| : ℝ) : EReal) + (((1 / 2 : ℝ) * ∑ i, ((x - y) i) ^ 2 : ℝ) : EReal)) =
      ((∑ i, (|y i| + (x i - y i) ^ 2 / 2 : ℝ) : ℝ) : EReal) := by
  -- Combine the `ℓ¹` and quadratic pieces into one finite real sum before comparing in `EReal`.
  rw [← EReal.coe_add]
  congr 1
  calc
    (∑ i, |y i| : ℝ) + (1 / 2 : ℝ) * ∑ i, ((x - y) i) ^ 2
        = (∑ i, |y i| : ℝ) + ∑ i, ((x i - y i) ^ 2 / 2 : ℝ) := by
            simp [Pi.sub_apply, div_eq_mul_inv, Finset.mul_sum, mul_comm]
    _ = ∑ i, (|y i| + (x i - y i) ^ 2 / 2 : ℝ) := by
          rw [← Finset.sum_add_distrib]

/- [BLOCK Exercise 2.30 | 47 | thm]
Let n ∈ ℕ. For functions f,g:ℝ^n → ℝ, define their infimal convolution by
(f square g)(x)=∈f_{y ∈ ℝ^n}(f(y)+g(x-y)), x ∈ ℝ^n.
For x=(x₁,dots,xₙ) ∈ ℝ^n, let
‖x‖_1=sum_{i=1}^n |xᵢ|, ‖x‖_2=(sum_{i=1}^n xᵢ^2)^{1/2}.
Consider
f(x)=‖x‖_1, g(x)=(1)/(2)‖x‖_2^2,
and define
h(x)=(f square g)(x)=∈f_{y ∈ ℝ^n}(‖y‖_1+(1)/(2)‖x-y‖_2^2).
Show that h is the Huber penalty, that is,
h(x)=sum_{i=1}^n φ(xᵢ),
where φ:ℝ→ℝ is given by
φ(u)=
cases
(u^2)/(2), & |u|≤q 1,;
|u|-(1)/(2), & |u|>1.
cases
-/
theorem infimalConvolution_l1_sqNorm_eq_huberPenalty (n : ℕ) :
    infimalConvolution
        (fun x : Fin n → ℝ => ((∑ i, |x i| : ℝ) : EReal))
        (fun x : Fin n → ℝ => ((1 / 2 : ℝ) * ∑ i, (x i) ^ 2 : ℝ))
      =
      fun x : Fin n → ℝ => (huberPenalty x : EReal) := by
  -- Compare both functions pointwise, then identify the infimum with the Huber value.
  funext x
  unfold infimalConvolution
  change
    sInf
        {r : EReal |
          ∃ y : Fin n → ℝ,
            r =
              (((∑ i, |y i| : ℝ) : EReal) +
                (((1 / 2 : ℝ) * ∑ i, ((x - y) i) ^ 2 : ℝ) : EReal))} =
      (huberPenalty x : EReal)
  refine le_antisymm ?_ ?_
  · -- The coordinatewise soft-thresholding witness attains the lower bound exactly.
    let y : Fin n → ℝ := fun i => softThresholdScalar (x i)
    have hy_mem :
        (((∑ i, |y i| : ℝ) : EReal) + (((1 / 2 : ℝ) * ∑ i, ((x - y) i) ^ 2 : ℝ) : EReal)) ∈
          {r : EReal |
            ∃ y : Fin n → ℝ,
              r =
                (((∑ i, |y i| : ℝ) : EReal) +
                  (((1 / 2 : ℝ) * ∑ i, ((x - y) i) ^ 2 : ℝ) : EReal))} := by
      exact ⟨y, rfl⟩
    calc
      sInf
          {r : EReal |
            ∃ y : Fin n → ℝ,
              r =
                (((∑ i, |y i| : ℝ) : EReal) +
                  (((1 / 2 : ℝ) * ∑ i, ((x - y) i) ^ 2 : ℝ) : EReal))} ≤
          ((∑ i, (|y i| + (x i - y i) ^ 2 / 2 : ℝ) : ℝ) : EReal) := by
            exact (sInf_le hy_mem).trans_eq (infimalObjective_eq_coordinateSum x y)
      _ = (huberPenalty x : EReal) := by
        simpa [y] using
          congrArg (fun r : ℝ => (r : EReal))
            (huberPenalty_eq_coordinateObjective_softThreshold x).symm
  · -- Every witness dominates the Huber penalty, so the infimum does as well.
    apply le_sInf
    intro r hr
    rcases hr with ⟨y, rfl⟩
    rw [infimalObjective_eq_coordinateSum]
    exact EReal.coe_le_coe_iff.mpr (huberPenalty_le_coordinateObjective x y)
end «problem-65»
