import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-172»
/-
Let C be a nonempty convex subset of ℝ^n, let C^c = ℝ^n C, and fix a norm. Define dist(x, S) =
\inf{‖x - z‖: z in S}. For x in C, define depth(x, C) = dist(x, C^c). Prove that depth(., C) is
concave
on C: for all x, y in C and θ in [0, 1], depth(θ x + (1 - θ) y, C) > = θ depth(x, C) + (1 - θ)
depth(y,
C).
-/
/-- A point strictly inside the weighted-radius ball around a convex combination can be written
as the same convex combination of points in the corresponding radius balls. -/
lemma weighted_ball_decomposition
    {n : ℕ} {x y w : EuclideanSpace ℝ (Fin n)} {θ rx ry : ℝ}
    (hrx : 0 ≤ rx) (hry : 0 ≤ ry)
    (hw : dist (θ • x + (1 - θ) • y) w < θ * rx + (1 - θ) * ry) :
    ∃ u v : EuclideanSpace ℝ (Fin n),
      w = θ • u + (1 - θ) • v ∧
      (u = x ∨ u ∈ Metric.ball x rx) ∧
      (v = y ∨ v ∈ Metric.ball y ry) := by
  -- Introduce the weighted center and the common displacement toward `w`.
  let z : EuclideanSpace ℝ (Fin n) := θ • x + (1 - θ) • y
  let D : ℝ := θ * rx + (1 - θ) * ry
  let d : EuclideanSpace ℝ (Fin n) := w - z
  have hdist_nonneg : 0 ≤ dist (θ • x + (1 - θ) • y) w := dist_nonneg
  have hDpos : 0 < D := by
    linarith
  have hDne : D ≠ 0 := ne_of_gt hDpos
  -- Split the displacement proportionally to the two radii.
  let u : EuclideanSpace ℝ (Fin n) := x + (rx / D) • d
  let v : EuclideanSpace ℝ (Fin n) := y + (ry / D) • d
  refine ⟨u, v, ?_, ?_, ?_⟩
  · -- Expanding the definitions shows that the new convex combination is exactly `w`.
    have hcoeff : θ * (rx / D) + (1 - θ) * (ry / D) = 1 := by
      field_simp [D, hDne]
      ring
    calc
      w = z + d := by simp [d]
      _ = z + (θ * (rx / D) + (1 - θ) * (ry / D)) • d := by rw [hcoeff, one_smul]
      _ = z + ((θ * (rx / D)) • d + ((1 - θ) * (ry / D)) • d) := by
        rw [add_smul]
      _ = z + (θ * (rx / D)) • d + ((1 - θ) * (ry / D)) • d := by
        simp [add_assoc]
      _ = θ • x + (1 - θ) • y + (θ * (rx / D)) • d + ((1 - θ) * (ry / D)) • d := by
        simp [z, add_assoc]
      _ = θ • u + (1 - θ) • v := by
        simp [u, v, smul_add, smul_smul, add_assoc, add_left_comm]
  · by_cases hrx0 : rx = 0
    · -- Zero radius forces the first point to stay at the original center.
      left
      ext i
      simp [u, d, hrx0]
    · -- Otherwise the first point lands strictly inside the `rx`-ball around `x`.
      right
      have hrx0' : 0 ≠ rx := by
        intro h
        exact hrx0 h.symm
      have hrxpos : 0 < rx := lt_of_le_of_ne hrx hrx0'
      have hd_norm : ‖d‖ < D := by
        have hw' : dist w (θ • x + (1 - θ) • y) < D := by
          simpa [D, dist_comm] using hw
        simpa [d, z, dist_eq_norm] using hw'
      have hu_dist : dist u x = (rx / D) * ‖d‖ := by
        calc
          dist u x = ‖u - x‖ := dist_eq_norm _ _
          _ = ‖(rx / D) • d‖ := by
            simp [u, sub_eq_add_neg, add_assoc]
          _ = ‖(rx / D : ℝ)‖ * ‖d‖ := norm_smul _ _
          _ = (rx / D) * ‖d‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hrx hDpos.le)]
      have hu_lt_aux : (rx * ‖d‖) / D < rx := by
        rw [div_lt_iff₀ hDpos]
        nlinarith
      have hu_lt : dist u x < rx := by
        rw [hu_dist]
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hu_lt_aux
      exact Metric.mem_ball.2 hu_lt
  · by_cases hry0 : ry = 0
    · -- Zero radius forces the second point to stay at the original center.
      left
      ext i
      simp [v, d, hry0]
    · -- Otherwise the second point lands strictly inside the `ry`-ball around `y`.
      right
      have hry0' : 0 ≠ ry := by
        intro h
        exact hry0 h.symm
      have hrypos : 0 < ry := lt_of_le_of_ne hry hry0'
      have hd_norm : ‖d‖ < D := by
        have hw' : dist w (θ • x + (1 - θ) • y) < D := by
          simpa [D, dist_comm] using hw
        simpa [d, z, dist_eq_norm] using hw'
      have hv_dist : dist v y = (ry / D) * ‖d‖ := by
        calc
          dist v y = ‖v - y‖ := dist_eq_norm _ _
          _ = ‖(ry / D) • d‖ := by
            simp [v, sub_eq_add_neg, add_assoc]
          _ = ‖(ry / D : ℝ)‖ * ‖d‖ := norm_smul _ _
          _ = (ry / D) * ‖d‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hry hDpos.le)]
      have hv_lt_aux : (ry * ‖d‖) / D < ry := by
        rw [div_lt_iff₀ hDpos]
        nlinarith
      have hv_lt : dist v y < ry := by
        rw [hv_dist]
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hv_lt_aux
      exact Metric.mem_ball.2 hv_lt

theorem depth_concave_on_convex_set
    {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hC_nonempty : C.Nonempty)
    (hC_compl_nonempty : (Cᶜ).Nonempty)
    (hC_convex : Convex ℝ C) :
    ∀ x y : EuclideanSpace ℝ (Fin n), x ∈ C → y ∈ C →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
        Metric.infDist (θ • x + (1 - θ) • y) (Cᶜ) ≥
          θ * Metric.infDist x (Cᶜ) + (1 - θ) * Metric.infDist y (Cᶜ) := by
  -- The nonemptiness assumption remains part of the statement even though the proof only uses
  -- convexity and nonemptiness of the complement.
  let _ := hC_nonempty
  intro x y hx hy θ hθ0 hθ1
  -- Rewrite the concavity claim as a lower bound against every point of the complement.
  change θ * Metric.infDist x (Cᶜ) + (1 - θ) * Metric.infDist y (Cᶜ) ≤
    Metric.infDist (θ • x + (1 - θ) • y) (Cᶜ)
  refine (Metric.le_infDist hC_compl_nonempty).2 ?_
  intro w hwC
  by_contra hdist
  have hdist_lt :
      dist (θ • x + (1 - θ) • y) w <
        θ * Metric.infDist x (Cᶜ) + (1 - θ) * Metric.infDist y (Cᶜ) :=
    lt_of_not_ge hdist
  -- Decompose `w` into a convex combination of points forced to stay inside `C`.
  rcases weighted_ball_decomposition Metric.infDist_nonneg Metric.infDist_nonneg hdist_lt with
    ⟨u, v, hwuv, hu, hv⟩
  have huC : u ∈ C := by
    rcases hu with rfl | hu_ball
    · exact hx
    · exact Metric.ball_infDist_compl_subset (s := C) hu_ball
  have hvC : v ∈ C := by
    rcases hv with rfl | hv_ball
    · exact hy
    · exact Metric.ball_infDist_compl_subset (s := C) hv_ball
  have hw_in_C : w ∈ C := by
    rw [hwuv]
    exact hC_convex huC hvC hθ0 (sub_nonneg.2 hθ1) (by ring)
  exact hwC hw_in_C

end «problem-172»
