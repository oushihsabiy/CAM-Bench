import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-171»
/-
A set C is a Chebyshev set if for every x ∈ ℝ^n there exists a unique point P_C(x) in C such that ‖x
- P_C(x)‖ < = ‖x - y‖ for all y in C.
-/
def IsChebyshevSet {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n),
    ∃! p, p ∈ C ∧ ∀ y, y ∈ C → ‖x - p‖ ≤ ‖x - y‖

/-
Let C be a Chebyshev set ∈ ℝ^n. Assume that for every x ∈ ℝ^n and every t > = 0, P_C(P_C(x) + t (x -
P_C(x))) = P_C(x). Prove that C is convex.
-/
theorem chebyshev_set_convex_of_projection_ray_fixed {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsChebyshevSet C)
    (hproj :
      ∀ x : EuclideanSpace ℝ (Fin n), ∀ t : ℝ,
        0 ≤ t →
          let p := Classical.choose (hC x)
          Classical.choose (hC (p + t • (x - p))) = p) :
    Convex ℝ C := by
  -- It is enough to show that every strict convex combination of points of `C` stays in `C`.
  rw [convex_iff_forall_pos]
  intro u hu v hv a b ha hb hab
  let z : EuclideanSpace ℝ (Fin n) := a • u + b • v
  let pz : EuclideanSpace ℝ (Fin n) := Classical.choose (hC z)
  have hpz_spec := Classical.choose_spec (hC z)
  have hpz_mem : pz ∈ C := hpz_spec.1.1

  -- Along every outward ray from a chosen projection, the minimizer inequality forces an obtuse angle.
  have chosen_projection_inner_nonpos :
      ∀ x y : EuclideanSpace ℝ (Fin n), y ∈ C →
        ⟪x - Classical.choose (hC x), y - Classical.choose (hC x)⟫ ≤ 0 := by
    intro x y hy
    let p : EuclideanSpace ℝ (Fin n) := Classical.choose (hC x)
    have hp : p ∈ C ∧ ∀ z, z ∈ C → ‖x - p‖ ≤ ‖x - z‖ := (Classical.choose_spec (hC x)).1
    by_contra hnonpos
    have hpos : 0 < ⟪x - p, y - p⟫ := by
      simpa [p] using lt_of_not_ge hnonpos
    let t : ℝ := ‖y - p‖ ^ 2 / (2 * ⟪x - p, y - p⟫) + 1
    have ht_nonneg : 0 ≤ t := by
      have hs : 0 < 2 * ⟪x - p, y - p⟫ := by
        nlinarith
      have hdiv : 0 ≤ ‖y - p‖ ^ 2 / (2 * ⟪x - p, y - p⟫) := by
        exact div_nonneg (by positivity) hs.le
      dsimp [t]
      linarith
    have hfix : Classical.choose (hC (p + t • (x - p))) = p := by
      simpa [p] using hproj x t ht_nonneg
    -- The ray hypothesis turns the chosen point `p` into a minimizer for the shifted base point.
    have hdist_raw : ‖(p + t • (x - p)) - p‖ ≤ ‖(p + t • (x - p)) - y‖ := by
      have hmin := (Classical.choose_spec (hC (p + t • (x - p)))).1.2 y hy
      rw [hfix] at hmin
      exact hmin
    have hdist : ‖t • (x - p)‖ ≤ ‖(p + t • (x - p)) - y‖ := by
      calc
        ‖t • (x - p)‖ = ‖(p + t • (x - p)) - p‖ := by
          congr 1
          abel_nf
        _ ≤ ‖(p + t • (x - p)) - y‖ := hdist_raw
    -- Squaring and expanding both sides isolates the linear term in `t`.
    have hsq : ‖t • (x - p)‖ ^ 2 ≤ ‖t • (x - p) - (y - p)‖ ^ 2 := by
      have hsquared : ‖t • (x - p)‖ ^ 2 ≤ ‖(p + t • (x - p)) - y‖ ^ 2 := by
        nlinarith [norm_nonneg (t • (x - p)), norm_nonneg ((p + t • (x - p)) - y), hdist]
      calc
        ‖t • (x - p)‖ ^ 2 ≤ ‖(p + t • (x - p)) - y‖ ^ 2 := hsquared
        _ = ‖t • (x - p) - (y - p)‖ ^ 2 := by
          congr 1
          abel_nf
    have hleft : ‖t • (x - p)‖ ^ 2 = t ^ 2 * ‖x - p‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hright :
        ‖t • (x - p) - (y - p)‖ ^ 2 =
          t ^ 2 * ‖x - p‖ ^ 2 - 2 * t * ⟪x - p, y - p⟫ + ‖y - p‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_left, hleft]
      ring
    have hineq : 0 ≤ -2 * t * ⟪x - p, y - p⟫ + ‖y - p‖ ^ 2 := by
      rw [hleft, hright] at hsq
      nlinarith
    have hs_ne : 2 * ⟪x - p, y - p⟫ ≠ 0 := by
      nlinarith
    have ht_value : -2 * t * ⟪x - p, y - p⟫ + ‖y - p‖ ^ 2 = -2 * ⟪x - p, y - p⟫ := by
      dsimp [t]
      field_simp [hs_ne]
      ring
    rw [ht_value] at hineq
    nlinarith

  have hu_inner : ⟪z - pz, u - pz⟫ ≤ 0 := by
    simpa [z, pz] using chosen_projection_inner_nonpos z u hu
  have hv_inner : ⟪z - pz, v - pz⟫ ≤ 0 := by
    simpa [z, pz] using chosen_projection_inner_nonpos z v hv

  -- Rewriting the displacement `z - pz` in barycentric form lets the obtuse-angle inequalities close the norm.
  have hzsub : z - pz = a • (u - pz) + b • (v - pz) := by
    calc
      a • u + b • v - pz = a • u + b • v - ((a + b) • pz) := by
        rw [hab, one_smul]
      _ = a • (u - pz) + b • (v - pz) := by
        rw [add_smul, smul_sub, smul_sub]
        abel_nf
  have hself : ⟪z - pz, z - pz⟫ = a * ⟪z - pz, u - pz⟫ + b * ⟪z - pz, v - pz⟫ := by
    rw [hzsub, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have hself_nonpos : ⟪z - pz, z - pz⟫ ≤ 0 := by
    rw [hself]
    nlinarith
  have hself_eq : ⟪z - pz, z - pz⟫ = 0 := by
    have hself_nonneg : 0 ≤ ⟪z - pz, z - pz⟫ := real_inner_self_nonneg
    linarith
  have hz_eq_pz : z = pz := by
    have hz_zero : z - pz = 0 := by
      rwa [inner_self_eq_zero] at hself_eq
    exact sub_eq_zero.mp hz_zero

  -- The chosen projection lies in `C`, so the convex combination belongs to `C` as well.
  simpa [z, hz_eq_pz] using hpz_mem
end «problem-171»
