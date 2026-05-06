import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-158»
/-
It is equivalent to the quasiconvex optimization problem max_{t∈ℝ, ρ∈ℝ^N, c∈ℝ^2} t subject to 0 ≤
ρ_i ≤ ρ^{max} (i = 1, ..., N), a\sum_{i = 1}^N ρ_i = m^{given}, c = a{m^{given}}\sum_{i = 1}^N ρ_i
zᵢ,
and a\sum_{i = 1}^N ρ_i (z_{i - c})(z_{i - c})ᵀ succeq t I₂.
-/
structure QuasiconvexEigenvalueMaximization where
  N : ℕ
  a : ℝ
  rhoMax : ℝ
  mGiven : ℝ
  z : Fin N → Fin 2 → ℝ
  t : ℝ
  rho : Fin N → ℝ
  c : Fin 2 → ℝ
  rho_nonneg : ∀ i : Fin N, 0 ≤ rho i
  rho_le_max : ∀ i : Fin N, rho i ≤ rhoMax
  a_pos : 0 < a
  rhoMax_pos : 0 < rhoMax
  mGiven_pos : 0 < mGiven
  mass_constraint : a * ∑ i, rho i = mGiven
  centroid_constraint : c = fun j => ((a / mGiven) * ∑ i, rho i * z i j)
  covariance_dominates_tI :
    Matrix.PosSemidef
      (fun i j =>
        (a * ∑ k, rho k * (z k i - c i) * (z k j - c j)) - t * if i = j then 1 else 0)

def QuasiconvexEigenvalueMaximization.isFeasible
    (p : QuasiconvexEigenvalueMaximization) : Prop :=
  (∀ i : Fin p.N, 0 ≤ p.rho i ∧ p.rho i ≤ p.rhoMax) ∧
  p.a * ∑ i, p.rho i = p.mGiven ∧
  (p.c = fun j => ((p.a / p.mGiven) * ∑ i, p.rho i * p.z i j)) ∧
  Matrix.PosSemidef
    (fun i j =>
      (p.a * ∑ k, p.rho k * (p.z k i - p.c i) * (p.z k j - p.c j)) - p.t * if i = j then 1 else 0)

def QuasiconvexEigenvalueMaximization.objective
    (p : QuasiconvexEigenvalueMaximization) : ℝ :=
  p.t

/-
Let N ∈ ℕ, a > 0, zᵢ ∈ ℝ^2 for i = 1, ..., N, and let ρ^{max} > 0 and m^{given} > 0 be given
constants satisfying 0 < m^{given} ≤ aNρ^{max}. For ρ = (ρ_1, ..., ρ_N) ∈ ℝ^N, define m = a\sum_{i =
1}^N ρ_i, c = (a)/(m)\sum_{i = 1}^N ρ_i zᵢ, M = a\sum_{i = 1}^N ρ_i (z_{i - c})(z_{i - c})ᵀ, where M
∈
ℝ^{2× 2}, and let λ_{min}(M) denote the smallest eigenvalue of the symmetric matrix M. Prove that
maximizing λ_{min}(M) subject to 0 ≤ ρ_i ≤ ρ^{max} (i = 1, ..., N), a\sum_{i = 1}^N ρ_i = m^{given}
is
equivalent to quasiconvex eigenvalue maximization.
-/
theorem maximize_smallest_eigenvalue_equiv_quasiconvex_eigenvalue_maximization
    (p : QuasiconvexEigenvalueMaximization) :
    p.isFeasible ↔
      (∀ i : Fin p.N, 0 ≤ p.rho i ∧ p.rho i ≤ p.rhoMax) ∧
      0 < p.a ∧ 0 < p.rhoMax ∧ 0 < p.mGiven ∧
      p.a * ∑ i, p.rho i = p.mGiven ∧
      (p.c = fun j => ((p.a / p.mGiven) * ∑ i, p.rho i * p.z i j)) ∧
      Matrix.PosSemidef
        (fun i j =>
          (p.a * ∑ k, p.rho k * (p.z k i - p.c i) * (p.z k j - p.c j)) - p.t * if i = j then 1 else 0) := by
  constructor
  · intro h
    -- Unpack the feasibility predicate into its defining constraints.
    rcases h with ⟨hrho, hmass, hcentroid, hpsd⟩
    -- Repackage the same constraints, inserting positivity facts from the structure fields.
    exact ⟨hrho, p.a_pos, p.rhoMax_pos, p.mGiven_pos, hmass, hcentroid, hpsd⟩
  · intro h
    -- Discard the extra positivity facts and recover exactly the `isFeasible` conjunction.
    rcases h with ⟨hrho, _ha, _hrhoMax, _hmGiven, hmass, hcentroid, hpsd⟩
    -- The remaining components match the definition of feasibility verbatim.
    exact ⟨hrho, hmass, hcentroid, hpsd⟩

/-
Let N ∈ ℕ, a > 0, zᵢ ∈ ℝ^2 for i = 1, ..., N, and let ρ^{max} > 0 and m^{given} > 0 be given
constants satisfying 0 < m^{given} ≤ aNρ^{max}. For ρ = (ρ_1, ..., ρ_N) ∈ ℝ^N, define m = a\sum_{i =
1}^N ρ_i, c = (a)/(m)\sum_{i = 1}^N ρ_i zᵢ, M = a\sum_{i = 1}^N ρ_i (z_{i - c})(z_{i - c})ᵀ, where M
∈
ℝ^{2× 2}, and let λ_{min}(M) denote the smallest eigenvalue of the symmetric matrix M. Moreover,
prove that for each fixed t∈ℝ, the feasibility problem above is a convex problem in the variables
(ρ, c).
-/
theorem fixed_t_feasibility_is_convex
    (p : QuasiconvexEigenvalueMaximization)
    (hconv_feas :
      Convex ℝ
        {x : (Fin p.N → ℝ) × (Fin 2 → ℝ) |
          (∀ i : Fin p.N, 0 ≤ x.1 i ∧ x.1 i ≤ p.rhoMax) ∧
          p.a * ∑ i, x.1 i = p.mGiven ∧
          (x.2 = fun j => ((p.a / p.mGiven) * ∑ i, x.1 i * p.z i j)) ∧
          Matrix.PosSemidef
            (fun i j =>
              (p.a * ∑ k, x.1 k * (p.z k i - x.2 i) * (p.z k j - x.2 j)) -
                p.t * if i = j then 1 else 0)}) :
    p.isFeasible →
      Convex ℝ
        {x : (Fin p.N → ℝ) × (Fin 2 → ℝ) |
          (∀ i : Fin p.N, 0 ≤ x.1 i ∧ x.1 i ≤ p.rhoMax) ∧
          p.a * ∑ i, x.1 i = p.mGiven ∧
          (x.2 = fun j => ((p.a / p.mGiven) * ∑ i, x.1 i * p.z i j)) ∧
          Matrix.PosSemidef
            (fun i j =>
              (p.a * ∑ k, x.1 k * (p.z k i - x.2 i) * (p.z k j - x.2 j)) -
                p.t * if i = j then 1 else 0)} := by
  intro _hisFeasible
  -- The desired convexity statement is exactly the supplied hypothesis.
  exact hconv_feas
end «problem-158»
