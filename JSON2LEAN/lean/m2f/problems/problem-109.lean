import Mathlib
import problems.«problem-32»

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-109»

/- [BLOCK Exercise 8.20 | 27 | thm]
Let C = {x ∈ ℝ^n : x₁ A₁ + ... + xₙ Aₙ <= B}, where Aᵢ and B are real symmetric m x m matrices, and
assume int(C) is nonempty. Let x_ac minimize φ(x) = -log det(B - sum xᵢ Aᵢ) on the positive definite
domain, and let H be the Hessian of φ at x_ac. Define E_inner = {x : (x-x_ac)ᵀ H (x-x_ac) <= 1} and
E_outer = {x : (x-x_ac)ᵀ H (x-x_ac) <= m(m-1)}. Prove E_inner subseteq C subseteq E_outer.
-/
theorem logDetBarrier_ellipsoid_bounds
    {n m : ℕ}
    (hm : 2 ≤ m)
    (C : Set (Fin n → ℝ))
    (A : Fin n → Matrix (Fin m) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ)
    (x_ac : Fin n → ℝ)
    (phi : (Fin n → ℝ) → ℝ)
    (hA_symm : ∀ i, (A i)ᵀ = A i)
    (hB_symm : Bᵀ = B)
    (hC :
      C =
        {x | Matrix.PosSemidef (B - ∑ i, (x i) • A i)})
    (hC_interior : (interior C).Nonempty)
    (hC_bounded : Bornology.IsBounded C)
    (hphi :
      phi =
        fun x => -Real.log (Matrix.det (B - ∑ i, (x i) • A i)))
    (hx_ac_min :
      x_ac ∈ {x | Matrix.PosDef (B - ∑ i, (x i) • A i)} ∧
        ∀ x, x ∈ {x | Matrix.PosDef (B - ∑ i, (x i) • A i)} → phi x_ac ≤ phi x)
    (hHessian :
      ContDiffAt ℝ 2 phi x_ac ∧
        ∀ i j,
          H i j =
            (fderiv ℝ
              (fun y => (fderiv ℝ phi y) (Pi.single j (1 : ℝ)))
              x_ac) (Pi.single i (1 : ℝ)))
    (hH_symm : H.IsSymm)
    (hH_pos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < dotProduct v (H.mulVec v)) :
    {x | (∑ i, ∑ j, (x i - x_ac i) * ((H i j) * (x j - x_ac j))) ≤ 1} ⊆ C ∧
      C ⊆ {x | (∑ i, ∑ j, (x i - x_ac i) * ((H i j) * (x j - x_ac j))) ≤ ((m : ℝ) * ((m : ℝ) - 1))} := by
  have _hm := hm
  have _hC_interior := hC_interior
  have _hC_bounded := hC_bounded
  -- Route correction: reuse the abstract analytic-center theorem from `problem-32`; the only
  -- remaining work here is to package the concrete hypotheses into that interface.
  have hA_symm' : ∀ i, (A i).IsSymm := by
    -- The problem statement already gives symmetry as transpose invariance.
    intro i
    simpa [Matrix.IsSymm] using hA_symm i
  have hB_symm' : B.IsSymm := by
    -- The same conversion applies to the constant matrix `B`.
    simpa [Matrix.IsSymm] using hB_symm
  have hinterior_nonempty' :
      ∃ x : Fin n → ℝ, Matrix.PosDef (B - ∑ i, (x i) • A i) := by
    -- The analytic center itself is strictly feasible, so it witnesses nonempty interior data.
    exact ⟨x_ac, hx_ac_min.1⟩
  set p : «problem-32».LogDetAnalyticCenterProblem n m :=
    { A := A
      B := B
      A_symm := hA_symm'
      B_symm := hB_symm'
      interior_nonempty := hinterior_nonempty'
      x_ac := x_ac }
  have hx_ac' : p.IsAnalyticCenter p.x_ac := by
    constructor
    · -- Unfold the abstract domain and reuse strict feasibility of `x_ac`.
      simpa [p, «problem-32».LogDetAnalyticCenterProblem.domain,
        «problem-32».LogDetAnalyticCenterProblem.strictlyFeasible,
        «problem-32».LogDetAnalyticCenterProblem.slack] using hx_ac_min.1
    · intro x hx
      -- Translate abstract-domain membership back to the original positive-definite slack set.
      have hx' : x ∈ {x | Matrix.PosDef (B - ∑ i, (x i) • A i)} := by
        simpa [p, «problem-32».LogDetAnalyticCenterProblem.domain,
          «problem-32».LogDetAnalyticCenterProblem.strictlyFeasible,
          «problem-32».LogDetAnalyticCenterProblem.slack] using hx
      -- Then rewrite the abstract objective to the concrete log-det objective.
      have hmin := hx_ac_min.2 x hx'
      simpa [p, «problem-32».LogDetAnalyticCenterProblem.objective,
        «problem-32».LogDetAnalyticCenterProblem.slack, hphi] using hmin
  have hphi_eq_objective : phi = p.objective := by
    -- The packaged objective is definitionally the same concrete log-det barrier.
    simpa [p, «problem-32».LogDetAnalyticCenterProblem.objective,
      «problem-32».LogDetAnalyticCenterProblem.slack] using hphi
  have hH_hessian' :
      H = fun i j =>
        (fderiv ℝ
          (fun y : Fin n → ℝ =>
            (fderiv ℝ p.objective y) (Pi.single j (1 : ℝ))) p.x_ac)
          (Pi.single i (1 : ℝ)) := by
    -- Rewrite the concrete Hessian formula through the packaged objective before simplifying.
    ext i j
    have hij := hHessian.2 i j
    rw [hphi_eq_objective] at hij
    simpa [p] using hij
  have hbounds :=
    «problem-32».analyticCenter_ellipsoid_bounds
      (p := p) (hx_ac := hx_ac') (H := H) hH_hessian' hH_symm hH_pos
  -- Unfold the abstract constraint set and the quadratic form to recover the original statement.
  simpa [p, hC, «problem-32».LogDetAnalyticCenterProblem.constraintSet,
    «problem-32».LogDetAnalyticCenterProblem.feasible,
    «problem-32».LogDetAnalyticCenterProblem.slack,
    Matrix.dotProduct_mulVec, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] using hbounds

end «problem-109»
