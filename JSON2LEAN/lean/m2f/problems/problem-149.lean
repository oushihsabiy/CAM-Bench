import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-149»
/-
Let the function f: ℝ^n → ℝ be defined by f(x) = ln(\sum_{k = 1}^n e^{xₖ}), x = (x₁, ..., xₙ)^→p ∈
ℝ^n. Compute the Hessian matrix abla^2 f(x) of f.
-/
open scoped BigOperators

theorem hessian_log_sum_exp
    (n : ℕ)
    (hn : 0 < n)
    (x : Fin n → ℝ) :
    ∀ i j : Fin n,
      (fderiv ℝ
        (fun y : Fin n → ℝ =>
          (fderiv ℝ
            (fun z : Fin n → ℝ => Real.log (∑ k : Fin n, Real.exp (z k))) y)
            (Pi.single j (1 : ℝ))) x)
        (Pi.single i (1 : ℝ))
      =
      (Real.exp (x i) / (∑ k : Fin n, Real.exp (x k))) *
        ((if i = j then (1 : ℝ) else 0) -
          Real.exp (x j) / (∑ k : Fin n, Real.exp (x k))) := by
  intro i j
  let S : (Fin n → ℝ) → ℝ := fun y => ∑ k : Fin n, Real.exp (y k)
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 hn
  -- The common denominator is positive because it is a nonempty sum of positive exponentials.
  have hS_pos : ∀ y : Fin n → ℝ, 0 < S y := by
    intro y
    refine Finset.sum_pos ?_ Finset.univ_nonempty
    intro k hk
    exact Real.exp_pos (y k)
  -- Differentiate the `sum exp` map coordinatewise.
  have hS_fderiv :
      ∀ y : Fin n → ℝ,
        HasFDerivAt S
          (∑ k : Fin n, Real.exp (y k) • ContinuousLinearMap.proj (R := ℝ) k) y := by
    intro y
    dsimp [S]
    change HasFDerivAt (fun z : Fin n → ℝ => ∑ k : Fin n, Real.exp (z k))
      (∑ k : Fin n, Real.exp (y k) • ContinuousLinearMap.proj (R := ℝ) k) y
    exact
      HasFDerivAt.fun_sum (u := Finset.univ)
        (A := fun k : Fin n => fun z : Fin n → ℝ => Real.exp (z k))
        (A' := fun k : Fin n => Real.exp (y k) • ContinuousLinearMap.proj (R := ℝ) k)
        (x := y) fun k hk => by
          simpa using (hasFDerivAt_apply k y).exp
  -- The gradient entry of `log (sum exp)` is the corresponding softmax coordinate.
  have hlog_single :
      ∀ y : Fin n → ℝ,
        ∀ l : Fin n,
          (fderiv ℝ (fun z : Fin n → ℝ => Real.log (S z)) y) (Pi.single l (1 : ℝ)) =
            Real.exp (y l) / S y := by
    intro y l
    have hlog :
        HasFDerivAt
          (fun z : Fin n → ℝ => Real.log (S z))
          ((S y)⁻¹ • ∑ k : Fin n, Real.exp (y k) • ContinuousLinearMap.proj (R := ℝ) k)
          y := by
      exact (hS_fderiv y).log (hS_pos y).ne'
    calc
      (fderiv ℝ (fun z : Fin n → ℝ => Real.log (S z)) y) (Pi.single l (1 : ℝ))
          =
            (((S y)⁻¹ • ∑ k : Fin n, Real.exp (y k) • ContinuousLinearMap.proj (R := ℝ) k)
              (Pi.single l (1 : ℝ))) := by
            rw [hlog.fderiv]
      _ = (S y)⁻¹ * Real.exp (y l) := by
        simp [ContinuousLinearMap.proj_apply, Pi.single_apply, mul_comm]
      _ = Real.exp (y l) / S y := by
        rw [div_eq_mul_inv, mul_comm]
  change
    (fderiv ℝ
      (fun y : Fin n → ℝ =>
        (fderiv ℝ (fun z : Fin n → ℝ => Real.log (S z)) y)
          (Pi.single j (1 : ℝ))) x)
      (Pi.single i (1 : ℝ))
    =
    (Real.exp (x i) / S x) *
      ((if i = j then (1 : ℝ) else 0) - Real.exp (x j) / S x)
  -- Rewrite the inner derivative entry as `exp (y_j - log (S y))` to differentiate it again.
  have hrewrite :
      (fun y : Fin n → ℝ =>
        (fderiv ℝ (fun z : Fin n → ℝ => Real.log (S z)) y) (Pi.single j (1 : ℝ))) =
      fun y : Fin n → ℝ => Real.exp (y j - Real.log (S y)) := by
    funext y
    calc
      (fderiv ℝ (fun z : Fin n → ℝ => Real.log (S z)) y) (Pi.single j (1 : ℝ))
          = Real.exp (y j) / S y := hlog_single y j
      _ = Real.exp (y j - Real.log (S y)) := by
        rw [Real.exp_sub, Real.exp_log (hS_pos y)]
  rw [hrewrite]
  -- Route correction: differentiating `exp (y_j - log (S y))` is cleaner than a direct quotient rule.
  have hlog_at_x :
      HasFDerivAt
        (fun z : Fin n → ℝ => Real.log (S z))
        (fderiv ℝ (fun z : Fin n → ℝ => Real.log (S z)) x)
        x := by
    have hlog :
        HasFDerivAt
          (fun z : Fin n → ℝ => Real.log (S z))
          ((S x)⁻¹ • ∑ k : Fin n, Real.exp (x k) • ContinuousLinearMap.proj (R := ℝ) k)
          x := by
      exact (hS_fderiv x).log (hS_pos x).ne'
    simpa [hlog.fderiv] using hlog
  have hexp_sub_log :
      HasFDerivAt
        (fun y : Fin n → ℝ => Real.exp (y j - Real.log (S y)))
        (Real.exp (x j - Real.log (S x)) •
          (ContinuousLinearMap.proj (R := ℝ) j -
            fderiv ℝ (fun z : Fin n → ℝ => Real.log (S z)) x))
        x := by
    -- The exponent differentiates as a coordinate projection minus the derivative of `log (S y)`.
    exact ((hasFDerivAt_apply j x).sub hlog_at_x).exp
  -- Evaluate the resulting linear map on the basis vector `Pi.single i 1`.
  calc
    (fderiv ℝ (fun y : Fin n → ℝ => Real.exp (y j - Real.log (S y))) x) (Pi.single i (1 : ℝ))
        =
          ((((Real.exp (x j - Real.log (S x)) : ℝ) •
              (ContinuousLinearMap.proj (R := ℝ) j -
                fderiv ℝ (fun z : Fin n → ℝ => Real.log (S z)) x)) :
              (Fin n → ℝ) →L[ℝ] ℝ)
            (Pi.single i (1 : ℝ))) := by
          rw [hexp_sub_log.fderiv]
    _ =
        Real.exp (x j - Real.log (S x)) *
          ((if i = j then (1 : ℝ) else 0) - Real.exp (x i) / S x) := by
        rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.proj_apply, hlog_single x i]
        simp [Pi.single_apply, eq_comm]
    _ =
        (Real.exp (x j) / S x) *
          ((if i = j then (1 : ℝ) else 0) - Real.exp (x i) / S x) := by
        rw [Real.exp_sub, Real.exp_log (hS_pos x)]
    _ =
        (Real.exp (x i) / S x) *
          ((if i = j then (1 : ℝ) else 0) - Real.exp (x j) / S x) := by
        by_cases hij : i = j
        · subst hij
          ring
        · ring_nf
          simp [hij]

/-
Let the function f: ℝ^n → ℝ be defined by f(x) = ln(\sum_{k = 1}^n e^{xₖ}), x = (x₁, ..., xₙ)^→p ∈
ℝ^n. Prove that for any x∈ ℝ^n, the matrix abla^2 f(x) is positive semidefinite.
-/
theorem hessian_log_sum_exp_posSemidef
    (n : ℕ)
    (hn : 0 < n)
    (x v : Fin n → ℝ) :
    0 ≤
      ∑ i : Fin n, ∑ j : Fin n,
        v i *
          ((fderiv ℝ
            (fun y : Fin n → ℝ =>
              (fderiv ℝ
                (fun z : Fin n → ℝ => Real.log (∑ k : Fin n, Real.exp (z k))) y)
                (Pi.single j (1 : ℝ))) x)
            (Pi.single i (1 : ℝ))) * v j := by
  sorry

/-
Let the function f: ℝ^n → ℝ be defined by f(x) = ln(\sum_{k = 1}^n e^{xₖ}), x = (x₁, ..., xₙ)^→p ∈
ℝ^n. Deduce that f is convex on ℝ^n.
-/
theorem log_sum_exp_convex
    (n : ℕ)
    (hn : 0 < n) :
    ConvexOn ℝ Set.univ (fun x : Fin n → ℝ => Real.log (∑ k : Fin n, Real.exp (x k))) := by
  sorry
end «problem-149»
