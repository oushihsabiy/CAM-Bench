import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-162»
/-
Let A = (A_{ij})∈ ℝ^{n×n} satisfy A_{ij} > 0 for all i, j = 1, ..., n, and let u, v∈ ℝ^n satisfy uᵢ
>
0 and vᵢ > 0 for all i = 1, ..., n. Define α_i = uᵢ vᵢ for i = 1, ..., n. Consider the optimization
problem minimize & prod_{i = 1}^n (\sum_{j = 1}^n A_{ij}xⱼ)^{α_i}; subject to &
prod_{i = 1}^n xᵢ^{α_i} = 1, array over x∈ ℝ^n with xᵢ > 0 for all i = 1, ..., n.
-/
open scoped BigOperators

structure PositiveMatrixProductMinimization (n : ℕ) where
  A : Fin n → Fin n → ℝ
  u : Fin n → ℝ
  v : Fin n → ℝ
  A_pos : ∀ i j, 0 < A i j
  u_pos : ∀ i, 0 < u i
  v_pos : ∀ i, 0 < v i

def PositiveMatrixProductMinimization.alpha {n : ℕ}
    (P : PositiveMatrixProductMinimization n) : Fin n → ℝ :=
  fun i => P.u i * P.v i

def PositiveMatrixProductMinimization.is_feasible {n : ℕ}
    (P : PositiveMatrixProductMinimization n) (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 < x i) ∧ ∏ i, Real.rpow (x i) (P.alpha i) = 1

def PositiveMatrixProductMinimization.objective {n : ℕ}
    (P : PositiveMatrixProductMinimization n) (x : Fin n → ℝ) : ℝ :=
  ∏ i, Real.rpow (∑ j, P.A i j * x j) (P.alpha i)

/-
positive matrix product minimization. For y∈ ℝ^n, let diag(y) denote the diagonal matrix with
diagonal entries y₁, ..., yₙ, and let Aᵀ denote the ᵀ of A. Using a solution x of this problem,
define D₁ = diag(u)diag(Ax)^{- 1}, D₂ = diag(u)^{- 1}diag(x), where Ax is the usual matrix - vector
product. Show that D₁ and D₂ are positive diagonal matrices satisfying (D_1AD_2)u = u, (D_1AD_2)ᵀ v
= v, by expressing the above problem as a convex optimization problem and deriving the optimality
conditions.
-/
theorem positive_diagonal_scaling_from_optimal_solution
    {n : ℕ} (P : PositiveMatrixProductMinimization n) (x : Fin n → ℝ)
    (hx : P.is_feasible x)
    (hopt :
      ∀ y, P.is_feasible y → P.objective x ≤ P.objective y) :
    let D₁ : Fin n → ℝ := fun i => P.u i / (∑ j, P.A i j * x j)
    let D₂ : Fin n → ℝ := fun j => x j / P.u j
    (∀ i, 0 < D₁ i) ∧
    (∀ j, 0 < D₂ j) ∧
    (∀ i, D₁ i * (∑ j, P.A i j * (D₂ j * P.u j)) = P.u i) ∧
    (∀ j, ∑ i, D₁ i * P.A i j * D₂ j * P.v i = P.v j) := by
  dsimp
  rcases hx with ⟨hx_pos, hx_prod⟩
  set rowSum : Fin n → ℝ := fun i => ∑ l, P.A i l * x l

  -- The weights `α` are strictly positive because both prescribed vectors are positive.
  have hα_pos : ∀ i, 0 < P.alpha i := by
    intro i
    exact mul_pos (P.u_pos i) (P.v_pos i)

  -- Every row sum against a positive vector is positive because each matrix entry is positive.
  have hrow_sum_pos :
      ∀ y : Fin n → ℝ, (∀ m, 0 < y m) → ∀ i, 0 < ∑ l, P.A i l * y l := by
    intro y hy i
    have hterm_pos : 0 < P.A i i * y i := by
      exact mul_pos (P.A_pos i i) (hy i)
    have hterm_nonneg : ∀ l : Fin n, 0 ≤ P.A i l * y l := by
      intro l
      exact mul_nonneg (le_of_lt (P.A_pos i l)) (le_of_lt (hy l))
    exact lt_of_lt_of_le hterm_pos (Finset.single_le_sum (fun l hl => hterm_nonneg l) (by simp))

  have hrow_pos : ∀ i, 0 < rowSum i := by
    intro i
    simpa [rowSum] using hrow_sum_pos x hx_pos i

  have hrow_ne : ∀ i, rowSum i ≠ 0 := by
    intro i
    exact (hrow_pos i).ne'

  -- The objective at the optimizer is positive, so taking logs later is legitimate.
  have hobj_pos : 0 < P.objective x := by
    unfold PositiveMatrixProductMinimization.objective
    refine Finset.prod_pos ?_
    intro i hi
    exact Real.rpow_pos_of_pos (by simpa [rowSum] using hrow_pos i) (P.alpha i)

  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    -- The first diagonal scaling is positive because both numerator and row sum are positive.
    change 0 < P.u i / rowSum i
    exact div_pos (P.u_pos i) (hrow_pos i)
  · intro j
    -- The second diagonal scaling is positive because both `x_j` and `u_j` are positive.
    exact div_pos (hx_pos j) (P.u_pos j)
  · intro i
    -- The row identity is just the definition of `D₁` and `D₂` after cancelling `u_j`.
    change P.u i / rowSum i * (∑ j, P.A i j * (x j / P.u j * P.u j)) = P.u i
    have hsum : (∑ j, P.A i j * (x j / P.u j * P.u j)) = rowSum i := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hu_ne : P.u j ≠ 0 := (P.u_pos j).ne'
      field_simp [hu_ne]
    rw [hsum]
    field_simp [hrow_ne i]
  · -- The column identity comes from first-order optimality along feasible multiplicative perturbations.
    have hpairwise_stationarity :
        ∀ j k : Fin n, j ≠ k →
          x j / P.alpha j * (∑ i, P.alpha i * P.A i j / rowSum i) =
            x k / P.alpha k * (∑ i, P.alpha i * P.A i k / rowSum i) := by
      intro j k hjk
      let scale : ℝ → Fin n → ℝ :=
        fun t m => if m = j then Real.exp (t / P.alpha j)
          else if m = k then Real.exp (-t / P.alpha k) else 1
      let γ : ℝ → Fin n → ℝ := fun t m => x m * scale t m

      -- The perturbation factors are always positive.
      have hscale_pos : ∀ t m, 0 < scale t m := by
        intro t m
        by_cases hmj : m = j
        · simpa [scale, hmj] using Real.exp_pos (t / P.alpha j)
        · by_cases hmk : m = k
          · simpa [scale, hmj, hmk, hjk.symm] using Real.exp_pos (-t / P.alpha k)
          · simp [scale, hmj, hmk]

      -- The `t = 0` perturbation is the original optimizer.
      have hγ_zero : γ 0 = x := by
        funext m
        by_cases hmj : m = j
        · simp [γ, scale, hmj]
        · by_cases hmk : m = k
          · simp [γ, scale, hmk, hjk.symm]
          · simp [γ, scale, hmj, hmk]

      -- The multiplicative feasibility constraint is preserved because the two exponential factors cancel.
      have hscale_rpow :
          ∀ t m, Real.rpow (scale t m) (P.alpha m) =
            if m = j then Real.exp t else if m = k then Real.exp (-t) else 1 := by
        intro t m
        by_cases hmj : m = j
        · have hαj_ne : P.alpha j ≠ 0 := (hα_pos j).ne'
          calc
            Real.rpow (scale t m) (P.alpha m) = Real.rpow (Real.exp (t / P.alpha j)) (P.alpha j) := by
              simp [scale, hmj]
            _ = Real.exp ((t / P.alpha j) * P.alpha j) := by
              simpa using (Real.exp_mul (t / P.alpha j) (P.alpha j)).symm
            _ = Real.exp t := by
              congr 1
              field_simp [hαj_ne]
            _ = if m = j then Real.exp t else if m = k then Real.exp (-t) else 1 := by
              simp [hmj]
        · by_cases hmk : m = k
          · have hαk_ne : P.alpha k ≠ 0 := (hα_pos k).ne'
            calc
              Real.rpow (scale t m) (P.alpha m) = Real.rpow (Real.exp (-t / P.alpha k)) (P.alpha k) := by
                simp [scale, hmk, hjk.symm]
              _ = Real.exp ((-t / P.alpha k) * P.alpha k) := by
                simpa using (Real.exp_mul (-t / P.alpha k) (P.alpha k)).symm
              _ = Real.exp (-t) := by
                congr 1
                field_simp [hαk_ne]
              _ = if m = j then Real.exp t else if m = k then Real.exp (-t) else 1 := by
                simp [hmk, hjk.symm]
          · simp [scale, hmj, hmk]

      have hscale_prod : ∀ t, ∏ m, Real.rpow (scale t m) (P.alpha m) = 1 := by
        intro t
        calc
          ∏ m, Real.rpow (scale t m) (P.alpha m)
              = ∏ m, (if m = j then Real.exp t else if m = k then Real.exp (-t) else 1) := by
                  refine Finset.prod_congr rfl ?_
                  intro m hm
                  rw [hscale_rpow]
          _ = 1 := by
            rw [Finset.prod_eq_mul_prod_diff_singleton (s := Finset.univ) (i := j) (by simp)]
            rw [if_pos rfl]
            have hk : k ∈ Finset.univ \ {j} := by
              simp [hjk.symm]
            rw [Finset.prod_eq_mul_prod_diff_singleton (s := Finset.univ \ {j}) (i := k) hk]
            have hrest :
                ∏ x ∈ (Finset.univ \ {j}) \ {k},
                  (if x = j then Real.exp t else if x = k then Real.exp (-t) else 1 : ℝ) = 1 := by
              apply Finset.prod_eq_one
              intro m hm
              simp at hm
              simp [hm.1, hm.2]
            rw [hrest]
            simp [hjk.symm]
            rw [← Real.exp_add]
            simp

      have hγ_feasible : ∀ t, P.is_feasible (γ t) := by
        intro t
        constructor
        · intro m
          exact mul_pos (hx_pos m) (hscale_pos t m)
        · calc
            ∏ m, Real.rpow (γ t m) (P.alpha m)
                = ∏ m, Real.rpow (x m * scale t m) (P.alpha m) := by
                    rfl
            _ = ∏ m, (Real.rpow (x m) (P.alpha m) * Real.rpow (scale t m) (P.alpha m)) := by
                  refine Finset.prod_congr rfl ?_
                  intro m hm
                  simpa using
                    (Real.mul_rpow (le_of_lt (hx_pos m)) (le_of_lt (hscale_pos t m))
                      (z := P.alpha m))
            _ = (∏ m, Real.rpow (x m) (P.alpha m)) * ∏ m, Real.rpow (scale t m) (P.alpha m) := by
                  rw [Finset.prod_mul_distrib]
            _ = 1 * ∏ m, Real.rpow (scale t m) (P.alpha m) := by
                  rw [hx_prod]
            _ = 1 := by
                  rw [hscale_prod t]
                  simp

      let F : ℝ → ℝ := fun t => ∑ i, P.alpha i * Real.log (∑ l, P.A i l * γ t l)

      have hγ_row_pos : ∀ t i, 0 < ∑ l, P.A i l * γ t l := by
        intro t i
        exact hrow_sum_pos (γ t) (hγ_feasible t).1 i

      -- Rewriting the objective with logarithms turns the minimum into a differentiable one-variable problem.
      have hF_eq_logObjective : ∀ t, F t = Real.log (P.objective (γ t)) := by
        intro t
        dsimp [F, PositiveMatrixProductMinimization.objective]
        rw [Real.log_prod]
        · refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Real.log_rpow (hγ_row_pos t i)]
        · intro i hi
          exact (Real.rpow_pos_of_pos (hγ_row_pos t i) (P.alpha i)).ne'

      have hF_min : ∀ t, F 0 ≤ F t := by
        intro t
        have hγt_feasible : P.is_feasible (γ t) := hγ_feasible t
        calc
          F 0 = Real.log (P.objective (γ 0)) := hF_eq_logObjective 0
          _ = Real.log (P.objective x) := by rw [hγ_zero]
          _ ≤ Real.log (P.objective (γ t)) := by
                exact Real.log_le_log hobj_pos (hopt (γ t) hγt_feasible)
          _ = F t := (hF_eq_logObjective t).symm

      have hlocal_min : IsLocalMin F 0 := by
        exact Filter.Eventually.of_forall hF_min

      -- Differentiate each row sum at `0`; only the `j` and `k` coordinates vary.
      have hrow_deriv :
          ∀ i, HasDerivAt (fun t => ∑ l, P.A i l * γ t l)
            (((P.A i j * x j) / P.alpha j) - ((P.A i k * x k) / P.alpha k)) 0 := by
        intro i
        have hterm :
            ∀ l ∈ Finset.univ,
              HasDerivAt (fun t => P.A i l * γ t l)
                (if l = j then (P.A i j * x j) / P.alpha j
                  else if l = k then -((P.A i k * x k) / P.alpha k) else 0) 0 := by
          intro l hl
          by_cases hlj : l = j
          · have hdiv : HasDerivAt (fun t => t / P.alpha j) (1 / P.alpha j) 0 := by
              simpa using (hasDerivAt_id 0).div_const (P.alpha j)
            have hexp : HasDerivAt (fun t => Real.exp (t / P.alpha j)) (1 / P.alpha j) 0 := by
              simpa using (Real.hasDerivAt_exp (0 / P.alpha j)).comp 0 hdiv
            simpa [hlj, γ, scale, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
              HasDerivAt.const_mul (P.A i j) (HasDerivAt.const_mul (x j) hexp)
          · by_cases hlk : l = k
            · have hdiv : HasDerivAt (fun t => -t / P.alpha k) (-(1 / P.alpha k)) 0 := by
                simpa [one_div, div_eq_mul_inv] using ((hasDerivAt_id 0).neg.div_const (P.alpha k))
              have hexp : HasDerivAt (fun t => Real.exp (-t / P.alpha k)) (-(1 / P.alpha k)) 0 := by
                simpa using (Real.hasDerivAt_exp (-0 / P.alpha k)).comp 0 hdiv
              simpa [hlk, hlj, hjk.symm, γ, scale, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
                HasDerivAt.const_mul (P.A i k) (HasDerivAt.const_mul (x k) hexp)
            · have hconst : HasDerivAt (fun t => P.A i l * γ t l) 0 0 := by
                simpa [γ, scale, hlj, hlk] using (hasDerivAt_const 0 (P.A i l * x l))
              simpa [hlj, hlk] using hconst
        have hsum :
            HasDerivAt (fun t => ∑ l, P.A i l * γ t l)
              (∑ l, if l = j then (P.A i j * x j) / P.alpha j
                else if l = k then -((P.A i k * x k) / P.alpha k) else 0) 0 := by
          have hsum₀ := HasDerivAt.sum (u := Finset.univ) hterm
          convert hsum₀ using 1
          ext t
          simp
        have hsum_eval :
            (∑ l, if l = j then (P.A i j * x j) / P.alpha j
              else if l = k then -((P.A i k * x k) / P.alpha k) else 0) =
              ((P.A i j * x j) / P.alpha j) - ((P.A i k * x k) / P.alpha k) := by
          rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ) (i := j) (by simp)]
          have hk : k ∈ Finset.univ \ {j} := by
            simp [hjk.symm]
          rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ \ {j}) (i := k) hk]
          have hrest :
              ∑ m ∈ (Finset.univ \ {j}) \ {k},
                (if m = j then (P.A i j * x j) / P.alpha j
                  else if m = k then -((P.A i k * x k) / P.alpha k) else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro m hm
            simp at hm
            simp [hm.1, hm.2]
          rw [hrest]
          rw [sub_eq_add_neg]
          simp [hjk.symm]
        simpa [hsum_eval] using hsum

      have hlog_row_deriv :
          ∀ i, HasDerivAt (fun t => Real.log (∑ l, P.A i l * γ t l))
            ((((P.A i j * x j) / P.alpha j) - ((P.A i k * x k) / P.alpha k)) / rowSum i) 0 := by
        intro i
        have hrow_at_zero : (∑ l, P.A i l * γ 0 l) = rowSum i := by
          simp [hγ_zero, rowSum]
        have hlog := (hrow_deriv i).log (by rw [hrow_at_zero]; exact hrow_ne i)
        simpa [hrow_at_zero] using hlog

      have hF_deriv :
          HasDerivAt F
            (∑ i, P.alpha i *
              ((((P.A i j * x j) / P.alpha j) - ((P.A i k * x k) / P.alpha k)) / rowSum i)) 0 := by
        have hF_deriv₀ :
            HasDerivAt
              (∑ i : Fin n, fun t => P.alpha i * Real.log (∑ l, P.A i l * γ t l))
              (∑ i, P.alpha i *
                ((((P.A i j * x j) / P.alpha j) - ((P.A i k * x k) / P.alpha k)) / rowSum i)) 0 :=
          HasDerivAt.sum (u := Finset.univ) fun i hi =>
            HasDerivAt.const_mul (P.alpha i) (hlog_row_deriv i)
        convert hF_deriv₀ using 1
        ext t
        simp [F]

      have hsum_zero :
          ∑ i, P.alpha i *
            ((((P.A i j * x j) / P.alpha j) - ((P.A i k * x k) / P.alpha k)) / rowSum i) = 0 := by
        calc
          ∑ i, P.alpha i *
              ((((P.A i j * x j) / P.alpha j) - ((P.A i k * x k) / P.alpha k)) / rowSum i)
              = deriv F 0 := by
                  symm
                  exact hF_deriv.deriv
          _ = 0 := hlocal_min.deriv_eq_zero

      have hsplit :
          ∑ i, P.alpha i *
            ((((P.A i j * x j) / P.alpha j) - ((P.A i k * x k) / P.alpha k)) / rowSum i)
              = x j / P.alpha j * (∑ i, P.alpha i * P.A i j / rowSum i)
                - x k / P.alpha k * (∑ i, P.alpha i * P.A i k / rowSum i) := by
        calc
          ∑ i, P.alpha i *
              ((((P.A i j * x j) / P.alpha j) - ((P.A i k * x k) / P.alpha k)) / rowSum i)
              = ∑ i, ((x j / P.alpha j) * (P.alpha i * P.A i j / rowSum i)
                  - (x k / P.alpha k) * (P.alpha i * P.A i k / rowSum i)) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    ring
          _ = (∑ i, (x j / P.alpha j) * (P.alpha i * P.A i j / rowSum i))
                - ∑ i, (x k / P.alpha k) * (P.alpha i * P.A i k / rowSum i) := by
                    rw [Finset.sum_sub_distrib]
          _ = x j / P.alpha j * (∑ i, P.alpha i * P.A i j / rowSum i)
                - x k / P.alpha k * (∑ i, P.alpha i * P.A i k / rowSum i) := by
                    rw [← Finset.mul_sum, ← Finset.mul_sum]

      have hstationary_sub :
          x j / P.alpha j * (∑ i, P.alpha i * P.A i j / rowSum i)
            - x k / P.alpha k * (∑ i, P.alpha i * P.A i k / rowSum i) = 0 := by
        rw [← hsplit]
        exact hsum_zero

      exact sub_eq_zero.mp hstationary_sub

    have hbeta_eq_alpha :
        ∀ j, x j * (∑ i, P.alpha i * P.A i j / rowSum i) = P.alpha j := by
      intro j
      let β : Fin n → ℝ := fun l => x l * (∑ i, P.alpha i * P.A i l / rowSum i)

      -- Pairwise stationarity says the normalized quantities `β_l / α_l` are all equal.
      have hβ_prop : ∀ l, β l = (β j / P.alpha j) * P.alpha l := by
        intro l
        by_cases hlj : l = j
        · calc
            β l = β j := by simp [hlj]
            _ = (β j / P.alpha j) * P.alpha j := by
                  have hαj_ne : P.alpha j ≠ 0 := (hα_pos j).ne'
                  field_simp [hαj_ne]
            _ = (β j / P.alpha j) * P.alpha l := by simp [hlj]
        · have hjl : j ≠ l := by
            intro h
            exact hlj h.symm
          have hratio : β j / P.alpha j = β l / P.alpha l := by
            simpa [β, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
              hpairwise_stationarity j l hjl
          calc
            β l = (β l / P.alpha l) * P.alpha l := by
              have hαl_ne : P.alpha l ≠ 0 := (hα_pos l).ne'
              field_simp [hαl_ne]
            _ = (β j / P.alpha j) * P.alpha l := by
              rw [← hratio]

      have hsum_beta : ∑ l, β l = ∑ i, P.alpha i := by
        calc
          ∑ l, β l = ∑ l, x l * (∑ i, P.alpha i * P.A i l / rowSum i) := by
            rfl
          _ = ∑ l, ∑ i, x l * (P.alpha i * P.A i l / rowSum i) := by
                refine Finset.sum_congr rfl ?_
                intro l hl
                rw [Finset.mul_sum]
          _ = ∑ i, ∑ l, x l * (P.alpha i * P.A i l / rowSum i) := by
                rw [Finset.sum_comm]
          _ = ∑ i, P.alpha i := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                calc
                  ∑ l, x l * (P.alpha i * P.A i l / rowSum i)
                      = ∑ l, (P.A i l * x l) * (P.alpha i / rowSum i) := by
                          refine Finset.sum_congr rfl ?_
                          intro l hl
                          ring
                  _ = (∑ l, P.A i l * x l) * (P.alpha i / rowSum i) := by
                        rw [Finset.sum_mul]
                  _ = rowSum i * (P.alpha i / rowSum i) := by
                        simp [rowSum]
                  _ = P.alpha i := by
                        field_simp [hrow_ne i]

      have hαsum_pos : 0 < ∑ l, P.alpha l := by
        have hnonneg : ∀ l : Fin n, 0 ≤ P.alpha l := by
          intro l
          exact (hα_pos l).le
        exact lt_of_lt_of_le (hα_pos j) (Finset.single_le_sum (fun l hl => hnonneg l) (by simp))

      have hscale : β j / P.alpha j = 1 := by
        apply (mul_right_cancel₀ hαsum_pos.ne')
        calc
          (β j / P.alpha j) * (∑ l, P.alpha l) = ∑ l, (β j / P.alpha j) * P.alpha l := by
            rw [Finset.mul_sum]
          _ = ∑ l, β l := by
                refine Finset.sum_congr rfl ?_
                intro l hl
                rw [hβ_prop l]
          _ = ∑ l, P.alpha l := hsum_beta
          _ = 1 * (∑ l, P.alpha l) := by ring

      calc
        x j * (∑ i, P.alpha i * P.A i j / rowSum i) = β j := by
          rfl
        _ = (β j / P.alpha j) * P.alpha j := by
              have hαj_ne : P.alpha j ≠ 0 := (hα_pos j).ne'
              field_simp [β, hαj_ne]
        _ = P.alpha j := by
              rw [hscale, one_mul]

    intro j
    -- Rewriting the column sum in terms of `β_j` finishes the proof.
    change ∑ i, (P.u i / rowSum i) * P.A i j * (x j / P.u j) * P.v i = P.v j
    calc
      ∑ i, (P.u i / rowSum i) * P.A i j * (x j / P.u j) * P.v i
          = ∑ i, (x j / P.u j) * (P.alpha i * P.A i j / rowSum i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [PositiveMatrixProductMinimization.alpha, div_eq_mul_inv, mul_assoc, mul_left_comm,
                mul_comm]
      _ = (x j / P.u j) * (∑ i, P.alpha i * P.A i j / rowSum i) := by
            rw [← Finset.mul_sum]
      _ = (1 / P.u j) * (x j * (∑ i, P.alpha i * P.A i j / rowSum i)) := by
            ring
      _ = (1 / P.u j) * P.alpha j := by
            rw [hbeta_eq_alpha j]
      _ = P.v j := by
            rw [show P.alpha j = P.u j * P.v j by rfl]
            field_simp [(P.u_pos j).ne']

end «problem-162»
