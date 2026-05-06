import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-3»
/-
Let A ∈ ℝ^{m × n} have rows a_1ᵀ, ..., a_mᵀ, let b ∈ ℝ^m, c ∈ ℝ^n, and let μ > 0. Consider the
convex
optimization problem min_{x ∈ ℝ^n} (cᵀ x + (1)/(μ) \sum_{i = 1}^m log(1 + e^{μ(a_iᵀ x - bᵢ)})).
-/
structure ConvexLogisticProgram where
  m : ℕ
  n : ℕ
  A : Fin m → Fin n → ℝ
  b : Fin m → ℝ
  c : Fin n → ℝ
  μ : ℝ
  μ_pos : 0 < μ

def ConvexLogisticProgram.rowDot (P : ConvexLogisticProgram) (i : Fin P.m) (x : Fin P.n → ℝ) : ℝ :=
  ∑ j : Fin P.n, P.A i j * x j

def ConvexLogisticProgram.objective (P : ConvexLogisticProgram) (x : Fin P.n → ℝ) : ℝ :=
  (∑ j : Fin P.n, P.c j * x j) +
    (1 / P.μ) * ∑ i : Fin P.m, Real.log (1 + Real.exp (P.μ * (P.rowDot i x - P.b i)))

def ConvexLogisticProgram.optimalValue (P : ConvexLogisticProgram) : EReal :=
  sInf ((fun x : Fin P.n → ℝ => (P.objective x : EReal)) '' Set.univ)

/-
Consider the following primal - dual pair of linear programs: primal: & min cᵀ x; & subject to Ax ≤
b,
dual: & max - bᵀ z; & subject to Aᵀ z + c = 0,; & z ≥ 0.
-/
structure PrimalDualLinearProgram where
  m : ℕ
  n : ℕ
  A : Fin m → Fin n → ℝ
  b : Fin m → ℝ
  c : Fin n → ℝ

def PrimalDualLinearProgram.primalFeasible (P : PrimalDualLinearProgram) (x : Fin P.n → ℝ) : Prop :=
  ∀ i : Fin P.m, (∑ j : Fin P.n, P.A i j * x j) ≤ P.b i

def PrimalDualLinearProgram.primalObjective (P : PrimalDualLinearProgram) (x : Fin P.n → ℝ) : ℝ :=
  ∑ j : Fin P.n, P.c j * x j

def PrimalDualLinearProgram.dualFeasible (P : PrimalDualLinearProgram) (z : Fin P.m → ℝ) : Prop :=
  (∀ j : Fin P.n, (∑ i : Fin P.m, P.A i j * z i) + P.c j = 0) ∧
    ∀ i : Fin P.m, 0 ≤ z i

def PrimalDualLinearProgram.dualObjective (P : PrimalDualLinearProgram) (z : Fin P.m → ℝ) : ℝ :=
  -∑ i : Fin P.m, P.b i * z i

def PrimalDualLinearProgram.primalOptimalValue (P : PrimalDualLinearProgram) : EReal :=
  sInf ((fun x : Fin P.n → ℝ => (P.primalObjective x : EReal)) '' {x | P.primalFeasible x})

def PrimalDualLinearProgram.dualOptimalValue (P : PrimalDualLinearProgram) : EReal :=
  sSup ((fun z : Fin P.m → ℝ => (P.dualObjective z : EReal)) '' {z | P.dualFeasible z})

/-- A softplus term dominates any `z * t` with `z ∈ [0, 1]`. -/
lemma softplus_ge_mul_of_unit_interval {μ z t : ℝ} (hμ : 0 < μ) (hz₀ : 0 ≤ z) (hz₁ : z ≤ 1) :
    z * t ≤ (1 / μ) * Real.log (1 + Real.exp (μ * t)) := by
  -- Split into the nonnegative and nonpositive regimes for `t`.
  by_cases ht : 0 ≤ t
  · -- For `t ≥ 0`, compare first with `t`, then use `exp (μ t) ≤ 1 + exp (μ t)`.
    have hzt : z * t ≤ t := by
      have hmul := mul_le_mul_of_nonneg_right hz₁ ht
      simpa using hmul
    have hlog : μ * t ≤ Real.log (1 + Real.exp (μ * t)) := by
      rw [Real.le_log_iff_exp_le]
      · have hexp_pos : 0 < Real.exp (μ * t) := Real.exp_pos (μ * t)
        linarith
      · have hexp_pos : 0 < Real.exp (μ * t) := Real.exp_pos (μ * t)
        linarith
    have hscaled :
        (1 / μ) * (μ * t) ≤ (1 / μ) * Real.log (1 + Real.exp (μ * t)) := by
      exact mul_le_mul_of_nonneg_left hlog (by positivity)
    have ht_softplus : t ≤ (1 / μ) * Real.log (1 + Real.exp (μ * t)) := by
      simpa [div_eq_mul_inv, mul_assoc, hμ.ne'] using hscaled
    exact hzt.trans ht_softplus
  · -- For `t ≤ 0`, the left side is nonpositive while the softplus stays nonnegative.
    have ht' : t ≤ 0 := le_of_not_ge ht
    have hzt : z * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hz₀ ht'
    have hlog_nonneg : 0 ≤ Real.log (1 + Real.exp (μ * t)) := by
      apply Real.log_nonneg
      have hexp_pos : 0 < Real.exp (μ * t) := Real.exp_pos (μ * t)
      linarith
    have hsoftplus_nonneg : 0 ≤ (1 / μ) * Real.log (1 + Real.exp (μ * t)) := by
      exact mul_nonneg (by positivity) hlog_nonneg
    exact hzt.trans hsoftplus_nonneg

/-- A softplus term is at most `log 2 / μ` on the nonpositive half-line. -/
lemma softplus_le_log_two_div_of_nonpos {μ t : ℝ} (hμ : 0 < μ) (ht : t ≤ 0) :
    (1 / μ) * Real.log (1 + Real.exp (μ * t)) ≤ Real.log 2 / μ := by
  -- Bound the exponential by `1` and then use monotonicity of `log`.
  have hμt_nonpos : μ * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hμ.le ht
  have hexp_le_one : Real.exp (μ * t) ≤ 1 := Real.exp_le_one_iff.mpr hμt_nonpos
  have harg_le_two : 1 + Real.exp (μ * t) ≤ 2 := by linarith
  have hlog_le : Real.log (1 + Real.exp (μ * t)) ≤ Real.log 2 := by
    apply Real.log_le_log
    · have hexp_pos : 0 < Real.exp (μ * t) := Real.exp_pos (μ * t)
      linarith
    · exact harg_le_two
  have hscaled :
      (1 / μ) * Real.log (1 + Real.exp (μ * t)) ≤ (1 / μ) * Real.log 2 := by
    exact mul_le_mul_of_nonneg_left hlog_le (by positivity)
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled

/-- Under dual feasibility, the primal objective plus weighted residuals equals the dual objective. -/
lemma primalObjective_add_weightedResidual_eq_dualObjective
    (P : PrimalDualLinearProgram) (z : Fin P.m → ℝ) (hz : P.dualFeasible z)
    (x : Fin P.n → ℝ) :
    P.primalObjective x +
        ∑ i : Fin P.m, z i * ((∑ j : Fin P.n, P.A i j * x j) - P.b i) =
      P.dualObjective z := by
  rcases hz with ⟨hz_eq, _⟩
  -- Rewrite the mixed double sum by exchanging the order of summation.
  have hswap :
      ∑ i : Fin P.m, z i * ∑ j : Fin P.n, P.A i j * x j =
        ∑ j : Fin P.n, x j * ∑ i : Fin P.m, P.A i j * z i := by
    calc
      ∑ i : Fin P.m, z i * ∑ j : Fin P.n, P.A i j * x j
          = ∑ i : Fin P.m, ∑ j : Fin P.n, z i * (P.A i j * x j) := by
              simp [Finset.mul_sum]
      _ = ∑ j : Fin P.n, ∑ i : Fin P.m, x j * (P.A i j * z i) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro j _
            refine Finset.sum_congr rfl ?_
            intro i _
            ring
      _ = ∑ j : Fin P.n, x j * ∑ i : Fin P.m, P.A i j * z i := by
            simp [Finset.mul_sum, mul_left_comm, mul_comm]
  have hdual_zero : ∀ j : Fin P.n, P.c j + ∑ i : Fin P.m, P.A i j * z i = 0 := by
    intro j
    linarith [hz_eq j]
  -- Expand the weighted residuals and collapse the coefficient of each `x j`.
  have hresidual :
      ∑ i : Fin P.m, z i * ((∑ j : Fin P.n, P.A i j * x j) - P.b i) =
        (∑ i : Fin P.m, z i * ∑ j : Fin P.n, P.A i j * x j) -
          ∑ i : Fin P.m, P.b i * z i := by
    calc
      ∑ i : Fin P.m, z i * ((∑ j : Fin P.n, P.A i j * x j) - P.b i)
          = ∑ i : Fin P.m, (z i * ∑ j : Fin P.n, P.A i j * x j - P.b i * z i) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              ring
      _ = (∑ i : Fin P.m, z i * ∑ j : Fin P.n, P.A i j * x j) -
            ∑ i : Fin P.m, P.b i * z i := by
              rw [Finset.sum_sub_distrib]
  have hlinear_zero :
      (∑ j : Fin P.n, P.c j * x j) + ∑ i : Fin P.m, z i * ∑ j : Fin P.n, P.A i j * x j = 0 := by
    rw [hswap]
    calc
      (∑ j : Fin P.n, P.c j * x j) + ∑ j : Fin P.n, x j * ∑ i : Fin P.m, P.A i j * z i
          = ∑ j : Fin P.n, (P.c j * x j + x j * ∑ i : Fin P.m, P.A i j * z i) := by
              rw [← Finset.sum_add_distrib]
      _ = ∑ j : Fin P.n, x j * (P.c j + ∑ i : Fin P.m, P.A i j * z i) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            ring
      _ = 0 := by
            apply Finset.sum_eq_zero
            intro j _
            rw [hdual_zero j, mul_zero]
  calc
    P.primalObjective x + ∑ i : Fin P.m, z i * ((∑ j : Fin P.n, P.A i j * x j) - P.b i)
        = (∑ j : Fin P.n, P.c j * x j) +
            ∑ i : Fin P.m, z i * ∑ j : Fin P.n, P.A i j * x j -
            ∑ i : Fin P.m, P.b i * z i := by
              rw [PrimalDualLinearProgram.primalObjective, hresidual]
              ring
    _ = 0 - ∑ i : Fin P.m, P.b i * z i := by rw [hlinear_zero]
    _ = -∑ i : Fin P.m, P.b i * z i := by ring
    _ = P.dualObjective z := by
          rw [PrimalDualLinearProgram.dualObjective]

/-
Consider the convex logistic program. Let q^star be its optimal value. Consider also the primal -
dual
linear programs. Assume the primal linear program is feasible, these linear programs have finite
optimal value p^star, and that there exists a dual optimal solution z^star ∈ ℝ^m such that
z^star ≤ 1, where all inequalities are componentwise and 1 ∈ ℝ^m is the all - ones vector. Show that
p^star ≤ q^star ≤ p^star + \frac{m log 2}{μ}.
-/
theorem primal_dual_linear_program_optimalValue_le_convexLogisticProgram_optimalValue_le
    (P : PrimalDualLinearProgram)
    (Q : ConvexLogisticProgram)
    (hm : Q.m = P.m)
    (hn : Q.n = P.n)
    (hA : ∀ i : Fin P.m, ∀ j : Fin P.n, Q.A (Fin.cast hm.symm i) (Fin.cast hn.symm j) = P.A i j)
    (hb : ∀ i : Fin P.m, Q.b (Fin.cast hm.symm i) = P.b i)
    (hc : ∀ j : Fin P.n, Q.c (Fin.cast hn.symm j) = P.c j)
    (pStar : ℝ)
    (h_primal_feasible : ∃ x : Fin P.n → ℝ, P.primalFeasible x)
    (hp_primal : P.primalOptimalValue = (pStar : EReal))
    (hp_dual : P.dualOptimalValue = (pStar : EReal))
    (hz_exists : ∃ zStar : Fin P.m → ℝ,
      (P.dualFeasible zStar ∧ P.dualObjective zStar = pStar) ∧
      (∀ i : Fin P.m, zStar i ≤ 1)) :
    (pStar : EReal) ≤ Q.optimalValue ∧
      Q.optimalValue ≤ ((pStar + (P.m : ℝ) * Real.log 2 / Q.μ : ℝ) : EReal) := by
  cases P with
  | mk m n A b c =>
    cases Q with
    | mk mQ nQ AQ bQ cQ μ μ_pos =>
      revert hA hb hc
      cases hm
      cases hn
      intro hA hb hc
      let P : PrimalDualLinearProgram := ⟨m, n, A, b, c⟩
      let Q : ConvexLogisticProgram := ⟨m, n, AQ, bQ, cQ, μ, μ_pos⟩
      have hA' : ∀ i : Fin P.m, ∀ j : Fin P.n, Q.A i j = P.A i j := by
        simpa [P, Q] using hA
      have hb' : ∀ i : Fin P.m, Q.b i = P.b i := by
        simpa [P, Q] using hb
      have hc' : ∀ j : Fin P.n, Q.c j = P.c j := by
        simpa [P, Q] using hc
      have h_primal_feasible' : ∃ x : Fin P.n → ℝ, P.primalFeasible x := by
        simpa [P] using h_primal_feasible
      have hp_primal' : P.primalOptimalValue = (pStar : EReal) := by
        simpa [P] using hp_primal
      have hp_dual' : P.dualOptimalValue = (pStar : EReal) := by
        simpa [P] using hp_dual
      have hz_exists' : ∃ zStar : Fin P.m → ℝ,
          (P.dualFeasible zStar ∧ P.dualObjective zStar = pStar) ∧
            (∀ i : Fin P.m, zStar i ≤ 1) := by
        simpa [P] using hz_exists
      have hmain :
          (pStar : EReal) ≤ Q.optimalValue ∧
            Q.optimalValue ≤ ((pStar + (P.m : ℝ) * Real.log 2 / Q.μ : ℝ) : EReal) := by
        rcases hz_exists' with ⟨zStar, ⟨hz_dual, hz_obj⟩, hz_one⟩
        rcases hz_dual with ⟨hz_eq, hz_nonneg⟩
        let shift : ℝ := (P.m : ℝ) * Real.log 2 / Q.μ
        let shiftE : EReal := (shift : ℝ)
        have hobjective_eq :
            ∀ x : Fin P.n → ℝ,
              Q.objective x =
                P.primalObjective x +
                  ∑ i : Fin P.m,
                    (1 / Q.μ) *
                      Real.log (1 + Real.exp (Q.μ * ((∑ j : Fin P.n, P.A i j * x j) - P.b i))) := by
          intro x
          -- Rewrite the logistic objective using the shared LP data.
          simp [ConvexLogisticProgram.objective, ConvexLogisticProgram.rowDot,
            PrimalDualLinearProgram.primalObjective, hA', hb', hc', Finset.mul_sum]
          ring
        have hpointwise_lower :
            ∀ x : Fin P.n → ℝ,
              pStar ≤ Q.objective x := by
          intro x
          -- Compare each softplus term with the dual weight on the same residual.
          have hsum :
              ∑ i : Fin P.m, zStar i * ((∑ j : Fin P.n, P.A i j * x j) - P.b i) ≤
                ∑ i : Fin P.m,
                  (1 / Q.μ) *
                    Real.log (1 + Real.exp (Q.μ * ((∑ j : Fin P.n, P.A i j * x j) - P.b i))) := by
            apply Finset.sum_le_sum
            intro i _
            exact softplus_ge_mul_of_unit_interval Q.μ_pos (hz_nonneg i) (hz_one i)
          -- Collapse the weighted residuals using the dual feasibility equations.
          calc
            pStar = P.dualObjective zStar := hz_obj.symm
            _ =
                P.primalObjective x +
                  ∑ i : Fin P.m, zStar i * ((∑ j : Fin P.n, P.A i j * x j) - P.b i) := by
                    symm
                    exact primalObjective_add_weightedResidual_eq_dualObjective P zStar ⟨hz_eq, hz_nonneg⟩ x
            _ ≤
                P.primalObjective x +
                  ∑ i : Fin P.m,
                    (1 / Q.μ) *
                      Real.log (1 + Real.exp (Q.μ * ((∑ j : Fin P.n, P.A i j * x j) - P.b i))) := by
                    simpa [add_comm, add_left_comm, add_assoc] using
                      add_le_add_left hsum (P.primalObjective x)
            _ = Q.objective x := by
                  rw [hobjective_eq x]
        have hlower : (pStar : EReal) ≤ Q.optimalValue := by
          -- Show that every logistic objective value is at least `pStar`, then take the infimum.
          rw [ConvexLogisticProgram.optimalValue]
          have hnonempty :
              (((fun x : Fin P.n → ℝ => (Q.objective x : EReal)) '' Set.univ) : Set EReal).Nonempty := by
            refine Set.image_nonempty.mpr ?_
            exact Set.univ_nonempty
          exact (le_csInf_iff'' hnonempty).2 <| by
            intro y hy
            rcases hy with ⟨x, -, rfl⟩
            have hxlowerE : (pStar : EReal) ≤ (Q.objective x : EReal) := by
              exact_mod_cast (hpointwise_lower x)
            simpa using hxlowerE
        have hobjective_feasible :
            ∀ x : Fin P.n → ℝ, P.primalFeasible x → Q.objective x ≤ P.primalObjective x + shift := by
          intro x hx
          -- On the feasible region, every residual is nonpositive, so each softplus is uniformly bounded.
          have hsum :
              ∑ i : Fin P.m,
                  (1 / Q.μ) *
                    Real.log (1 + Real.exp (Q.μ * ((∑ j : Fin P.n, P.A i j * x j) - P.b i))) ≤
                ∑ i : Fin P.m, Real.log 2 / Q.μ := by
            apply Finset.sum_le_sum
            intro i _
            have hres_nonpos : (∑ j : Fin P.n, P.A i j * x j) - P.b i ≤ 0 := by
              linarith [hx i]
            exact softplus_le_log_two_div_of_nonpos Q.μ_pos hres_nonpos
          calc
            Q.objective x =
                P.primalObjective x +
                  ∑ i : Fin P.m,
                    (1 / Q.μ) *
                      Real.log (1 + Real.exp (Q.μ * ((∑ j : Fin P.n, P.A i j * x j) - P.b i))) := by
                    rw [hobjective_eq x]
            _ ≤ P.primalObjective x + ∑ i : Fin P.m, Real.log 2 / Q.μ := by
                  simpa [add_comm, add_left_comm, add_assoc] using
                    add_le_add_left hsum (P.primalObjective x)
            _ = P.primalObjective x + shift := by
                  simp [shift, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        let primalSet : Set EReal :=
          (fun x : Fin P.n → ℝ => (P.primalObjective x : EReal)) '' {x | P.primalFeasible x}
        let shiftedSet : Set EReal :=
          (fun x : Fin P.n → ℝ => ((P.primalObjective x + shift : ℝ) : EReal)) '' {x | P.primalFeasible x}
        have hprimal_nonempty : primalSet.Nonempty := by
          rcases h_primal_feasible' with ⟨x, hx⟩
          exact ⟨(P.primalObjective x : EReal), ⟨x, hx, rfl⟩⟩
        have hshifted_nonempty : shiftedSet.Nonempty := by
          rcases h_primal_feasible' with ⟨x, hx⟩
          exact ⟨((P.primalObjective x + shift : ℝ) : EReal), ⟨x, hx, rfl⟩⟩
        have hshifted_eq :
            shiftedSet = (fun y : EReal => shiftE + y) '' primalSet := by
          ext y
          constructor
          · intro hy
            rcases hy with ⟨x, hx, rfl⟩
            refine ⟨(P.primalObjective x : EReal), ⟨x, hx, rfl⟩, ?_⟩
            simp [shiftE, shift, add_comm]
          · intro hy
            rcases hy with ⟨u, ⟨x, hx, rfl⟩, rfl⟩
            exact ⟨x, hx, by simp [shiftE, shift, add_comm]⟩
        have hupper_to_shifted : Q.optimalValue ≤ sInf shiftedSet := by
          -- `q*` lies below every feasible shifted primal value, hence below their infimum.
          have hbound :
              ∀ y ∈ shiftedSet, Q.optimalValue ≤ y := by
            intro y hy
            rcases hy with ⟨x, hx, rfl⟩
            have hq_le_obj : Q.optimalValue ≤ (Q.objective x : EReal) := by
              rw [ConvexLogisticProgram.optimalValue]
              exact csInf_le' ⟨x, Set.mem_univ x, rfl⟩
            have hobj_le_shift :
                (Q.objective x : EReal) ≤ ((P.primalObjective x + shift : ℝ) : EReal) := by
              exact_mod_cast hobjective_feasible x hx
            exact hq_le_obj.trans hobj_le_shift
          exact (le_csInf_iff'' hshifted_nonempty).2 hbound
        have hshifted_sInf :
            sInf shiftedSet = ((pStar + shift : ℝ) : EReal) := by
          -- Rewrite the shifted feasible image as an additive image of the primal objective set.
          have hp_primal_set : sInf primalSet = (pStar : EReal) := by
            simpa [primalSet, PrimalDualLinearProgram.primalOptimalValue] using hp_primal'
          have hmono : Monotone (fun y : EReal => shiftE + y) := by
            intro a b hab
            simpa [add_comm] using add_le_add_right hab shiftE
          have hcont : ContinuousAt (fun y : EReal => shiftE + y) (sInf primalSet) := by
            refine (EReal.continuousAt_add (p := (shiftE, sInf primalSet)) ?_ ?_).comp ?_
            · exact Or.inl (by simp [shiftE])
            · exact Or.inl (by simp [shiftE])
            · exact (continuous_const.continuousAt).prodMk continuous_id.continuousAt
          have hmap : shiftE + sInf primalSet = sInf shiftedSet := by
            simpa [hshifted_eq] using
              (Monotone.map_csInf_of_continuousAt (A := primalSet) hcont hmono hprimal_nonempty)
          calc
            sInf shiftedSet = shiftE + sInf primalSet := hmap.symm
            _ = shiftE + (pStar : EReal) := by rw [hp_primal_set]
            _ = ((pStar + shift : ℝ) : EReal) := by simp [shiftE, shift, add_comm]
        constructor
        · exact hlower
        · calc
            Q.optimalValue ≤ sInf shiftedSet := hupper_to_shifted
            _ = ((pStar + shift : ℝ) : EReal) := hshifted_sInf
            _ = ((pStar + (P.m : ℝ) * Real.log 2 / Q.μ : ℝ) : EReal) := by rfl
      simpa [P, Q] using hmain

end «problem-3»
