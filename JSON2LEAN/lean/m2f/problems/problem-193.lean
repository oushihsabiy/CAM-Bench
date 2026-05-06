import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-193»

/- [BLOCK Exercise 7.2 | 2 | defn]
Given a parametric family of densities or mass functions {p_θ} for observed data y, a parameter
value hatθ is a maximum-likelihood estimate if hatθ ∈ operatorname*{argmax}_{θ} p_θ(y);
equivalently, hatθ maximizes the log-likelihood log p_θ(y) over all feasible θ.
-/
def IsMaximumLikelihoodEstimate {Θ Y : Type _} (p : Θ → Y → ℝ) (feasible : Set Θ) (y : Y)
    (θhat : Θ) : Prop :=
  θhat ∈ feasible ∧ ∀ θ, θ ∈ feasible → p θ y ≤ p θhat y

/- [BLOCK Exercise 7.2 | 3 | thm]
Consider the linear measurement model y = Ax + v, where A is known, x is an unknown vector, y is
observed, and the components of v are independent and identically distributed with density
p(z)=
cases
1{2α}, & |z| ≤ α,;
0, & |z| > α,
cases
where α > 0 is unknown. Let ‖u‖_{∞} = max_i |uᵢ| for a vector u. Show that a pair (hat x, hat α) is
a maximum-likelihood estimate if and only if hat x minimizes ‖Ax-y‖_{∞} and hat α = ‖Ahat x-y‖_{∞}.
-/
open scoped BigOperators

theorem mle_uniform_noise_iff_minimizes_infNorm_residual
    {m n : ℕ} (hm : 0 < m) (A : Matrix (Fin m) (Fin n) ℝ) (y : Fin m → ℝ)
    (hres_pos :
      ∀ x : Fin n → ℝ,
        0 < sSup (Set.range fun i : Fin m => |∑ j : Fin n, A i j * x j - y i|))
    (xalpha_hat : (Fin n → ℝ) × ℝ) :
    IsMaximumLikelihoodEstimate
        (fun xa : (Fin n → ℝ) × ℝ => fun y' : Fin m → ℝ =>
          if hfeas : 0 < xa.2 ∧
              ∀ i : Fin m, |y' i - ∑ j : Fin n, A i j * xa.1 j| ≤ xa.2 then
            if hzero : xa.2 = 0 then
              if (sSup (Set.range fun i : Fin m => |y' i - ∑ j : Fin n, A i j * xa.1 j|)) = 0
              then 1 else 0
            else
              (1 / (2 * xa.2)) ^ m
          else 0)
        {xa : (Fin n → ℝ) × ℝ | 0 < xa.2}
        y
        xalpha_hat
        ↔
        ((∀ x : Fin n → ℝ,
            sSup (Set.range fun i : Fin m => |∑ j : Fin n, A i j * xalpha_hat.1 j - y i|) ≤
              sSup (Set.range fun i : Fin m => |∑ j : Fin n, A i j * x j - y i|)) ∧
          xalpha_hat.2 =
            sSup (Set.range fun i : Fin m => |∑ j : Fin n, A i j * xalpha_hat.1 j - y i|)) := by
  -- Route correction: normalize the likelihood through a single residual radius and
  -- compare it only on positive radii, where the nested `if` collapses to one branch.
  set R : (Fin n → ℝ) → ℝ :=
    fun x => sSup (Set.range fun i : Fin m => |∑ j : Fin n, A i j * x j - y i|)
  set p : ((Fin n → ℝ) × ℝ) → (Fin m → ℝ) → ℝ :=
    fun xa : (Fin n → ℝ) × ℝ => fun y' : Fin m → ℝ =>
      if hfeas : 0 < xa.2 ∧
          ∀ i : Fin m, |y' i - ∑ j : Fin n, A i j * xa.1 j| ≤ xa.2 then
        if hzero : xa.2 = 0 then
          if (sSup (Set.range fun i : Fin m => |y' i - ∑ j : Fin n, A i j * xa.1 j|)) = 0
          then 1 else 0
        else
          (1 / (2 * xa.2)) ^ m
      else 0
  have hm_ne : m ≠ 0 := Nat.ne_of_gt hm
  have i0 : Fin m := ⟨0, hm⟩
  have hR_pos : ∀ x : Fin n → ℝ, 0 < R x := by
    intro x
    simpa [R] using hres_pos x
  have hR_nonneg : ∀ x : Fin n → ℝ, 0 ≤ R x := by
    intro x
    exact (hR_pos x).le
  have hfeasible_iff :
      ∀ x : Fin n → ℝ, ∀ α : ℝ,
        (∀ i : Fin m, |y i - ∑ j : Fin n, A i j * x j| ≤ α) ↔ R x ≤ α := by
    intro x α
    constructor
    · intro hbox
      -- The pointwise box constraint makes `α` an upper bound for the residual range.
      refine csSup_le ?_ ?_
      · exact ⟨|∑ j : Fin n, A i0 j * x j - y i0|, Set.mem_range_self i0⟩
      · intro b hb
        rcases hb with ⟨i, rfl⟩
        simpa [abs_sub_comm] using hbox i
    · intro hRle i
      -- Each residual lies below the supremum radius, so the supremum bound implies feasibility.
      have hi : |∑ j : Fin n, A i j * x j - y i| ≤ R x := by
        exact le_csSup (Finite.bddAbove_range fun k : Fin m => |∑ j : Fin n, A k j * x j - y k|)
          (Set.mem_range_self i)
      exact (by simpa [abs_sub_comm] using hi.trans hRle)
  have hp_at_y :
      ∀ x : Fin n → ℝ, ∀ α : ℝ, 0 < α →
        p (x, α) y = if R x ≤ α then (1 / (2 * α)) ^ m else 0 := by
    intro x α hα
    by_cases hRle : R x ≤ α
    · -- On the feasible branch, positivity of `α` removes the degenerate `α = 0` case.
      have hbox : ∀ i : Fin m, |y i - ∑ j : Fin n, A i j * x j| ≤ α :=
        (hfeasible_iff x α).2 hRle
      have hfeas : 0 < α ∧ ∀ i : Fin m, |y i - ∑ j : Fin n, A i j * x j| ≤ α := ⟨hα, hbox⟩
      simp [p, hfeas, hα.ne', hRle]
    · -- Outside the box constraint the likelihood vanishes.
      have hnotfeas : ¬ (0 < α ∧ ∀ i : Fin m, |y i - ∑ j : Fin n, A i j * x j| ≤ α) := by
        intro hfeas
        exact hRle ((hfeasible_iff x α).1 hfeas.2)
      simp [p, hnotfeas, hRle]
  have hp_self :
      ∀ x : Fin n → ℝ, p (x, R x) y = (1 / (2 * R x)) ^ m := by
    intro x
    simpa using hp_at_y x (R x) (hR_pos x)
  constructor
  · intro hmle
    rcases hmle with ⟨hxhat_feas, hmax⟩
    have hαhat_pos : 0 < xalpha_hat.2 := hxhat_feas
    have hspecial_feas : (xalpha_hat.1, R xalpha_hat.1) ∈ {xa : (Fin n → ℝ) × ℝ | 0 < xa.2} := by
      simpa using hR_pos xalpha_hat.1
    have hspecial_le : p (xalpha_hat.1, R xalpha_hat.1) y ≤ p xalpha_hat y :=
      hmax (xalpha_hat.1, R xalpha_hat.1) hspecial_feas
    have hhat_eval :
        p xalpha_hat y =
          if R xalpha_hat.1 ≤ xalpha_hat.2 then (1 / (2 * xalpha_hat.2)) ^ m else 0 := by
      simpa using hp_at_y xalpha_hat.1 xalpha_hat.2 hαhat_pos
    have hRhat_le_alpha : R xalpha_hat.1 ≤ xalpha_hat.2 := by
      -- If the MLE pair were infeasible for its own residual radius, its likelihood would be `0`
      -- while the comparison point `(x̂, R x̂)` has strictly positive likelihood.
      by_contra hnot
      have hnonpos :
          (1 / (2 * R xalpha_hat.1)) ^ m ≤ 0 := by
        simpa [hp_self, hhat_eval, hnot] using hspecial_le
      have hpos_pow : 0 < (1 / (2 * R xalpha_hat.1)) ^ m := by
        have htwoR_pos : 0 < 2 * R xalpha_hat.1 := by
          nlinarith [hR_pos xalpha_hat.1]
        exact pow_pos (one_div_pos.mpr htwoR_pos) _
      exact (not_le_of_gt hpos_pow) hnonpos
    have halpha_le_Rhat : xalpha_hat.2 ≤ R xalpha_hat.1 := by
      -- Comparing `(x̂, R x̂)` with `(x̂, α̂)` forces `α̂` not to exceed the residual radius.
      have hpow :
          (1 / (2 * R xalpha_hat.1)) ^ m ≤ (1 / (2 * xalpha_hat.2)) ^ m := by
        simpa [hp_self, hhat_eval, hRhat_le_alpha] using hspecial_le
      have hbase :
          1 / (2 * R xalpha_hat.1) ≤ 1 / (2 * xalpha_hat.2) := by
        have hbase_nonneg : 0 ≤ 1 / (2 * xalpha_hat.2) := by
          have htwoα_pos : 0 < 2 * xalpha_hat.2 := by
            nlinarith [hαhat_pos]
          exact (one_div_pos.mpr htwoα_pos).le
        exact le_of_pow_le_pow_left₀ hm_ne hbase_nonneg hpow
      have htwomul : 2 * xalpha_hat.2 ≤ 2 * R xalpha_hat.1 := by
        have htwoR_pos : 0 < 2 * R xalpha_hat.1 := by
          nlinarith [hR_pos xalpha_hat.1]
        exact le_of_one_div_le_one_div htwoR_pos hbase
      nlinarith
    have halpha_eq : xalpha_hat.2 = R xalpha_hat.1 := le_antisymm halpha_le_Rhat hRhat_le_alpha
    refine ⟨?_, halpha_eq⟩
    intro x
    have hx_feas : (x, R x) ∈ {xa : (Fin n → ℝ) × ℝ | 0 < xa.2} := by
      simpa using hR_pos x
    have hx_le : p (x, R x) y ≤ p xalpha_hat y := hmax (x, R x) hx_feas
    have hhat_self :
        p xalpha_hat y = (1 / (2 * R xalpha_hat.1)) ^ m := by
      simpa [halpha_eq] using hhat_eval
    -- Comparing any feasible pair `(x, R x)` with the MLE pair yields the minimal-radius property.
    have hpow :
        (1 / (2 * R x)) ^ m ≤ (1 / (2 * R xalpha_hat.1)) ^ m := by
      simpa [hp_self, hhat_self] using hx_le
    have hbase : 1 / (2 * R x) ≤ 1 / (2 * R xalpha_hat.1) := by
      have hbase_nonneg : 0 ≤ 1 / (2 * R xalpha_hat.1) := by
        have htwoRhat_pos : 0 < 2 * R xalpha_hat.1 := by
          nlinarith [hR_pos xalpha_hat.1]
        exact (one_div_pos.mpr htwoRhat_pos).le
      exact le_of_pow_le_pow_left₀ hm_ne hbase_nonneg hpow
    have htwomul : 2 * R xalpha_hat.1 ≤ 2 * R x := by
      have htwoRx_pos : 0 < 2 * R x := by
        nlinarith [hR_pos x]
      exact le_of_one_div_le_one_div htwoRx_pos hbase
    nlinarith
  · rintro ⟨hmin_radius, halpha_eq⟩
    refine ⟨?_, ?_⟩
    · -- The prescribed radius is positive because every residual supremum is positive by hypothesis.
      simpa [halpha_eq] using hR_pos xalpha_hat.1
    · intro xa hxa_feas
      rcases xa with ⟨x, α⟩
      have hα_pos : 0 < α := hxa_feas
      have hαhat_pos : 0 < xalpha_hat.2 := by
        simpa [halpha_eq] using hR_pos xalpha_hat.1
      have hhat_eval_raw :
          p xalpha_hat y =
            if R xalpha_hat.1 ≤ xalpha_hat.2 then (1 / (2 * xalpha_hat.2)) ^ m else 0 := by
        simpa using hp_at_y xalpha_hat.1 xalpha_hat.2 hαhat_pos
      have hhat_eval :
          p xalpha_hat y = (1 / (2 * R xalpha_hat.1)) ^ m := by
        rw [hhat_eval_raw]
        simp [halpha_eq, R]
      have hx_eval :
          p (x, α) y = if R x ≤ α then (1 / (2 * α)) ^ m else 0 := by
        simpa using hp_at_y x α hα_pos
      by_cases hRle : R x ≤ α
      · -- In the feasible branch, radius minimality and reciprocal monotonicity bound the likelihood.
        rw [hx_eval, if_pos hRle, hhat_eval]
        have hRhat_le_alpha : R xalpha_hat.1 ≤ α := (hmin_radius x).trans hRle
        have hbase : 1 / (2 * α) ≤ 1 / (2 * R xalpha_hat.1) := by
          have htwoRhat_pos : 0 < 2 * R xalpha_hat.1 := by
            nlinarith [hR_pos xalpha_hat.1]
          apply one_div_le_one_div_of_le htwoRhat_pos
          nlinarith
        exact pow_le_pow_left₀ (by positivity) hbase m
      · -- In the infeasible branch, the competitor likelihood is exactly `0`.
        rw [hx_eval, if_neg hRle, hhat_eval]
        have hbase_nonneg : 0 ≤ 1 / (2 * R xalpha_hat.1) := by
          have htwoRhat_pos : 0 < 2 * R xalpha_hat.1 := by
            nlinarith [hR_pos xalpha_hat.1]
          exact (one_div_pos.mpr htwoRhat_pos).le
        exact pow_nonneg hbase_nonneg _


end «problem-193»
