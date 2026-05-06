import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-147»

-- chapter5_Ex_9

/- [BLOCK chapter5 Ex.9 | 8 | thm]
Let I,E be finite index sets, and let the feasible set be X:={x∈ ℝ^n:\ cᵢ(x)≤ 0\ (i∈ I),\ cᵢ(x)=0\
(i∈ E)}, where each cᵢ:ℝ^n o ℝ is differentiable in a neighborhood of the point x. Let x∈ X be a
feasible point, and define the active inequality index set by I(x):={i∈ I:\ cᵢ(x)=0}. Define the
tangent cone of X at x by T_X(x):=≤ft{d∈ ℝ^n:\ ∃ x^k∈ X,\ ∃ tₖ>0,\ tₖ o 0,\
rac{x^k-x}{tₖ}	o d
ight}, and the linearized cone by F(x):={d∈ ℝ^n:\
abla cᵢ(x)ᵀ d≤ 0\ (i∈ I(x)),\
abla cᵢ(x)ᵀ d=0\ (i∈ E)}. Suppose that all constraint functions cᵢ (i∈ Icup E) are linear functions
at the point x; affine functions are treated as equivalent to linearization. Prove that T_X(x)=F(x).
-/
open scoped BigOperators

/-- An affine expansion around `x` identifies the Fréchet derivative with its linear part. -/
lemma affine_linearization_fderiv_apply
    {n : Type*} [Fintype n]
    (f : EuclideanSpace ℝ n → ℝ) (x d : EuclideanSpace ℝ n)
    (L : EuclideanSpace ℝ n →ₗ[ℝ] ℝ)
    (hL : ∀ y, f y = f x + L (y - x)) :
    fderiv ℝ f x d = L d := by
  let Lc : EuclideanSpace ℝ n →L[ℝ] ℝ :=
    { toLinearMap := L
      cont := L.continuous_of_finiteDimensional }
  let b : ℝ := f x - L x
  have hfun :
      f = fun y : EuclideanSpace ℝ n => Lc y + b := by
    funext y
    -- Rewrite the affine model into the standard linear-plus-constant form.
    rw [hL y]
    simp [Lc, b, sub_eq_add_neg, add_left_comm]
  have hfd :
      HasFDerivAt (fun y : EuclideanSpace ℝ n => Lc y + b) Lc x := by
    -- The derivative of a continuous linear map plus a constant is the linear map itself.
    simpa using (Lc.hasFDerivAt.add_const b)
  -- Apply the derivative formula to the direction `d`.
  calc
    fderiv ℝ f x d = fderiv ℝ (fun y : EuclideanSpace ℝ n => Lc y + b) x d := by
      rw [hfun]
    _ = Lc d := by rw [hfd.fderiv]
    _ = L d := rfl

/-- A strictly inactive affine inequality stays feasible along the inverse-step ray eventually. -/
lemma inactive_constraint_eventually_nonpositive
    {n : Type*} [Fintype n]
    (c : EuclideanSpace ℝ n → ℝ) (x d : EuclideanSpace ℝ n)
    (L : EuclideanSpace ℝ n →ₗ[ℝ] ℝ)
    (hxneg : c x < 0)
    (hL : ∀ y, c y = c x + L (y - x)) :
    ∀ᶠ k : ℕ in atTop, c (x + ((((k + 1 : ℕ) : ℝ)⁻¹)) • d) ≤ 0 := by
  have htk :
      Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
    -- Shift the standard inverse sequence so every denominator is nonzero.
    exact
      (Filter.tendsto_add_atTop_iff_nat (f := fun k : ℕ => ((k : ℝ)⁻¹)) (l := 𝓝 0) 1).2
        (tendsto_inv_atTop_nhds_zero_nat :
          Tendsto (fun k : ℕ => ((k : ℝ)⁻¹)) atTop (𝓝 0))
  have hmul :
      Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℝ)⁻¹) * L d) atTop (𝓝 0) := by
    -- Multiplying by the fixed slope keeps the limit at zero.
    simpa using htk.mul tendsto_const_nhds
  have hlim :
      Tendsto (fun k : ℕ => c (x + ((((k + 1 : ℕ) : ℝ)⁻¹)) • d)) atTop (𝓝 (c x)) := by
    have hEq :
        (fun k : ℕ => c (x + ((((k + 1 : ℕ) : ℝ)⁻¹)) • d)) =ᶠ[atTop]
          fun k : ℕ => c x + (((k + 1 : ℕ) : ℝ)⁻¹) * L d := by
      exact Filter.Eventually.of_forall fun k => by
        change c (x + ((((k + 1 : ℕ) : ℝ)⁻¹)) • d) = c x + (((k + 1 : ℕ) : ℝ)⁻¹) * L d
        -- Expand the affine constraint value along the ray.
        rw [hL (x + ((((k + 1 : ℕ) : ℝ)⁻¹)) • d)]
        simp [LinearMap.map_smul, smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm,
          add_comm]
    have hlim_aux :
        Tendsto (fun k : ℕ => c x + (((k + 1 : ℕ) : ℝ)⁻¹) * L d) atTop (𝓝 (c x)) := by
      simpa using tendsto_const_nhds.add hmul
    exact Filter.Tendsto.congr' hEq.symm hlim_aux
  have hmem : Set.Iio (0 : ℝ) ∈ 𝓝 (c x) := IsOpen.mem_nhds isOpen_Iio hxneg
  -- Once the ray values enter the open negative half-line, they are certainly nonpositive.
  exact (hlim.eventually hmem).mono fun _ hk => le_of_lt hk

theorem tangentCone_eq_linearizedCone_of_linear_constraints
    {n I E : Type*} [Fintype n] [Fintype I] [Fintype E]
    (cI : I → EuclideanSpace ℝ n → ℝ) (cE : E → EuclideanSpace ℝ n → ℝ)
    (x : EuclideanSpace ℝ n)
    (hfeasI : ∀ i, cI i x ≤ 0)
    (hfeasE : ∀ i, cE i x = 0)
    (hdiffI : ∀ i, DifferentiableAt ℝ (cI i) x)
    (hdiffE : ∀ i, DifferentiableAt ℝ (cE i) x)
    (hlinI : ∀ i, ∃ L : EuclideanSpace ℝ n →ₗ[ℝ] ℝ, ∀ y, cI i y = cI i x + L (y - x))
    (hlinE : ∀ i, ∃ L : EuclideanSpace ℝ n →ₗ[ℝ] ℝ, ∀ y, cE i y = cE i x + L (y - x))
    :
    let X : Set (EuclideanSpace ℝ n) := {y | (∀ i, cI i y ≤ 0) ∧ (∀ i, cE i y = 0)}
    {d : EuclideanSpace ℝ n |
      ∃ xk : ℕ → EuclideanSpace ℝ n, (∀ k, xk k ∈ X) ∧
        ∃ tk : ℕ → ℝ, (∀ k, 0 < tk k) ∧ Tendsto tk atTop (𝓝 0) ∧
          Tendsto (fun k => (1 / tk k) • (xk k - x)) atTop (𝓝 d)} =
    {d : EuclideanSpace ℝ n |
      (∀ i, cI i x = 0 → fderiv ℝ (cI i) x d ≤ 0) ∧
      (∀ i, fderiv ℝ (cE i) x d = 0)} := by
  classical
  dsimp
  ext d
  constructor
  · intro hd
    rcases hd with ⟨xk, hxk, tk, htk_pos, _htk_zero, hscaled⟩
    constructor
    · intro i hiActive
      rcases hlinI i with ⟨L, hL⟩
      have hderiv : fderiv ℝ (cI i) x d = L d :=
        affine_linearization_fderiv_apply (f := cI i) (x := x) (d := d) L hL
      have hpointwise : ∀ k, L ((1 / tk k) • (xk k - x)) ≤ 0 := by
        intro k
        have hxk_le : cI i (xk k) ≤ 0 := (hxk k).1 i
        have hbase : L (xk k - x) ≤ 0 := by
          -- Use feasibility of `xk k` and the active-constraint expansion.
          rw [hL (xk k), hiActive] at hxk_le
          simpa using hxk_le
        have hinv_nonneg : 0 ≤ 1 / tk k := by
          simpa [one_div] using (inv_nonneg.mpr (le_of_lt (htk_pos k)))
        -- Positive rescaling preserves nonpositivity.
        rw [LinearMap.map_smul, smul_eq_mul]
        exact mul_nonpos_of_nonneg_of_nonpos hinv_nonneg hbase
      have hlim :
          Tendsto (fun k : ℕ => L ((1 / tk k) • (xk k - x))) atTop (𝓝 (L d)) := by
        -- Pass the tangent-sequence convergence through the continuous linear map `L`.
        exact ((L.continuous_of_finiteDimensional).tendsto d).comp hscaled
      have hle : L d ≤ 0 := le_of_tendsto_of_tendsto' hlim tendsto_const_nhds hpointwise
      simpa [hderiv] using hle
    · intro i
      rcases hlinE i with ⟨L, hL⟩
      have hderiv : fderiv ℝ (cE i) x d = L d :=
        affine_linearization_fderiv_apply (f := cE i) (x := x) (d := d) L hL
      have hpointwise : ∀ k, L ((1 / tk k) • (xk k - x)) = 0 := by
        intro k
        have hxk_eq : cE i (xk k) = 0 := (hxk k).2 i
        have hbase : L (xk k - x) = 0 := by
          -- Equality constraints stay exactly zero along the feasible sequence.
          rw [hL (xk k), hfeasE i] at hxk_eq
          simpa using hxk_eq
        rw [LinearMap.map_smul, smul_eq_mul, hbase, mul_zero]
      have hlim :
          Tendsto (fun k : ℕ => L ((1 / tk k) • (xk k - x))) atTop (𝓝 (L d)) := by
        -- Again map the tangent convergence through the linear functional.
        exact ((L.continuous_of_finiteDimensional).tendsto d).comp hscaled
      have hzero :
          Tendsto (fun k : ℕ => L ((1 / tk k) • (xk k - x))) atTop (𝓝 0) := by
        -- The mapped sequence is actually identically zero.
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        exact Filter.Eventually.of_forall fun k => (hpointwise k).symm
      have hEq : L d = 0 := tendsto_nhds_unique hlim hzero
      simpa [hderiv] using hEq
  · intro hd
    rcases hd with ⟨hconeI, hconeE⟩
    let tk : ℕ → ℝ := fun k => (((k + 1 : ℕ) : ℝ)⁻¹)
    let y : ℕ → EuclideanSpace ℝ n := fun k => x + tk k • d
    have htk_pos : ∀ k, 0 < tk k := by
      intro k
      -- The shifted inverse sequence has positive terms.
      dsimp [tk]
      positivity
    have htk_zero : Tendsto tk atTop (𝓝 0) := by
      -- Shift the standard inverse sequence so it is defined everywhere.
      dsimp [tk]
      exact
        (Filter.tendsto_add_atTop_iff_nat (f := fun k : ℕ => ((k : ℝ)⁻¹)) (l := 𝓝 0) 1).2
          (tendsto_inv_atTop_nhds_zero_nat :
            Tendsto (fun k : ℕ => ((k : ℝ)⁻¹)) atTop (𝓝 0))
    have hIevent_aux :
        ∀ i ∈ (Finset.univ : Finset I), ∀ᶠ k : ℕ in atTop, cI i (y k) ≤ 0 := by
      intro i _hi
      rcases hlinI i with ⟨L, hL⟩
      have hderiv : fderiv ℝ (cI i) x d = L d :=
        affine_linearization_fderiv_apply (f := cI i) (x := x) (d := d) L hL
      by_cases hactive : cI i x = 0
      · have hLd : L d ≤ 0 := by
          -- Route correction: use the derivative-identification helper instead of reasoning
          -- directly with gradients, since the assumptions only provide affine expansions.
          have := hconeI i hactive
          simpa [hderiv] using this
        exact Filter.Eventually.of_forall fun k => by
          have htk_nonneg : 0 ≤ tk k := by positivity
          have hyk : cI i (y k) = tk k * L d := by
            -- Expand the active affine inequality exactly along the ray.
            rw [hL (y k), hactive]
            simp [y, tk, LinearMap.map_smul, smul_eq_mul, sub_eq_add_neg, add_assoc,
              add_left_comm, add_comm]
          -- Expand the active constraint and use the sign of `L d`.
          rw [hyk]
          exact mul_nonpos_of_nonneg_of_nonpos htk_nonneg hLd
      · have hxneg : cI i x < 0 := lt_of_le_of_ne (hfeasI i) hactive
        -- Strictly inactive constraints are eventually feasible along the ray.
        simpa [y, tk] using
          inactive_constraint_eventually_nonpositive (c := cI i) (x := x) (d := d) L hxneg hL
    have hIevent_univ : ∀ᶠ k : ℕ in atTop, ∀ i ∈ (Finset.univ : Finset I), cI i (y k) ≤ 0 := by
      -- Combine the finitely many inequality-eventualities into one eventual statement.
      exact (Finset.eventually_all (I := Finset.univ) (l := atTop)
        (p := fun i k => cI i (y k) ≤ 0)).2 hIevent_aux
    have hIevent : ∀ᶠ k : ℕ in atTop, ∀ i, cI i (y k) ≤ 0 := by
      filter_upwards [hIevent_univ] with k hk i
      exact hk i (by simp)
    have hEevent_aux :
        ∀ i ∈ (Finset.univ : Finset E), ∀ᶠ k : ℕ in atTop, cE i (y k) = 0 := by
      intro i _hi
      rcases hlinE i with ⟨L, hL⟩
      have hderiv : fderiv ℝ (cE i) x d = L d :=
        affine_linearization_fderiv_apply (f := cE i) (x := x) (d := d) L hL
      have hLd : L d = 0 := by
        -- Equality constraints use the same derivative-identification bridge.
        have := hconeE i
        simpa [hderiv] using this
      exact Filter.Eventually.of_forall fun k => by
        have hyk : cE i (y k) = tk k * L d := by
          -- Expand the affine equality exactly along the ray.
          rw [hL (y k), hfeasE i]
          simp [y, tk, LinearMap.map_smul, smul_eq_mul, sub_eq_add_neg, add_assoc,
            add_left_comm, add_comm]
        -- Expand the affine equality constraint along the ray.
        rw [hyk, hLd, mul_zero]
    have hEevent_univ : ∀ᶠ k : ℕ in atTop, ∀ i ∈ (Finset.univ : Finset E), cE i (y k) = 0 := by
      -- Combine the finitely many equality-eventualities into one eventual statement.
      exact (Finset.eventually_all (I := Finset.univ) (l := atTop)
        (p := fun i k => cE i (y k) = 0)).2 hEevent_aux
    have hEevent : ∀ᶠ k : ℕ in atTop, ∀ i, cE i (y k) = 0 := by
      filter_upwards [hEevent_univ] with k hk i
      exact hk i (by simp)
    have hXevent :
        ∀ᶠ k : ℕ in atTop, (∀ i, cI i (y k) ≤ 0) ∧ (∀ i, cE i (y k) = 0) := by
      -- Package the two eventual constraint families into eventual feasibility.
      filter_upwards [hIevent, hEevent] with k hkI hkE
      exact ⟨hkI, hkE⟩
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hXevent
    let xk : ℕ → EuclideanSpace ℝ n := fun k => if k < N then x else y k
    have hxk : ∀ k, xk k ∈ {y | (∀ i, cI i y ≤ 0) ∧ (∀ i, cE i y = 0)} := by
      intro k
      by_cases hk : k < N
      · -- Before the cutoff, freeze the sequence at the feasible base point `x`.
        simp [xk, hk, hfeasI, hfeasE]
      · have hk' : N ≤ k := le_of_not_gt hk
        -- After the cutoff, the inverse ray is feasible.
        simpa [xk, hk] using hN k hk'
    have hscaled_eventually :
        ∀ᶠ k : ℕ in atTop, (1 / tk k) • (xk k - x) = d := by
      refine Filter.eventually_atTop.2 ⟨N, ?_⟩
      intro k hk
      have hnot : ¬ k < N := not_lt.mpr hk
      have htk_ne : tk k ≠ 0 := ne_of_gt (htk_pos k)
      -- After the cutoff, the frozen sequence coincides with the ray and rescales exactly to `d`.
      calc
        (1 / tk k) • (xk k - x) = (1 / tk k) • (tk k • d) := by
          simp [xk, hnot, y]
        _ = ((1 / tk k) * tk k) • d := by rw [smul_smul]
        _ = d := by rw [one_div, inv_mul_cancel₀ htk_ne, one_smul]
    have hscaled_tendsto :
        Tendsto (fun k => (1 / tk k) • (xk k - x)) atTop (𝓝 d) := by
      -- An eventually constant sequence converges to its constant value.
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      exact hscaled_eventually.mono fun _ hk => hk.symm
    refine ⟨xk, hxk, tk, htk_pos, htk_zero, hscaled_tendsto⟩

end «problem-147»
