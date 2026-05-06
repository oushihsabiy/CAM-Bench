import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators


namespace «problem-61»
/-
[BLOCK Exercise 9.9 | 24 | defn] Let f: ℝⁿ → ℝ be twice differentiable at x, and suppose the Hessian
∇²f(x) is invertible. The Newton decrement at x is defined by λ(x) = (∇f(x)ᵀ(∇²f(x))⁻¹∇f(x))^{1/2}.
-/
open scoped Matrix
local notation "newtonDecrementHessian" =>
  fun {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) =>
    Matrix.of fun i j : Fin n =>
      (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) x) (Pi.single i (1 : ℝ))

def newtonDecrement {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (_h_twice : ContDiffAt ℝ 2 f x)
    [Invertible (newtonDecrementHessian f x)] : ℝ :=
  let grad : Fin n → ℝ := fun i => (fderiv ℝ f x) (Pi.single i (1 : ℝ))
  let hess : Matrix (Fin n) (Fin n) ℝ := newtonDecrementHessian f x
  Real.sqrt (dotProduct grad (⅟ hess *ᵥ grad))

/-
Let f: ℝ^n → ℝ be twice differentiable at x ∈ ℝ^n, and assume that ∇^2 f(x) is positive definite.
Define the Newton decrement at x by λ(x) = (∇ f(x)ᵀ(∇^2 f(x)^{- 1}∇ f(x))^{1/2}. Show that λ(x) =
sup_{vᵀ∇^2 f(x)v = 1}(- vᵀ∇ f(x)) = sup_{vne 0} - vᵀ∇ f(x){(vᵀ∇^2 f(x)v)^{1/2}}. 9. 20
-/
theorem newtonDecrement_eq_sup_normalized_and_rayleigh_quotient
    {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hn : 0 < n)
    (h_twice : ContDiffAt ℝ 2 f x)
    [Invertible (newtonDecrementHessian f x)]
    (hpd : Matrix.PosDef (newtonDecrementHessian f x)) :
    let grad : Fin n → ℝ := fun i => (fderiv ℝ f x) (Pi.single i (1 : ℝ))
    let hess : Matrix (Fin n) (Fin n) ℝ := newtonDecrementHessian f x
    newtonDecrement f x h_twice =
      sSup {r : ℝ | ∃ v : Fin n → ℝ, dotProduct v (hess *ᵥ v) = 1 ∧ r = -dotProduct v grad} ∧
    sSup {r : ℝ | ∃ v : Fin n → ℝ, dotProduct v (hess *ᵥ v) = 1 ∧ r = -dotProduct v grad} =
      sSup
        {r : ℝ |
          ∃ v : Fin n → ℝ,
            v ≠ 0 ∧
            r = (-dotProduct v grad) / Real.sqrt (dotProduct v (hess *ᵥ v))} := by
  -- Rewrite the statement in terms of the gradient, Hessian, and its quadratic form.
  let grad : Fin n → ℝ := fun i => (fderiv ℝ f x) (Pi.single i (1 : ℝ))
  let hess : Matrix (Fin n) (Fin n) ℝ := newtonDecrementHessian f x
  let q : (Fin n → ℝ) → ℝ := fun v => dotProduct v (hess *ᵥ v)
  let S₁ : Set ℝ := {r : ℝ | ∃ v : Fin n → ℝ, q v = 1 ∧ r = -dotProduct v grad}
  let S₂ : Set ℝ :=
    {r : ℝ | ∃ v : Fin n → ℝ, v ≠ 0 ∧ r = (-dotProduct v grad) / Real.sqrt (q v)}
  change newtonDecrement f x h_twice = sSup S₁ ∧ sSup S₁ = sSup S₂
  have hsym : hessᵀ = hess := by
    simpa [hess] using hpd.isHermitian.eq
  -- The Hessian quadratic form is strictly positive on nonzero vectors and nonnegative everywhere.
  have hq_pos : ∀ {v : Fin n → ℝ}, v ≠ 0 → 0 < q v := by
    intro v hv
    simpa [q, hess] using hpd.dotProduct_mulVec_pos hv
  have hq_nonneg : ∀ v : Fin n → ℝ, 0 ≤ q v := by
    intro v
    by_cases hv : v = 0
    · simp [q, hv]
    · exact (hq_pos hv).le
  -- Record how the quadratic form behaves under scaling and how symmetry swaps the mixed term.
  have hq_smul : ∀ (a : ℝ) (v : Fin n → ℝ), q (a • v) = a ^ 2 * q v := by
    intro a v
    calc
      q (a • v) = dotProduct (a • v) (hess *ᵥ (a • v)) := rfl
      _ = dotProduct (a • v) (a • (hess *ᵥ v)) := by rw [Matrix.mulVec_smul]
      _ = a * dotProduct (a • v) (hess *ᵥ v) := by
        rw [dotProduct_smul]
        simp [smul_eq_mul]
      _ = a * (a * dotProduct v (hess *ᵥ v)) := by
        rw [smul_dotProduct]
        simp [smul_eq_mul]
      _ = a ^ 2 * q v := by
        simp [q, pow_two, mul_assoc]
  have hcross : ∀ (v w : Fin n → ℝ), dotProduct v (hess *ᵥ w) = dotProduct w (hess *ᵥ v) := by
    intro v w
    have hv : Matrix.vecMul v hess = hess *ᵥ v := by
      simpa [hsym] using (Matrix.vecMul_transpose hess v)
    calc
      dotProduct v (hess *ᵥ w) = dotProduct (Matrix.vecMul v hess) w := by
        simpa using (Matrix.dotProduct_mulVec v hess w)
      _ = dotProduct (hess *ᵥ v) w := by rw [hv]
      _ = dotProduct w (hess *ᵥ v) := by rw [dotProduct_comm]
  -- Expanding the quadratic form on translates gives the weighted Cauchy-Schwarz inequality.
  have hq_add : ∀ (v w : Fin n → ℝ),
      q (v + w) = q v + dotProduct v (hess *ᵥ w) + dotProduct w (hess *ᵥ v) + q w := by
    intro v w
    calc
      q (v + w) = dotProduct (v + w) (hess *ᵥ (v + w)) := rfl
      _ = dotProduct (v + w) (hess *ᵥ v + hess *ᵥ w) := by rw [Matrix.mulVec_add]
      _ = dotProduct v (hess *ᵥ v) + dotProduct w (hess *ᵥ v) +
            (dotProduct v (hess *ᵥ w) + dotProduct w (hess *ᵥ w)) := by
            rw [dotProduct_add, add_dotProduct, add_dotProduct]
      _ = q v + dotProduct v (hess *ᵥ w) + dotProduct w (hess *ᵥ v) + q w := by
            simp [q]
            ring
  have hq_sub : ∀ (v w : Fin n → ℝ) (t : ℝ),
      q (v - t • w) = q v - 2 * t * dotProduct v (hess *ᵥ w) + t ^ 2 * q w := by
    intro v w t
    have hneg : -(t • w) = (-t) • w := by
      ext i
      simp
    calc
      q (v - t • w) = q (v + -(t • w)) := by simp [sub_eq_add_neg]
      _ = q v + dotProduct v (hess *ᵥ (-(t • w))) + dotProduct (-(t • w)) (hess *ᵥ v) +
            q (-(t • w)) := hq_add v (-(t • w))
      _ = q v + (-t) * dotProduct v (hess *ᵥ w) + (-t) * dotProduct w (hess *ᵥ v) +
            (-t) ^ 2 * q w := by
            rw [Matrix.mulVec_neg, Matrix.mulVec_smul, dotProduct_neg, neg_dotProduct,
              dotProduct_smul, hneg, hq_smul]
            simp [smul_eq_mul]
      _ = q v - 2 * t * dotProduct v (hess *ᵥ w) + t ^ 2 * q w := by
            rw [hcross]
            ring
  -- The normalized Hessian sphere and the Rayleigh quotient parameterization describe the same set.
  have hsets : S₁ = S₂ := by
    ext r
    constructor
    · intro hr
      rcases hr with ⟨v, hv, rfl⟩
      refine ⟨v, ?_, ?_⟩
      · intro hv0
        have : q v = 0 := by simp [q, hv0]
        linarith
      · rw [(Real.sqrt_eq_one).2 hv]
        simp
    · intro hr
      rcases hr with ⟨v, hv, hr⟩
      let w : Fin n → ℝ := (Real.sqrt (q v))⁻¹ • v
      have hqv_pos : 0 < q v := hq_pos hv
      have hsqrt_ne : Real.sqrt (q v) ≠ 0 := Real.sqrt_ne_zero'.2 hqv_pos
      refine ⟨w, ?_, ?_⟩
      · calc
          q w = (Real.sqrt (q v))⁻¹ ^ 2 * q v := by
            simpa [w] using hq_smul ((Real.sqrt (q v))⁻¹) v
          _ = 1 := by
            field_simp [hsqrt_ne]
            rw [Real.sq_sqrt hqv_pos.le]
      · calc
          r = (-dotProduct v grad) / Real.sqrt (q v) := hr
          _ = -((Real.sqrt (q v))⁻¹ * dotProduct v grad) := by
            field_simp [hsqrt_ne]
          _ = -dotProduct w grad := by
            simp [w, smul_eq_mul]
  let y : Fin n → ℝ := ⅟ hess *ᵥ grad
  have hy_eval : hess *ᵥ y = grad := by
    simp [y, Matrix.mulVec_mulVec]
  have hpdInv : (⅟ hess).PosDef := by
    simpa [invOf_eq_inv, hess] using hpd.inv
  have hq_y : q y = dotProduct grad y := by
    simp [q, y, dotProduct_comm]
  have hy_nonneg : 0 ≤ dotProduct grad y := by
    by_cases hg : grad = 0
    · simp [y, hg]
    · exact le_of_lt (by simpa [y] using hpdInv.dotProduct_mulVec_pos hg)
  let lam : ℝ := Real.sqrt (dotProduct grad y)
  have hlam_nonneg : 0 ≤ lam := by
    exact Real.sqrt_nonneg _
  have hweighted : ∀ {v : Fin n → ℝ}, (dotProduct v grad) ^ 2 ≤ q v * dotProduct grad y := by
    intro v
    by_cases hg : grad = 0
    · simp [hg, y]
    · have hy_ne : y ≠ 0 := by
        intro hy0
        apply hg
        simpa [hy0] using hy_eval.symm
      have hqy_pos : 0 < q y := hq_pos hy_ne
      have hgy_pos : 0 < dotProduct grad y := by
        simpa [hq_y] using hqy_pos
      let t : ℝ := dotProduct v grad / dotProduct grad y
      have hnonneg : 0 ≤ q (v - t • y) := hq_nonneg _
      rw [hq_sub] at hnonneg
      rw [hy_eval, hq_y] at hnonneg
      simp [t] at hnonneg
      have hnonneg' := hnonneg
      field_simp [hgy_pos.ne'] at hnonneg'
      nlinarith
  have hlam_sq : lam ^ 2 = dotProduct grad y := by
    simpa [lam] using Real.sq_sqrt hy_nonneg
  -- Now build an explicit witness that attains the Newton decrement.
  have hlam_mem : lam ∈ S₁ := by
    by_cases hg : grad = 0
    · let i : Fin n := ⟨0, hn⟩
      let e : Fin n → ℝ := fun j => if j = i then 1 else 0
      have he_ne : e ≠ 0 := by
        intro he0
        have hi := congrArg (fun u : Fin n → ℝ => u i) he0
        simp [e] at hi
      have hqe_pos : 0 < q e := hq_pos he_ne
      let w : Fin n → ℝ := (Real.sqrt (q e))⁻¹ • e
      have hw_q : q w = 1 := by
        calc
          q w = (Real.sqrt (q e))⁻¹ ^ 2 * q e := by
            simpa [w] using hq_smul ((Real.sqrt (q e))⁻¹) e
          _ = 1 := by
            have hsqrt_ne : Real.sqrt (q e) ≠ 0 := Real.sqrt_ne_zero'.2 hqe_pos
            field_simp [hsqrt_ne]
            rw [Real.sq_sqrt hqe_pos.le]
      have hlam_zero : lam = 0 := by
        simp [lam, y, hg]
      refine hlam_zero ▸ ?_
      exact ⟨w, hw_q, by simp [w, hg]⟩
    · have hy_ne : y ≠ 0 := by
        intro hy0
        apply hg
        simpa [hy0] using hy_eval.symm
      have hqy_pos : 0 < q y := hq_pos hy_ne
      have hgy_pos : 0 < dotProduct grad y := by
        simpa [hq_y] using hqy_pos
      have hlam_pos : 0 < lam := by
        simpa [lam] using Real.sqrt_pos.mpr hgy_pos
      let w0 : Fin n → ℝ := -(lam)⁻¹ • y
      have hw0_q : q w0 = 1 := by
        calc
          q w0 = (-(lam)⁻¹) ^ 2 * q y := by
            simpa [w0] using hq_smul (-(lam)⁻¹) y
          _ = (-(lam)⁻¹) ^ 2 * lam ^ 2 := by
            rw [hq_y, ← hlam_sq]
          _ = 1 := by
            field_simp [hlam_pos.ne']
      have hw0_val : lam = -dotProduct w0 grad := by
        have hw0_eq : -dotProduct w0 grad = lam := by
          calc
          -dotProduct w0 grad = lam⁻¹ * dotProduct y grad := by
            simp [w0, smul_eq_mul]
          _ = lam⁻¹ * dotProduct grad y := by rw [dotProduct_comm]
          _ = lam := by
            rw [← hlam_sq]
            field_simp [hlam_pos.ne']
        exact hw0_eq.symm
      exact ⟨w0, hw0_q, hw0_val⟩
  -- The supremum is bounded above by the Newton decrement, and our witness attains it.
  have hupper : ∀ r ∈ S₁, r ≤ lam := by
    intro r hr
    rcases hr with ⟨v, hv, rfl⟩
    have hsq : (-dotProduct v grad) ^ 2 ≤ lam ^ 2 := by
      have hmain := hweighted (v := v)
      rw [hv, one_mul] at hmain
      simpa [sq_abs, ← hlam_sq] using hmain
    exact le_of_sq_le_sq hsq hlam_nonneg
  have hS1_bdd : BddAbove S₁ := ⟨lam, hupper⟩
  have hsup_eq : sSup S₁ = lam := by
    refine le_antisymm ?_ (le_csSup hS1_bdd hlam_mem)
    refine csSup_le ⟨lam, hlam_mem⟩ ?_
    exact hupper
  constructor
  · -- The first supremum is exactly the Newton decrement.
    calc
      newtonDecrement f x h_twice = lam := by
        simp [newtonDecrement, grad, hess, lam, y]
      _ = sSup S₁ := hsup_eq.symm
  · -- The second formulation is the same supremum because the parameter sets coincide.
    simp [hsets]

end «problem-61»
