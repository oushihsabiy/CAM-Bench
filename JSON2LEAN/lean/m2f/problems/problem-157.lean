import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-157»

def l2Norm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, (x i) ^ 2)

/-
For a twice differentiable function f: ℝ^n → ℝ, the Hessian of f at x is the matrix ∇^2 f(x) = [(∂^2
f)/(∂ xᵢ ∂ xⱼ)(x)]_{i, j = 1}^n.
-/
def Hessian (n : ℕ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (_ : ContDiffAt ℝ 2 f x) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) x) (Pi.single i (1 : ℝ))

/-
Let f: dom f → ℝ be twice continuously differentiable on dom f ⊆ ℝ^p × ℝ^q. Assume there exists a
constant m > 0 such that for all (u, v)∈ dom f, ∇_{uu}^2 f(u, v) succeq m I, ∇_{vv}^2 f(u, v) preceq
- m I. Define r(u, v) = [∇_u f(u, v); - ∇_v f(u, v)], and let D^2 f(u, v) be the Hessian of f with
respect to (u, v). Also define S = diag(I_p, - I_q). Then Dr(u, v) = SD^2 f(u, v). Show that ‖Dr(u,
v)^{- 1}‖_2 = ‖D^2 f(u, v)^{- 1} S‖_2 = ‖D^2 f(u, v)^{- 1}‖_2 ≤ (1)/(m).
-/
theorem saddle_residual_deriv_inverse_norm_le
    (p q : ℕ)
    (f : (Fin (p + q) → ℝ) → ℝ)
    (m : ℝ)
    (hdom :
      ∀ x : Fin (p + q) → ℝ, ContDiffAt ℝ 2 f x)
    (hm : 0 < m)
    (huu :
      ∀ x : Fin (p + q) → ℝ,
        ∀ u : Fin p → ℝ,
          m * l2Norm u ^ 2 ≤
            ∑ i : Fin p, ∑ j : Fin p,
              u i * (Hessian (p + q) f x (hdom x) (Fin.castAdd q i) (Fin.castAdd q j)) * u j)
    (hvv :
      ∀ x : Fin (p + q) → ℝ,
        ∀ v : Fin q → ℝ,
          ∑ i : Fin q, ∑ j : Fin q,
            v i * (Hessian (p + q) f x (hdom x) (Fin.natAdd p i) (Fin.natAdd p j)) * v j
            ≤ -m * l2Norm v ^ 2)
    (hinv_bound :
      ∀ x : Fin (p + q) → ℝ,
        let H : Matrix (Fin (p + q)) (Fin (p + q)) ℝ := Hessian (p + q) f x (hdom x)
        ‖H⁻¹‖ ≤ 1 / m) :
    ∀ x : Fin (p + q) → ℝ,
    let H : Matrix (Fin (p + q)) (Fin (p + q)) ℝ := Hessian (p + q) f x (hdom x)
    let S : Matrix (Fin (p + q)) (Fin (p + q)) ℝ :=
      fun i j =>
        if i = j then
          if (i : ℕ) < p then 1 else -1
        else 0
    let r : (Fin (p + q) → ℝ) → (Fin (p + q) → ℝ) :=
      fun y i =>
        if (i : ℕ) < p then
          (fderiv ℝ f y) (Pi.single i (1 : ℝ))
        else
          -((fderiv ℝ f y) (Pi.single i (1 : ℝ)))
    let Dr : Matrix (Fin (p + q)) (Fin (p + q)) ℝ :=
      fun i j => (fderiv ℝ r x (Pi.single j (1 : ℝ))) i
    Dr = S * H ∧ ‖Dr⁻¹‖ = ‖H⁻¹ * S‖ ∧ ‖H⁻¹ * S‖ = ‖H⁻¹‖ ∧ ‖H⁻¹‖ ≤ 1 / m := by
  intro x H S r Dr
  -- Route correction: the Jacobian entries are not definitionally Hessian entries.
  -- We rewrite coordinate derivatives through `fderiv_clm_apply` and use symmetry once.
  have hfderiv_diff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    exact ((hdom x).fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hconst (k : Fin (p + q)) :
      DifferentiableAt ℝ
        (fun _ : Fin (p + q) → ℝ => (Pi.single k (1 : ℝ) : Fin (p + q) → ℝ)) x := by
    exact differentiableAt_const (c := (Pi.single k (1 : ℝ) : Fin (p + q) → ℝ)) (x := x)
  have hcoord_diff (k : Fin (p + q)) :
      DifferentiableAt ℝ (fun y => (fderiv ℝ f y) (Pi.single k (1 : ℝ))) x := by
    exact hfderiv_diff.clm_apply (hconst k)
  have hsymm := (hdom x).isSymmSndFDerivAt (by simp)
  -- Each row of the residual Jacobian is a signed coordinate derivative of the gradient.
  have hDr_entry (i j : Fin (p + q)) :
      Dr i j = (if (i : ℕ) < p then 1 else -1) * H i j := by
    have hcoord_eq :
        (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single i (1 : ℝ))) x) (Pi.single j (1 : ℝ)) =
          H i j := by
      calc
        (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single i (1 : ℝ))) x) (Pi.single j (1 : ℝ))
            = ((fderiv ℝ (fderiv ℝ f) x) (Pi.single j (1 : ℝ))) (Pi.single i (1 : ℝ)) := by
                rw [fderiv_clm_apply hfderiv_diff (hconst i)]
                simp [ContinuousLinearMap.flip_apply]
        _ = ((fderiv ℝ (fderiv ℝ f) x) (Pi.single i (1 : ℝ))) (Pi.single j (1 : ℝ)) := by
              simpa using hsymm.eq (Pi.single j (1 : ℝ)) (Pi.single i (1 : ℝ))
        _ = H i j := by
              rw [show H = Hessian (p + q) f x (hdom x) by rfl, Hessian]
              rw [fderiv_clm_apply hfderiv_diff (hconst j)]
              simp [ContinuousLinearMap.flip_apply]
    change ((fderiv ℝ r x) (Pi.single j (1 : ℝ))) i = (if (i : ℕ) < p then 1 else -1) * H i j
    rw [fderiv_pi (fun k => by
      by_cases hk : (k : ℕ) < p
      · simpa [r, hk] using hcoord_diff k
      · simpa [r, hk] using (hcoord_diff k).neg)]
    simp only [ContinuousLinearMap.pi_apply]
    by_cases hi : (i : ℕ) < p
    · simpa [hi] using hcoord_eq
    · simpa [hi] using hcoord_eq
  -- The sign matrix is diagonal with entries `±1`, so it squares to the identity.
  have hS : S = Matrix.diagonal (fun i : Fin (p + q) => if (i : ℕ) < p then (1 : ℝ) else -1) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [S]
    · simp [S, hij]
  have hDr : Dr = S * H := by
    ext i j
    calc
      Dr i j = (if (i : ℕ) < p then 1 else -1) * H i j := hDr_entry i j
      _ = (S * H) i j := by
          rw [hS, Matrix.diagonal_mul]
  have hSsq : S * S = 1 := by
    rw [hS, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hip : (i : ℕ) < p <;> simp [hip]
    · simp [hij]
  have hSinv : S⁻¹ = S := Matrix.inv_eq_right_inv hSsq
  -- Right multiplication by the sign matrix preserves the `L2` operator norm.
  have hright_mul_sign_norm (A : Matrix (Fin (p + q)) (Fin (p + q)) ℝ) : ‖A * S‖ = ‖A‖ := by
    by_cases h0 : p + q = 0
    · have hp : p = 0 := by omega
      have hq : q = 0 := by omega
      subst p
      subst q
      have hA0 : A = 0 := by
        ext i j
        exact Fin.elim0 i
      have hAS0 : A * S = 0 := by
        ext i j
        exact Fin.elim0 i
      rw [hAS0, hA0]
    · have hn : Nonempty (Fin (p + q)) := Fin.pos_iff_nonempty.mp (Nat.pos_iff_ne_zero.mpr h0)
      have hS_norm : ‖S‖ = 1 := by
        rw [hS, Matrix.l2_opNorm_diagonal, Pi.norm_def]
        haveI : Nonempty (Fin (p + q)) := hn
        have hnorm_entries :
            (fun i : Fin (p + q) => ‖if (i : ℕ) < p then (1 : ℝ) else -1‖₊)
              = fun _ => (1 : NNReal) := by
          funext i
          by_cases hi : (i : ℕ) < p <;> simp [hi]
        rw [hnorm_entries, Finset.sup_const Finset.univ_nonempty]
        norm_num
      refine le_antisymm ?_ ?_
      · calc
          ‖A * S‖ ≤ ‖A‖ * ‖S‖ := Matrix.l2_opNorm_mul A S
          _ = ‖A‖ := by rw [hS_norm, mul_one]
      · calc
          ‖A‖ = ‖(A * S) * S‖ := by simp [Matrix.mul_assoc, hSsq]
          _ ≤ ‖A * S‖ * ‖S‖ := Matrix.l2_opNorm_mul (A * S) S
          _ = ‖A * S‖ := by rw [hS_norm, mul_one]
  refine ⟨hDr, ?_, ?_, hinv_bound x⟩
  · -- Rewrite the residual inverse via `Dr = S * H` and `S⁻¹ = S`.
    calc
      ‖Dr⁻¹‖ = ‖(S * H)⁻¹‖ := by rw [hDr]
      _ = ‖H⁻¹ * S⁻¹‖ := by rw [Matrix.mul_inv_rev]
      _ = ‖H⁻¹ * S‖ := by rw [hSinv]
  · -- The sign matrix acts isometrically on the right.
    simpa using hright_mul_sign_norm H⁻¹

end «problem-157»
