import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-72»

-- Exercise_11_16__b_

/- [BLOCK Exercise 11.16-(b) | 28 | defn]
A cone K ⊆ ℝ^n is proper if it is convex, closed, pointed (K cap (-K) = {0}), and has nonempty
interior.
-/
abbrev ConeProper {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  (∀ ⦃x y : Fin n → ℝ⦄, x ∈ K → y ∈ K → x + y ∈ K) ∧
  (∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x : Fin n → ℝ⦄, x ∈ K → a • x ∈ K) ∧
  Convex ℝ K ∧
  IsClosed K ∧
  (K ∩ Neg.neg '' K = ({0} : Set (Fin n → ℝ))) ∧
  (interior K).Nonempty

abbrev ConeSolid {n : ℕ} (K : ProperCone ℝ (Fin n → ℝ)) : Prop :=
  ConeProper (K : Set (Fin n → ℝ))

/- [BLOCK Exercise 11.16-(b) | 29 | thm]
Let K ⊆ ℝ^n be a proper cone, and write y succ_K 0 for y ∈ int(K). Let psi : int(K) → ℝ be twice
continuously differentiable and satisfy psi(t y)=psi(y)-θ log t for all y ∈ int(K),\ t>0, where θ is
a constant. Prove that for every y succ_K 0, ∇ psi(y)=-∇^2 psi(y)y.
-/
theorem gradient_eq_neg_hessian_mul_self_of_log_homogeneous
    {n : ℕ}
    (K : ProperCone ℝ (Fin n → ℝ))
    (hK : ConeSolid K)
    (ψext : (Fin n → ℝ) → ℝ)
    (θ : ℝ)
    (hψ_smooth :
      ContDiffOn ℝ 2 ψext (interior (K : Set (Fin n → ℝ))))
    (hscale :
      ∀ (y : interior (K : Set (Fin n → ℝ))) (t : ℝ), 0 < t →
        t • (y : Fin n → ℝ) ∈ interior (K : Set (Fin n → ℝ)))
    (hψ :
      ∀ (y : interior (K : Set (Fin n → ℝ))),
        ∀ (t : ℝ), 0 < t →
          ψext (t • (y : Fin n → ℝ)) = ψext y - θ * Real.log t) :
    ∀ y : interior (K : Set (Fin n → ℝ)),
      ∀ i : Fin n,
        (fderivWithin ℝ
            ψext
            (interior (K : Set (Fin n → ℝ))) (y : Fin n → ℝ)) (Pi.single i (1 : ℝ))
        =
        -(∑ j : Fin n,
            ((fderivWithin ℝ
                (fun z : Fin n → ℝ =>
                  (fderivWithin ℝ
                    ψext
                    (interior (K : Set (Fin n → ℝ))) z) (Pi.single j (1 : ℝ)))
                (interior (K : Set (Fin n → ℝ))) (y : Fin n → ℝ)) (Pi.single i (1 : ℝ))) * y.1 j) := by
  intro y i
  let s : Set (Fin n → ℝ) := interior (K : Set (Fin n → ℝ))
  let e : Fin n → (Fin n → ℝ) := fun j => Pi.single j (1 : ℝ)
  let c : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] ℝ) := fun z => fderivWithin ℝ ψext s z
  let F : (Fin n → ℝ) → ℝ := fun z => c z z
  have _ : ConeSolid K := hK
  have hsOpen : IsOpen s := by
    change IsOpen (interior (K : Set (Fin n → ℝ)))
    simp
  have hsUnique : UniqueDiffOn ℝ s := hsOpen.uniqueDiffOn
  have hy_mem : (y : Fin n → ℝ) ∈ s := by
    change (y : Fin n → ℝ) ∈ interior (K : Set (Fin n → ℝ))
    exact y.2
  have hsUniqueAt : UniqueDiffWithinAt ℝ s (y : Fin n → ℝ) := hsUnique _ hy_mem
  -- Differentiate the scalar scaling identity along each ray to get `Dψ(w)[w] = -θ`.
  have hray_self :
      ∀ w : s, (fderivWithin ℝ ψext s (w : Fin n → ℝ)) (w : Fin n → ℝ) = -θ := by
    intro w
    let r : ℝ → (Fin n → ℝ) := fun t => t • (w : Fin n → ℝ)
    have hw_cd : ContDiffWithinAt ℝ 2 ψext s (w : Fin n → ℝ) := by
      simpa [s] using hψ_smooth.contDiffWithinAt w.2
    have hray : HasDerivWithinAt r (w : Fin n → ℝ) (Set.Ioi 0) 1 := by
      -- The derivative of the ray `t ↦ t • w` at `t = 1` is the vector `w`.
      simpa [r] using (hasDerivWithinAt_id (x := (1 : ℝ)) (s := Set.Ioi 0)).smul_const
        (w : Fin n → ℝ)
    have hcomp :
        HasDerivWithinAt (fun t => ψext (r t))
          ((fderivWithin ℝ ψext s (w : Fin n → ℝ)) (w : Fin n → ℝ)) (Set.Ioi 0) 1 := by
      -- Compose the derivative of `ψext` with the derivative of the ray.
      refine
        ((hw_cd.differentiableWithinAt (by norm_num)).hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq
          (x := 1) hray ?_ ?_)
      intro t ht
      simpa [r, s] using hscale w t ht
      simp [r]
    have hmodel : HasDerivWithinAt (fun t : ℝ => ψext (w : Fin n → ℝ) - θ * Real.log t)
        (-θ) (Set.Ioi 0) 1 := by
      -- The model side differentiates to `-θ` because `(log t)' = 1 / t` and `t = 1`.
      have hlog : HasDerivWithinAt Real.log 1 (Set.Ioi 0) 1 := by
        simpa using (Real.hasDerivAt_log one_ne_zero).hasDerivWithinAt
      simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
        (hlog.const_mul (-θ)).const_add (ψext (w : Fin n → ℝ))
    have hcomp_model :
        HasDerivWithinAt (fun t : ℝ => ψext (w : Fin n → ℝ) - θ * Real.log t)
          ((fderivWithin ℝ ψext s (w : Fin n → ℝ)) (w : Fin n → ℝ)) (Set.Ioi 0) 1 := by
      -- Replace the composed function by the given log-homogeneous formula on `Ioi 0`.
      refine hcomp.congr_of_mem ?_ (by norm_num)
      intro t ht
      simpa [r] using (hψ w t ht).symm
    have hleft :
      derivWithin (fun t : ℝ => ψext (w : Fin n → ℝ) - θ * Real.log t) (Set.Ioi 0) 1
        = (fderivWithin ℝ ψext s (w : Fin n → ℝ)) (w : Fin n → ℝ) := by
      simpa using hcomp_model.derivWithin (isOpen_Ioi.uniqueDiffWithinAt (by norm_num))
    have hright :
        derivWithin (fun t : ℝ => ψext (w : Fin n → ℝ) - θ * Real.log t) (Set.Ioi 0) 1 = -θ := by
      simpa using hmodel.derivWithin (isOpen_Ioi.uniqueDiffWithinAt (by norm_num))
    exact hleft.symm.trans hright
  have hy_ray : (c (y : Fin n → ℝ)) (y : Fin n → ℝ) = -θ := by
    simpa [c, s] using hray_self ⟨(y : Fin n → ℝ), hy_mem⟩
  have hψ_cd : ContDiffWithinAt ℝ 2 ψext s (y : Fin n → ℝ) := by
    simpa [s] using hψ_smooth.contDiffWithinAt hy_mem
  have hc_cd : ContDiffWithinAt ℝ 1 c s (y : Fin n → ℝ) := by
    -- A `C²` function has a `C¹` derivative on the open interior.
    simpa [c] using hψ_cd.fderivWithin_right hsUnique (by norm_num) hy_mem
  have hc_diff : DifferentiableWithinAt ℝ c s (y : Fin n → ℝ) :=
    hc_cd.differentiableWithinAt (by norm_num)
  have hF_eq_const : Set.EqOn F (fun _ => -θ) s := by
    intro z hz
    -- The self-application `z ↦ Dψ(z)[z]` is constant on the interior by the ray identity.
    simpa [F, c, s] using hray_self ⟨z, hz⟩
  have hF_zero : (fderivWithin ℝ F s (y : Fin n → ℝ)) (e i) = 0 := by
    -- Differentiating a constant function on the interior gives zero.
    rw [fderivWithin_congr' (f₁ := F) (f := fun _ => -θ) hF_eq_const hy_mem, fderivWithin_const_apply]
    simp
  have hexpand :
      (fderivWithin ℝ F s (y : Fin n → ℝ)) (e i)
        = (c (y : Fin n → ℝ)) (e i) + ((fderivWithin ℝ c s (y : Fin n → ℝ)).flip (y : Fin n → ℝ))
            (e i) := by
    -- Apply the product rule to `F z = c z z`.
    simpa [F, c, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      fderivWithin_id hsUniqueAt] using
      congrArg (fun L => L (e i))
        (fderivWithin_clm_apply hsUniqueAt hc_diff differentiableWithinAt_id)
  have hy_expansion : (y : Fin n → ℝ) = ∑ j : Fin n, y.1 j • e j := by
    -- Expand `y` in the standard coordinate basis.
    calc
      (y : Fin n → ℝ) = ∑ j : Fin n, Pi.single j (y.1 j) := by
        simpa using (Finset.univ_sum_single (y : Fin n → ℝ)).symm
      _ = ∑ j : Fin n, y.1 j • e j := by
        ext k
        simp [e, Finset.sum_apply, Pi.single_apply]
  have happly_const :
      ∀ j : Fin n,
        ((fderivWithin ℝ c s (y : Fin n → ℝ)) (e i)) (e j)
          =
          (fderivWithin ℝ (fun z : Fin n → ℝ => c z (e j)) s (y : Fin n → ℝ)) (e i) := by
    intro j
    -- Differentiate the evaluation map `z ↦ c z (e_j)`; the constant vector contributes no term.
    simpa [ContinuousLinearMap.flip_apply, c, fderivWithin_const_apply] using
      (congrArg (fun L => L (e i))
        (fderivWithin_clm_apply hsUniqueAt hc_diff (differentiableWithinAt_const (e j)))).symm
  have hflip_sum :
      ((fderivWithin ℝ c s (y : Fin n → ℝ)).flip (y : Fin n → ℝ)) (e i)
        =
        ∑ j : Fin n,
          ((fderivWithin ℝ (fun z : Fin n → ℝ => c z (e j)) s (y : Fin n → ℝ)) (e i)) * y.1 j := by
    -- Expand the `y`-slot linearly and then rewrite each coordinate term as a scalar derivative.
    calc
      ((fderivWithin ℝ c s (y : Fin n → ℝ)).flip (y : Fin n → ℝ)) (e i)
          = ((fderivWithin ℝ c s (y : Fin n → ℝ)) (e i)) (y : Fin n → ℝ) := by
              simp [ContinuousLinearMap.flip_apply]
      _ = ((fderivWithin ℝ c s (y : Fin n → ℝ)) (e i)) (∑ j : Fin n, y.1 j • e j) := by
            exact congrArg (((fderivWithin ℝ c s (y : Fin n → ℝ)) (e i))) hy_expansion
      _ = ∑ j : Fin n, ((fderivWithin ℝ c s (y : Fin n → ℝ)) (e i)) (y.1 j • e j) := by
            rw [map_sum]
      _ = ∑ j : Fin n, (((fderivWithin ℝ c s (y : Fin n → ℝ)) (e i)) (e j)) * y.1 j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [mul_comm]
      _ = ∑ j : Fin n,
            ((fderivWithin ℝ (fun z : Fin n → ℝ => c z (e j)) s (y : Fin n → ℝ)) (e i)) * y.1 j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [happly_const j]
  -- The derivative of the constant self-application vanishes, so the gradient equals minus the
  -- coordinate expansion of the second-derivative term.
  have hmain :
      0 =
        (c (y : Fin n → ℝ)) (e i) +
          ∑ j : Fin n,
            ((fderivWithin ℝ (fun z : Fin n → ℝ => c z (e j)) s (y : Fin n → ℝ)) (e i)) * y.1 j := by
    calc
      0 = (fderivWithin ℝ F s (y : Fin n → ℝ)) (e i) := by simpa using hF_zero.symm
      _ = (c (y : Fin n → ℝ)) (e i) +
            ((fderivWithin ℝ c s (y : Fin n → ℝ)).flip (y : Fin n → ℝ)) (e i) := hexpand
      _ = (c (y : Fin n → ℝ)) (e i) +
            ∑ j : Fin n,
              ((fderivWithin ℝ (fun z : Fin n → ℝ => c z (e j)) s (y : Fin n → ℝ)) (e i)) *
                y.1 j := by
            rw [hflip_sum]
  linarith

end «problem-72»
