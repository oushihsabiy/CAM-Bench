import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-87»

-- Exercise_17_11

/- [BLOCK Exercise 17.11 | 19 | defn]
A function f : ℝ^n → ℝ is twice continuously differentiable if all second-order partial derivatives
of f exist and are continuous on ℝ^n; equivalently, f ∈ C^2(ℝ^n).
-/
def TwiceContinuouslyDifferentiable {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ContDiff ℝ 2 f

/- [BLOCK Exercise 17.11 | 20 | defn]
For a twice differentiable function f : ℝ^n → ℝ, the Hessian matrix at x is the matrix ∇^2 f(x) ∈
ℝ^{n×n} with entries (∇^2 f(x))_{ij} = (∂^2 f)/(∂ xᵢ ∂ xⱼ)(x).
-/
def HessianMatrix {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => iteratedFDeriv ℝ 2 f x (fun
    | 0 => Pi.single i 1
    | 1 => Pi.single j 1
    | _ => 0)

/- [BLOCK Exercise 17.11 | 21 | thm]
Let
psi(t,σ;μ)=
cases
-σ t+μ{2}t^2, & t-σ/μ≤ 0,\4pt]
-1{2μ}σ^2, & t-σ/μ>0.
cases
Assume μne 0. Prove that the second derivative of psi(t,σ;μ) with respect to t is given by
(∂^2 psi)/(∂ t^2)(t,σ;μ)=
cases
μ, & t<σ/μ,\4pt]
0, & t>σ/μ,
cases
and hence is discontinuous at t=σ/μ.
-/
theorem psi_second_derivative_piecewise
    {σ μ : ℝ} (hμ : μ ≠ 0) :
    (∀ t : ℝ,
      t < σ / μ →
        deriv
          (fun x : ℝ =>
            deriv
              (fun u : ℝ =>
                if u - σ / μ ≤ 0 then -σ * u + (μ / 2) * u^2 else -(σ^2) / (2 * μ))
              x)
          t = μ)
    ∧
    (∀ t : ℝ,
      t > σ / μ →
        deriv
          (fun x : ℝ =>
            deriv
              (fun u : ℝ =>
                if u - σ / μ ≤ 0 then -σ * u + (μ / 2) * u^2 else -(σ^2) / (2 * μ))
              x)
          t = 0)
    ∧
    ¬ ContinuousAt
      (fun t : ℝ =>
        deriv
          (fun x : ℝ =>
            deriv
              (fun u : ℝ =>
                if u - σ / μ ≤ 0 then -σ * u + (μ / 2) * u^2 else -(σ^2) / (2 * μ))
              x)
          t)
      (σ / μ) := by
  let a : ℝ := σ / μ
  let ψ : ℝ → ℝ := fun u =>
    if u - a ≤ 0 then -σ * u + (μ / 2) * u^2 else -(σ^2) / (2 * μ)
  let g : ℝ → ℝ := fun t => deriv (fun x : ℝ => deriv ψ x) t
  -- Route correction: instead of differentiating the `if` directly, switch locally to the active
  -- branch via eventual equality and then differentiate the polynomial/constant formulas.
  have hleft_formula : ∀ t : ℝ, t < a → g t = μ := by
    intro t ht
    -- Near a strict left point, the cutoff is always active, so `ψ` agrees with the quadratic
    -- branch and the second derivative reduces to an explicit polynomial calculation.
    have hψ :
        ψ =ᶠ[𝓝 t] fun u : ℝ => -σ * u + (μ / 2) * u^2 := by
      filter_upwards [Iio_mem_nhds ht] with u hu
      have hu' : u - a ≤ 0 := by
        exact sub_nonpos.mpr hu.le
      simp only [ψ, if_pos hu']
    have hquadratic_second :
        deriv (fun x : ℝ => deriv (fun u : ℝ => -σ * u + (μ / 2) * u^2) x) t = μ := by
      have hquadratic_first :
          deriv (fun u : ℝ => -σ * u + (μ / 2) * u^2) = fun x : ℝ => -σ + μ * x := by
        funext x
        have hleft : HasDerivAt (fun u : ℝ => -σ * u) (-σ) x := by
          simpa using (hasDerivAt_id' x).const_mul (-σ)
        have hright : HasDerivAt (fun u : ℝ => (μ / 2) * u^2) (μ * x) x := by
          have hpow : HasDerivAt (fun u : ℝ => u^2) (2 * x) x := by
            simpa using hasDerivAt_pow 2 x
          convert hpow.const_mul (μ / 2) using 1
          ring
        have hsum : HasDerivAt (fun u : ℝ => -σ * u + (μ / 2) * u^2) (-σ + μ * x) x := by
          simpa using hleft.add hright
        exact hsum.deriv
      rw [hquadratic_first]
      have hlinear : HasDerivAt (fun x : ℝ => -σ + μ * x) μ t := by
        have hmul : HasDerivAt (fun x : ℝ => μ * x) μ t := by
          simpa using (hasDerivAt_id' t).const_mul μ
        simpa using hmul.const_add (-σ)
      exact hlinear.deriv
    rw [show g t =
        deriv (fun x : ℝ => deriv (fun u : ℝ => -σ * u + (μ / 2) * u^2) x) t by
      unfold g
      exact hψ.deriv.deriv_eq]
    exact hquadratic_second
  have hright_formula : ∀ t : ℝ, a < t → g t = 0 := by
    intro t ht
    -- Near a strict right point, the cutoff is inactive, so `ψ` is locally constant and both
    -- derivatives vanish.
    have hψ :
        ψ =ᶠ[𝓝 t] fun _ : ℝ => -(σ^2) / (2 * μ) := by
      filter_upwards [Ioi_mem_nhds ht] with u hu
      have hu' : ¬ u - a ≤ 0 := by
        exact not_le.mpr (sub_pos.mpr hu)
      simp only [ψ, if_neg hu']
    have hconstant_second :
        deriv (fun x : ℝ => deriv (fun _ : ℝ => -(σ^2) / (2 * μ)) x) t = 0 := by
      simp
    rw [show g t =
        deriv (fun x : ℝ => deriv (fun _ : ℝ => -(σ^2) / (2 * μ)) x) t by
      unfold g
      exact hψ.deriv.deriv_eq]
    exact hconstant_second
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    have ht' : t < a := by
      simpa [a] using ht
    simpa [g, ψ, a] using hleft_formula t ht'
  · intro t ht
    have ht' : a < t := by
      simpa [a] using ht
    simpa [g, ψ, a] using hright_formula t ht'
  · change ¬ ContinuousAt g a
    intro hg_cont
    -- The left-hand formula makes `g` eventually constant with value `μ` on `𝓝[<] a`.
    have hleft_eventually : g =ᶠ[𝓝[<] a] fun _ : ℝ => μ := by
      filter_upwards [eventually_mem_nhdsWithin] with t ht
      exact hleft_formula t ht
    have hleft_tendsto : Tendsto g (𝓝[<] a) (𝓝 μ) :=
      hleft_eventually.tendsto
    have hleft_from_cont : Tendsto g (𝓝[<] a) (𝓝 (g a)) :=
      (hg_cont.continuousWithinAt (s := Set.Iio a)).tendsto
    have hga_left : g a = μ := by
      exact tendsto_nhds_unique hleft_from_cont hleft_tendsto
    -- The right-hand formula makes `g` eventually constant with value `0` on `𝓝[>] a`.
    have hright_eventually : g =ᶠ[𝓝[>] a] fun _ : ℝ => 0 := by
      filter_upwards [eventually_mem_nhdsWithin] with t ht
      exact hright_formula t ht
    have hright_tendsto : Tendsto g (𝓝[>] a) (𝓝 (0 : ℝ)) :=
      hright_eventually.tendsto
    have hright_from_cont : Tendsto g (𝓝[>] a) (𝓝 (g a)) :=
      (hg_cont.continuousWithinAt (s := Set.Ioi a)).tendsto
    have hga_right : g a = 0 := by
      exact tendsto_nhds_unique hright_from_cont hright_tendsto
    exact hμ (by simpa [hga_left] using hga_right)

/-- On the active side of the cutoff, the piecewise penalty agrees locally with its quadratic
branch. -/
lemma piecewise_eq_active_nhds
    {n : ℕ} (c : (Fin n → ℝ) → ℝ) (lam μ : ℝ) (x : Fin n → ℝ)
    (hc : TwiceContinuouslyDifferentiable c) (hcx : c x < lam / μ) :
    (fun y =>
      if c y - lam / μ ≤ 0 then -lam * c y + (μ / 2) * (c y)^2 else -(lam^2) / (2 * μ)) =ᶠ[𝓝 x]
      fun y => -lam * c y + (μ / 2) * (c y)^2 := by
  -- Continuity of `c` keeps nearby points on the same strict side of the switching surface.
  have hc2 : ContDiffAt ℝ 2 c x := hc.contDiffAt
  have hlt : {y | c y < lam / μ} ∈ 𝓝 x := by
    exact hc2.continuousAt.preimage_mem_nhds (Iio_mem_nhds hcx)
  filter_upwards [hlt] with y hy
  have hy' : c y - lam / μ ≤ 0 := sub_nonpos.mpr hy.le
  simp [hy']

/-- On the inactive side of the cutoff, the piecewise penalty agrees locally with its constant
branch. -/
lemma piecewise_eq_constant_nhds
    {n : ℕ} (c : (Fin n → ℝ) → ℝ) (lam μ : ℝ) (x : Fin n → ℝ)
    (hc : TwiceContinuouslyDifferentiable c) (hcx : lam / μ < c x) :
    (fun y =>
      if c y - lam / μ ≤ 0 then -lam * c y + (μ / 2) * (c y)^2 else -(lam^2) / (2 * μ)) =ᶠ[𝓝 x]
      fun _ : Fin n → ℝ => -(lam^2) / (2 * μ) := by
  -- Continuity of `c` keeps nearby points in the constant branch as well.
  have hc2 : ContDiffAt ℝ 2 c x := hc.contDiffAt
  have hgt : {y | lam / μ < c y} ∈ 𝓝 x := by
    exact hc2.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hcx)
  filter_upwards [hgt] with y hy
  have hy' : ¬ c y - lam / μ ≤ 0 := by
    exact not_le.mpr (sub_pos.mpr hy)
  simp [hy']

/-- The Fréchet derivative of the active quadratic branch is the expected scalar multiple of the
derivative of `c`. -/
lemma fderiv_active_branch
    {n : ℕ} (c : (Fin n → ℝ) → ℝ) (lam μ : ℝ) (x : Fin n → ℝ)
    (hc : TwiceContinuouslyDifferentiable c) :
    fderiv ℝ (fun y => -lam * c y + (μ / 2) * (c y)^2) x =
      (-lam + μ * c x) • fderiv ℝ c x := by
  -- Differentiate each polynomial term in `c` separately and collect the scalar factors.
  have hc2 : ContDiffAt ℝ 2 c x := hc.contDiffAt
  have hdiff : DifferentiableAt ℝ c x := hc2.differentiableAt (by norm_num)
  have hlinear : HasFDerivAt (fun y => -lam * c y) (-lam • fderiv ℝ c x) x := by
    exact hdiff.hasFDerivAt.const_mul (-lam)
  have hquadratic :
      HasFDerivAt (fun y => (μ / 2) * (c y)^2)
        (((μ / 2) * (2 * c x)) • fderiv ℝ c x) x := by
    have hpow : HasFDerivAt (fun y => (c y)^2) ((2 * c x) • fderiv ℝ c x) x := by
      convert hdiff.hasFDerivAt.pow 2 using 1
      ring
    convert hpow.const_mul (μ / 2) using 1
    ext v
    simp
    ring_nf
  have hsum :
      HasFDerivAt (fun y => -lam * c y + (μ / 2) * (c y)^2)
        ((-lam • fderiv ℝ c x) + (((μ / 2) * (2 * c x)) • fderiv ℝ c x)) x := by
    simpa using hlinear.add hquadratic
  convert hsum.fderiv using 1
  ext v
  simp
  ring_nf

/-- Evaluating the derivative of the derivative map on a fixed vector recovers the second
Fréchet derivative. -/
lemma fderiv_apply_const_eq_fderiv_fderiv
    {n : ℕ} {g : (Fin n → ℝ) → ℝ} {x v w : Fin n → ℝ}
    (hg2 : ContDiffAt ℝ 2 g x) :
    (fderiv ℝ (fun y => (fderiv ℝ g y) w) x) v = fderiv ℝ (fderiv ℝ g) x v w := by
  -- Differentiate the CLM-valued map `fderiv g` and then evaluate it on the fixed vector `w`.
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ g) x := (hg2.fderiv_right_succ).differentiableAt_one
  have hclm :
      fderiv ℝ (fun y => (fderiv ℝ g y) w) x =
        (fderiv ℝ (fderiv ℝ g) x).flip w := by
    simpa using
      fderiv_clm_apply (c := fderiv ℝ g) (u := fun _ : Fin n → ℝ => w) (x := x) hfdiff
        (differentiableAt_const w)
  simpa using congrArg (fun A => A v) hclm

/-- The Hessian of the active quadratic branch splits into the scaled Hessian of `c` plus the
outer product of its gradient with itself. -/
lemma hessian_active_branch_formula
    {n : ℕ} (c : (Fin n → ℝ) → ℝ) (lam μ : ℝ) (x : Fin n → ℝ)
    (hc : TwiceContinuouslyDifferentiable c) :
    HessianMatrix (fun y => -lam * c y + (μ / 2) * (c y)^2) x =
      fun i j =>
        (μ * c x - lam) * HessianMatrix c x i j +
          μ * (iteratedFDeriv ℝ 1 c x (fun _ => Pi.single i 1)) *
            (iteratedFDeriv ℝ 1 c x (fun _ => Pi.single j 1)) := by
  -- Expand the Hessian entrywise and differentiate the scalar product formula for the gradient.
  have hc2 : ContDiffAt ℝ 2 c x := hc.contDiffAt
  have hdiff : DifferentiableAt ℝ c x := hc2.differentiableAt (by norm_num)
  have hfderiv_diff : DifferentiableAt ℝ (fderiv ℝ c) x :=
    (hc2.fderiv_right_succ).differentiableAt_one
  ext i j
  let ei : Fin n → ℝ := Pi.single i 1
  let ej : Fin n → ℝ := Pi.single j 1
  have hEntry :
      (fun y : Fin n → ℝ => fderiv ℝ (fun z => -lam * c z + (μ / 2) * (c z)^2) y ej) =
        fun y => (-lam + μ * c y) * fderiv ℝ c y ej := by
    -- Evaluate the already computed first derivative on the fixed basis vector `e_j`.
    funext y
    rw [fderiv_active_branch c lam μ y hc]
    simp [ej, ContinuousLinearMap.smul_apply]
  have hcoeff_diff :
      DifferentiableAt ℝ (fun y : Fin n → ℝ => -lam + μ * c y) x := by
    exact (hdiff.const_mul μ).const_add (-lam)
  have hgrad_diff :
      DifferentiableAt ℝ (fun y : Fin n → ℝ => fderiv ℝ c y ej) x := by
    exact ((hc2.fderiv_right_succ).clm_apply contDiffAt_const).differentiableAt_one
  have hcoeff_fderiv :
      fderiv ℝ (fun y : Fin n → ℝ => -lam + μ * c y) x = μ • fderiv ℝ c x := by
    calc
      fderiv ℝ (fun y : Fin n → ℝ => -lam + μ * c y) x
          = fderiv ℝ (fun y : Fin n → ℝ => μ * c y) x := by
              rw [fderiv_const_add]
      _ = μ • fderiv ℝ c x := by
            rw [fderiv_const_mul hdiff μ]
  have hgrad_fderiv :
      fderiv ℝ (fun y : Fin n → ℝ => fderiv ℝ c y ej) x =
        (fderiv ℝ (fderiv ℝ c) x).flip ej := by
    simpa [ej] using
      fderiv_clm_apply (c := fderiv ℝ c) (u := fun _ : Fin n → ℝ => ej) (x := x)
        hfderiv_diff (differentiableAt_const ej)
  -- Route correction: differentiate the scalarized gradient entry rather than the original `if`
  -- expression, which keeps the second-derivative computation stable.
  calc
    HessianMatrix (fun y => -lam * c y + (μ / 2) * (c y)^2) x i j
        =
          fderiv ℝ
            (fun y : Fin n → ℝ => fderiv ℝ (fun z => -lam * c z + (μ / 2) * (c z)^2) y ej)
            x ei := by
              -- The Hessian entry is the derivative of the `j`-th gradient component in direction
              -- `e_i`.
              rw [show HessianMatrix (fun y => -lam * c y + (μ / 2) * (c y)^2) x i j =
                  (fderiv ℝ (fderiv ℝ (fun y => -lam * c y + (μ / 2) * (c y)^2)) x ei) ej by
                    simp [HessianMatrix, ei, ej, iteratedFDeriv_two_apply]]
              simpa [ei, ej] using
                (fderiv_apply_const_eq_fderiv_fderiv
                  (g := fun y => -lam * c y + (μ / 2) * (c y)^2) (x := x) (v := ei) (w := ej)
                  (by
                    have hactive2 :
                        ContDiffAt ℝ 2 (fun y => -lam * c y + (μ / 2) * (c y)^2) x := by
                      fun_prop
                    exact hactive2)).symm
    _ =
          fderiv ℝ (fun y : Fin n → ℝ => (-lam + μ * c y) * fderiv ℝ c y ej) x ei := by
            rw [hEntry]
    _ =
          (((-lam + μ * c x) •
              fderiv ℝ (fun y : Fin n → ℝ => fderiv ℝ c y ej) x) +
            (fderiv ℝ c x ej) • fderiv ℝ (fun y : Fin n → ℝ => -lam + μ * c y) x) ei := by
              rw [fderiv_fun_mul hcoeff_diff hgrad_diff]
    _ =
          (((-lam + μ * c x) • ((fderiv ℝ (fderiv ℝ c) x).flip ej)) +
            (fderiv ℝ c x ej) • (μ • fderiv ℝ c x)) ei := by
              rw [hgrad_fderiv, hcoeff_fderiv]
    _ =
          (μ * c x - lam) * HessianMatrix c x i j +
            μ * (iteratedFDeriv ℝ 1 c x (fun _ => Pi.single i 1)) *
              (iteratedFDeriv ℝ 1 c x (fun _ => Pi.single j 1)) := by
              have hHess :
                  ((fderiv ℝ (fderiv ℝ c) x) ei) ej = HessianMatrix c x i j := by
                simp [HessianMatrix, ei, ej, iteratedFDeriv_two_apply]
              have hFlip :
                  ((fderiv ℝ (fderiv ℝ c) x).flip ej) ei = HessianMatrix c x i j := by
                simpa [ContinuousLinearMap.flip_apply] using hHess
              have hGradI :
                  fderiv ℝ c x ei = iteratedFDeriv ℝ 1 c x (fun _ => Pi.single i 1) := by
                simp [ei, iteratedFDeriv_one_apply]
              have hGradJ :
                  fderiv ℝ c x ej = iteratedFDeriv ℝ 1 c x (fun _ => Pi.single j 1) := by
                simp [ej, iteratedFDeriv_one_apply]
              simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
                hFlip, hGradI, hGradJ]
              ring_nf

/- [BLOCK Exercise 17.11 | 22 | thm]
Let
psi(t,σ;μ)=
cases
-σ t+μ{2}t^2, & t-σ/μ≤ 0,\4pt]
-1{2μ}σ^2, & t-σ/μ>0.
cases
Assume μne 0. Also, let cᵢ:ℝ^n→ℝ be twice continuously differentiable, and let λ_i∈ℝ. Prove that the
Hessian matrix with respect to x of the function xmapsto psi(cᵢ(x),λ_i;μ) is
∇_x^2(psi(cᵢ(x),λ_i;μ))=
cases
(μ cᵢ(x)-λ_i)∇_x^2 cᵢ(x)+μ∇ cᵢ(x)∇ cᵢ(x)ᵀ, & cᵢ(x)<λ_i/μ,\6pt]
0, & cᵢ(x)≥ λ_i/μ.
cases
-/
theorem hessian_psi_comp_piecewise
    {n : ℕ} (c : (Fin n → ℝ) → ℝ) (lam μ : ℝ) (x : Fin n → ℝ)
    (hc : TwiceContinuouslyDifferentiable c) (hμ : μ ≠ 0)
    (hnot_boundary : c x ≠ lam / μ) :
    HessianMatrix
      (fun y =>
        if c y - lam / μ ≤ 0 then -lam * c y + (μ / 2) * (c y)^2 else -(lam^2) / (2 * μ))
      x
      =
    if c x < lam / μ then
      fun i j =>
        (μ * c x - lam) * HessianMatrix c x i j +
          μ * (iteratedFDeriv ℝ 1 c x (fun _ => Pi.single i 1)) *
            (iteratedFDeriv ℝ 1 c x (fun _ => Pi.single j 1))
    else 0 := by
  let _ := hμ
  let a : ℝ := lam / μ
  let F : (Fin n → ℝ) → ℝ := fun y =>
    if c y - a ≤ 0 then -lam * c y + (μ / 2) * (c y)^2 else -(lam^2) / (2 * μ)
  -- Route correction: replace the piecewise definition by the locally active or inactive branch
  -- before taking second derivatives, instead of differentiating the `if` directly.
  change HessianMatrix F x =
    if c x < lam / μ then
      fun i j =>
        (μ * c x - lam) * HessianMatrix c x i j +
          μ * (iteratedFDeriv ℝ 1 c x (fun _ => Pi.single i 1)) *
            (iteratedFDeriv ℝ 1 c x (fun _ => Pi.single j 1))
    else 0
  rcases lt_or_gt_of_ne hnot_boundary with hcx | hcx
  · have hF :
        F =ᶠ[𝓝 x] fun y => -lam * c y + (μ / 2) * (c y)^2 := by
      -- The active branch remains valid on a neighborhood of `x`.
      simpa [F, a] using piecewise_eq_active_nhds c lam μ x hc (by simpa [a] using hcx)
    have hiter :
        iteratedFDeriv ℝ 2 F x =
          iteratedFDeriv ℝ 2 (fun y => -lam * c y + (μ / 2) * (c y)^2) x := by
      exact (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hF 2).self_of_nhds
    have hH :
        HessianMatrix F x = HessianMatrix (fun y => -lam * c y + (μ / 2) * (c y)^2) x := by
      -- The Hessian only depends on the local germ of the function at `x`.
      ext i j
      dsimp [HessianMatrix]
      rw [hiter]
    rw [hH, hessian_active_branch_formula c lam μ x hc]
    simp [hcx]
  · have hF :
        F =ᶠ[𝓝 x] fun _ : Fin n → ℝ => -(lam^2) / (2 * μ) := by
      -- On the inactive side, the penalty is locally constant.
      simpa [F, a] using piecewise_eq_constant_nhds c lam μ x hc (by simpa [a] using hcx)
    have hiter :
        iteratedFDeriv ℝ 2 F x =
          iteratedFDeriv ℝ 2 (fun _ : Fin n → ℝ => -(lam^2) / (2 * μ)) x := by
      exact (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hF 2).self_of_nhds
    have hH : HessianMatrix F x = 0 := by
      -- The constant branch has vanishing second derivative.
      ext i j
      dsimp [HessianMatrix]
      rw [hiter]
      simp [iteratedFDeriv_const_of_ne]
    have hnot : ¬ c x < lam / μ := not_lt.mpr hcx.le
    simp [hH, hnot]

end «problem-87»
