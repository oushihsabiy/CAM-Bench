import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-73»
/-
For the equality - constrained problem with feasible point x, the Newton step δ x is the primal
component of a pair (δ x, nu) satisfying the KKT system [∇^2 f(x) & Aᵀ; A & 0] [δ x; nu] = [ - ∇
f(x);
0].
-/
def newtonStep
    {n m : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (xhat : Fin n → ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) : Fin n → ℝ :=
  by
    classical
    by_cases hsol :
        Nonempty
          { p : (Fin n → ℝ) × (Fin m → ℝ) //
              (∀ i : Fin n,
                (∑ j : Fin n,
                    ((fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) xhat)
                      (Pi.single i (1 : ℝ))) * p.1 j)
                  + ∑ j : Fin m, (A.transpose i j) * p.2 j
                  = -((fderiv ℝ f xhat) (Pi.single i (1 : ℝ)))) ∧
              (∀ i : Fin m, ∑ j : Fin n, A i j * p.1 j = 0) }
    · exact (Classical.choice hsol).1.1
    · exact 0

/-
The Newton decrement at x is defined by λ(x) = (- ∇ f(x)ᵀ δ x)^{1/2} = (δ xᵀ ∇^2 f(x) δ x)^{1/2},
where δ x is the Newton step at x.
-/
def newtonDecrement
    {n m : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (xhat : Fin n → ℝ)
    (_ : Matrix (Fin m) (Fin n) ℝ)
    (dx : Fin n → ℝ) : ℝ :=
  Real.sqrt (-∑ i : Fin n, ((fderiv ℝ f xhat) (Pi.single i (1 : ℝ))) * dx i)

/-
[BLOCK Exercise 8.2 | 3 | opt_prob] Consider the optimization problem minimize ∇f(x)ᵀy subject to Ay
= 0, yᵀ∇²f(x)y ≤ 1, where y ∈ ℝⁿ.
-/
structure QuadraticallyConstrainedLinearProgram where
  n : ℕ
  m : ℕ
  grad : Fin n → ℝ
  hess : Matrix (Fin n) (Fin n) ℝ
  A : Matrix (Fin m) (Fin n) ℝ

def QuadraticallyConstrainedLinearProgram.objective (P : QuadraticallyConstrainedLinearProgram) :
    (Fin P.n → ℝ) → ℝ :=
  fun y => dotProduct P.grad y

def QuadraticallyConstrainedLinearProgram.isFeasible (P : QuadraticallyConstrainedLinearProgram) :
    (Fin P.n → ℝ) → Prop :=
  fun y => P.A.mulVec y = 0 ∧ dotProduct y (P.hess.mulVec y) ≤ 1

/-
Let f: ℝⁿ → ℝ be a convex twice - differentiable function, let A ∈ ℝ^{p×n} satisfy rank(A) = p, and
let b ∈ ℝᵖ. Let x ∈ ℝⁿ satisfy Ax = b. Define the Newton step δx ∈ ℝⁿ as the x - component of the
unique solution (δx, ν) ∈ ℝⁿ × ℝᵖ of [∇²f(x) Aᵀ; A 0] [δx; ν] = [ - ∇f(x); 0]. Define the Newton
decrement by λ(x) = (- ∇f(x)ᵀ δx)^{1/2} = (δxᵀ ∇²f(x) δx)^{1/2}. Assume that [∇²f(x) Aᵀ; A 0] is
nonsingular and that λ(x) > 0. Consider the quadratically constrained linear program minimize
∇f(x)ᵀy subject to Ay = 0, yᵀ ∇²f(x) y ≤ 1, where y ∈ ℝⁿ. Prove that its unique solution is y = δx /
λ(x).
-/
set_option maxHeartbeats 1000000 in
theorem qcqp_unique_solution_eq_normalized_newton_step
    {n m : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (xhat : Fin n → ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (Δx : Fin n → ℝ)
    (hC2 : ContDiffAt ℝ 2 f xhat)
    (hconvex : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f)
    (hrank : Module.finrank ℝ (LinearMap.range A.toLin') = m)
    (hfeas : A.mulVec xhat = b)
    (hkkt_nonsingular :
      Function.Bijective
        (fun p : (Fin n → ℝ) × (Fin m → ℝ) =>
          ( (fun i : Fin n =>
                (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single i (1 : ℝ))) xhat) p.1
                  + ∑ j : Fin m, (A.transpose i j) * p.2 j),
            (fun i : Fin m => ∑ j : Fin n, A i j * p.1 j) )))
    (hstep : Δx = newtonStep f xhat A)
    (hlam_pos : 0 < newtonDecrement f xhat A Δx) :
    let P : QuadraticallyConstrainedLinearProgram :=
      { n := n
        m := m
        grad := fun i => (fderiv ℝ f xhat) (Pi.single i (1 : ℝ))
        hess := fun i j =>
          (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) xhat)
            (Pi.single i (1 : ℝ))
        A := A }
    QuadraticallyConstrainedLinearProgram.isFeasible P
        (fun i => Δx i / newtonDecrement f xhat A Δx) ∧
      (∀ z : Fin n → ℝ,
          QuadraticallyConstrainedLinearProgram.isFeasible P z →
          QuadraticallyConstrainedLinearProgram.objective P
              (fun i => Δx i / newtonDecrement f xhat A Δx) ≤
            QuadraticallyConstrainedLinearProgram.objective P z) ∧
      (∀ y : Fin n → ℝ,
          QuadraticallyConstrainedLinearProgram.isFeasible P y →
          (∀ z : Fin n → ℝ,
              QuadraticallyConstrainedLinearProgram.isFeasible P z →
              QuadraticallyConstrainedLinearProgram.objective P y ≤
                QuadraticallyConstrainedLinearProgram.objective P z) →
          y = (fun i => Δx i / newtonDecrement f xhat A Δx)) := by
  classical
  let g : Fin n → ℝ := fun i => (fderiv ℝ f xhat) (Pi.single i (1 : ℝ))
  let H : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) xhat)
      (Pi.single i (1 : ℝ))
  let lam : ℝ := newtonDecrement f xhat A Δx
  let _ := hrank
  let _ := hfeas
  -- Upgrade `C²` regularity to differentiability of the gradient field itself.
  have htwo_ne_zero : (2 : WithTop ℕ∞) ≠ 0 := by
    norm_num
  have hfderiv : DifferentiableAt ℝ (fun y => fderiv ℝ f y) xhat := by
    exact
      (hC2.fderiv_right (m := 1) (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  -- Rewrite coordinate second derivatives through the derivative of the gradient map.
  have hcoord_fderiv :
      ∀ i : Fin n,
        fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single i (1 : ℝ))) xhat =
          (fderiv ℝ (fun y => fderiv ℝ f y) xhat).flip (Pi.single i (1 : ℝ)) := by
    intro i
    simpa using
      (fderiv_clm_apply (x := xhat) hfderiv
        (differentiableAt_const (Pi.single i (1 : ℝ) : Fin n → ℝ))
      )
  -- The same `clm_apply` rewrite works for any fixed direction.
  have happly_fderiv :
      ∀ u : Fin n → ℝ,
        fderiv ℝ (fun y => (fderiv ℝ f y) u) xhat =
          (fderiv ℝ (fun y => fderiv ℝ f y) xhat).flip u := by
    intro u
    simpa using
      (fderiv_clm_apply (x := xhat) hfderiv (differentiableAt_const u))
  -- The coordinate Hessian is symmetric because `f` is `C²` at `xhat`.
  have hHsym : ∀ i j : Fin n, H i j = H j i := by
    intro i j
    have hsnd : IsSymmSndFDerivAt ℝ f xhat :=
      hC2.isSymmSndFDerivAt (n := 2) (by norm_num)
    calc
      H i j
          = ((fderiv ℝ (fun y => fderiv ℝ f y) xhat) (Pi.single i (1 : ℝ)))
              (Pi.single j (1 : ℝ)) := by
                simp [H, hcoord_fderiv]
      _ = ((fderiv ℝ (fun y => fderiv ℝ f y) xhat) (Pi.single j (1 : ℝ)))
            (Pi.single i (1 : ℝ)) := hsnd.eq (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ))
      _ = H j i := by
            simp [H, hcoord_fderiv]
  -- Expand directional derivatives in the standard basis of `Fin n → ℝ`.
  have hcoord_expand :
      ∀ i : Fin n, ∀ v : Fin n → ℝ,
        (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single i (1 : ℝ))) xhat) v =
          ∑ j : Fin n,
            (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single i (1 : ℝ))) xhat)
              (Pi.single j (1 : ℝ)) * v j := by
    intro i v
    have hv : v = ∑ j : Fin n, v j • (Pi.single j (1 : ℝ) : Fin n → ℝ) := by
      ext j
      simp [Pi.single_apply]
    rw [hv]
    simp [map_sum, Pi.single_apply, mul_comm]
  -- Route correction: `newtonStep` is written using the transpose convention for the Hessian
  -- coordinates, so we explicitly rewrite the directional derivative into the file's matrix form.
  have hcoord_as_mulVec :
      ∀ i : Fin n, ∀ v : Fin n → ℝ,
        (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single i (1 : ℝ))) xhat) v =
          ∑ j : Fin n, H i j * v j := by
    intro i v
    calc
      (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single i (1 : ℝ))) xhat) v
          = ∑ j : Fin n,
              (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single i (1 : ℝ))) xhat)
                (Pi.single j (1 : ℝ)) * v j := hcoord_expand i v
      _ = ∑ j : Fin n, H i j * v j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            have hentry :
                (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single i (1 : ℝ))) xhat)
                    (Pi.single j (1 : ℝ)) = H i j := by
              simpa [H] using hHsym j i
            rw [hentry]
  -- Package the chosen Newton step as an actual KKT witness in matrix-vector form.
  have hkkt :
      ∃ ν : Fin m → ℝ, H *ᵥ Δx + A.transpose *ᵥ ν = -g ∧ A *ᵥ Δx = 0 := by
    have hs :
        Nonempty
          { p : (Fin n → ℝ) × (Fin m → ℝ) //
              (∀ i : Fin n,
                (∑ j : Fin n, H i j * p.1 j) + ∑ j : Fin m, (A.transpose i j) * p.2 j = -g i) ∧
              (∀ i : Fin m, ∑ j : Fin n, A i j * p.1 j = 0) } := by
      rcases hkkt_nonsingular.surjective (-g, 0) with ⟨p, hp⟩
      refine ⟨⟨p, ?_, ?_⟩⟩
      · intro i
        have hi := congrFun (Prod.mk.inj hp).1 i
        calc
          (∑ j : Fin n, H i j * p.1 j) + ∑ j : Fin m, (A.transpose i j) * p.2 j
              = (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single i (1 : ℝ))) xhat) p.1
                  + ∑ j : Fin m, (A.transpose i j) * p.2 j := by
                    rw [hcoord_as_mulVec i p.1]
          _ = -g i := by simpa [g] using hi
      · intro i
        have hi := congrFun (Prod.mk.inj hp).2 i
        simpa using hi
    -- Route correction: `newtonStep` stores the symmetric Hessian in explicit matrix entries,
    -- so we unfold the definition and read the chosen witness back in that convention.
    unfold newtonStep at hstep
    split_ifs at hstep with hsol
    · refine ⟨(Classical.choice hsol).1.2, ?_, ?_⟩
      · ext i
        have hi := (Classical.choice hsol).2.1 i
        simpa [Matrix.mulVec, g, H, hstep] using hi
      · ext i
        have hi := (Classical.choice hsol).2.2 i
        simpa [Matrix.mulVec, hstep] using hi
    · exact (hsol hs).elim
  -- The coordinate symmetry upgrades the Hessian matrix to a Hermitian matrix over `ℝ`.
  have hHherm : H.IsHermitian := by
    ext i j
    exact hHsym j i
  -- Identify the quadratic Hessian form with the second derivative of the line restriction.
  have hquad_eq_second :
      ∀ v : Fin n → ℝ,
        ((fderiv ℝ (fun y => (fderiv ℝ f y) v) xhat) v) = dotProduct v (H *ᵥ v) := by
    intro v
    have hv : v = ∑ i : Fin n, v i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
      ext i
      simp [Pi.single_apply]
    calc
      ((fderiv ℝ (fun y => (fderiv ℝ f y) v) xhat) v)
          = ((fderiv ℝ (fun y => fderiv ℝ f y) xhat) v) v := by
              rw [happly_fderiv v]
              rfl
      _ = ∑ i : Fin n,
            v i * (((fderiv ℝ (fun y => fderiv ℝ f y) xhat) v) (Pi.single i (1 : ℝ))) := by
              nth_rewrite 2 [hv]
              simp [map_sum]
      _ = ∑ i : Fin n,
            v i * (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single i (1 : ℝ))) xhat) v := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [hcoord_fderiv]
      _ = ∑ i : Fin n, v i * ∑ j : Fin n, H i j * v j := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hcoord_as_mulVec i v]
      _ = dotProduct v (H *ᵥ v) := by
            simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
  -- Restricting to affine lines turns convexity into nonnegativity of the Hessian quadratic form.
  have hHquad_nonneg : ∀ v : Fin n → ℝ, 0 ≤ dotProduct v (H *ᵥ v) := by
    intro v
    let line : ℝ → Fin n → ℝ := AffineMap.lineMap xhat (xhat + v)
    let φ : ℝ → ℝ := f ∘ line
    let ψ : ℝ → ℝ := fun t => (fderiv ℝ f (line t)) v
    -- Work on a small open interval on which `f` is still `C²`.
    obtain ⟨u, hu_open, hx_u, huC2⟩ := hC2.contDiffOn' (m := 2) le_rfl (by simp)
    have hline_mem : line 0 ∈ u := by
      simpa [line, AffineMap.lineMap_apply_zero] using hx_u
    have hpre : line ⁻¹' u ∈ 𝓝 (0 : ℝ) := by
      exact hu_open.mem_nhds hline_mem |> AffineMap.lineMap_continuous.continuousAt.preimage_mem_nhds
    rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hεpos, hεsub⟩
    let S : Set ℝ := Metric.ball 0 ε
    have h0S : (0 : ℝ) ∈ S := by
      simp [S, hεpos]
    have hSsubset : S ⊆ line ⁻¹' u := hεsub
    have hφ_convex : ConvexOn ℝ Set.univ φ := by
      simpa [φ, line] using hconvex.comp_affineMap (AffineMap.lineMap xhat (xhat + v))
    have hφ_convexS : ConvexOn ℝ S φ := by
      refine ⟨convex_ball (0 : ℝ) ε, ?_⟩
      intro x hx y hy a b ha hb hab
      exact hφ_convex.2 (by simp) (by simp) ha hb hab
    -- On this interval, the line restriction is differentiable and its derivative is exactly `ψ`.
    have hφ_diff : ∀ t ∈ S, DifferentiableAt ℝ φ t := by
      intro t ht
      have htu : line t ∈ u := hSsubset ht
      have hf_t : DifferentiableAt ℝ f (line t) := by
        have hmem : insert xhat (Set.univ : Set (Fin n → ℝ)) ∩ u ∈ 𝓝 (line t) := by
          simpa using hu_open.mem_nhds htu
        exact ((huC2 (line t) ⟨by simp, htu⟩).contDiffAt hmem).differentiableAt
          htwo_ne_zero
      have hline_t : HasDerivAt line v t := by
        simpa [line] using
          (AffineMap.hasDerivAt_lineMap (a := xhat) (b := xhat + v) (x := t))
      exact (hf_t.hasFDerivAt.comp_hasDerivAt (x := t) hline_t).differentiableAt
    have hφ_deriv_eq : ∀ t ∈ S, deriv φ t = ψ t := by
      intro t ht
      have htu : line t ∈ u := hSsubset ht
      have hf_t : DifferentiableAt ℝ f (line t) := by
        have hmem : insert xhat (Set.univ : Set (Fin n → ℝ)) ∩ u ∈ 𝓝 (line t) := by
          simpa using hu_open.mem_nhds htu
        exact ((huC2 (line t) ⟨by simp, htu⟩).contDiffAt hmem).differentiableAt
          htwo_ne_zero
      have hline_t : HasDerivAt line v t := by
        simpa [line] using
          (AffineMap.hasDerivAt_lineMap (a := xhat) (b := xhat + v) (x := t))
      have hderiv_t : HasDerivAt φ ((fderiv ℝ f (line t)) v) t := by
        simpa [φ, ψ] using (hf_t.hasFDerivAt.comp_hasDerivAt (x := t) hline_t)
      exact hderiv_t.deriv
    have hpsi_mono : MonotoneOn ψ S := by
      have hmono_deriv : MonotoneOn (deriv φ) S := hφ_convexS.monotoneOn_deriv hφ_diff
      intro s hs t ht hst
      rw [← hφ_deriv_eq s hs, ← hφ_deriv_eq t ht]
      exact hmono_deriv hs ht hst
    -- Differentiate `ψ` at the origin and identify that derivative with the Hessian quadratic form.
    have hψ_base : DifferentiableAt ℝ (fun y => (fderiv ℝ f y) v) xhat := by
      simpa using hfderiv.clm_apply (differentiableAt_const v)
    have hline0 : HasDerivAt line v 0 := by
      simpa [line] using
        (AffineMap.hasDerivAt_lineMap (a := xhat) (b := xhat + v) (x := (0 : ℝ)))
    have hψ_deriv :
        HasDerivAt ψ ((fderiv ℝ (fun y => (fderiv ℝ f y) v) xhat) v) 0 := by
      have hbase :
          HasFDerivAt (fun y => (fderiv ℝ f y) v)
            (fderiv ℝ (fun y => (fderiv ℝ f y) v) xhat) (line 0) := by
        simpa [line, AffineMap.lineMap_apply_zero] using hψ_base.hasFDerivAt
      simpa [ψ] using hbase.comp_hasDerivAt (x := (0 : ℝ)) hline0
    have hwithin :
        derivWithin ψ S 0 = ((fderiv ℝ (fun y => (fderiv ℝ f y) v) xhat) v) :=
      hψ_deriv.hasDerivWithinAt.derivWithin
        (IsOpen.uniqueDiffWithinAt Metric.isOpen_ball h0S)
    have hnonneg_second :
        0 ≤ ((fderiv ℝ (fun y => (fderiv ℝ f y) v) xhat) v) := by
      simpa [hwithin] using (hpsi_mono.derivWithin_nonneg (x := (0 : ℝ)))
    simpa [hquad_eq_second v] using hnonneg_second
  have hHpsd : H.PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHherm hHquad_nonneg
  let q : (Fin n → ℝ) → ℝ := fun x => dotProduct x (H *ᵥ x)
  have hHtranspose : H.transpose = H := by
    ext i j
    exact hHsym j i
  -- Symmetry lets us swap the mixed Hessian pairing.
  have hcross : ∀ x z : Fin n → ℝ, dotProduct x (H *ᵥ z) = dotProduct z (H *ᵥ x) := by
    intro x z
    have hx : Matrix.vecMul x H = H *ᵥ x := by
      simpa [hHtranspose] using (Matrix.vecMul_transpose H x)
    calc
      dotProduct x (H *ᵥ z) = dotProduct (Matrix.vecMul x H) z := by
        simpa using (Matrix.dotProduct_mulVec x H z)
      _ = dotProduct (H *ᵥ x) z := by rw [hx]
      _ = dotProduct z (H *ᵥ x) := by rw [dotProduct_comm]
  -- The Hessian quadratic form scales quadratically.
  have hq_smul : ∀ (a : ℝ) (x : Fin n → ℝ), q (a • x) = a ^ 2 * q x := by
    intro a x
    calc
      q (a • x) = dotProduct (a • x) (H *ᵥ (a • x)) := rfl
      _ = dotProduct (a • x) (a • (H *ᵥ x)) := by rw [Matrix.mulVec_smul]
      _ = a * dotProduct (a • x) (H *ᵥ x) := by
            rw [dotProduct_smul]
            simp [smul_eq_mul]
      _ = a * (a * dotProduct x (H *ᵥ x)) := by rw [smul_dotProduct]; simp [smul_eq_mul]
      _ = a ^ 2 * q x := by simp [q, pow_two, mul_assoc]
  -- Expanding the quadratic form on sums exposes the mixed Hessian pairing.
  have hq_add :
      ∀ x z : Fin n → ℝ,
        q (x + z) = q x + dotProduct x (H *ᵥ z) + dotProduct z (H *ᵥ x) + q z := by
    intro x z
    calc
      q (x + z) = dotProduct (x + z) (H *ᵥ (x + z)) := rfl
      _ = dotProduct (x + z) (H *ᵥ x + H *ᵥ z) := by rw [Matrix.mulVec_add]
      _ = dotProduct x (H *ᵥ x) + dotProduct z (H *ᵥ x) +
            (dotProduct x (H *ᵥ z) + dotProduct z (H *ᵥ z)) := by
              rw [dotProduct_add, add_dotProduct, add_dotProduct]
      _ = q x + dotProduct x (H *ᵥ z) + dotProduct z (H *ᵥ x) + q z := by
            simp [q]
            ring
  -- The translated quadratic form is the square-completion identity used for optimality.
  have hq_sub :
      ∀ x z : Fin n → ℝ, ∀ a : ℝ,
        q (x - a • z) = q x - 2 * a * dotProduct x (H *ᵥ z) + a ^ 2 * q z := by
    intro x z a
    calc
      q (x - a • z) = q (x + (-a) • z) := by simp [sub_eq_add_neg]
      _ = q x + dotProduct x (H *ᵥ ((-a) • z)) + dotProduct ((-a) • z) (H *ᵥ x) +
            q ((-a) • z) := hq_add x ((-a) • z)
      _ = q x + (-a) * dotProduct x (H *ᵥ z) + (-a) * dotProduct z (H *ᵥ x) +
            (-a) ^ 2 * q z := by
              rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, hq_smul]
              simp [smul_eq_mul]
      _ = q x - 2 * a * dotProduct x (H *ᵥ z) + a ^ 2 * q z := by
            rw [hcross]
            ring
  -- A feasible vector with zero quadratic form lies in the kernel of the KKT matrix.
  have hkernel :
      ∀ w : Fin n → ℝ, A *ᵥ w = 0 → q w = 0 → w = 0 := by
    intro w hAw hqw
    have hw_ortho : ∀ z : Fin n → ℝ, dotProduct w (H *ᵥ z) = 0 := by
      intro z
      let c : ℝ := dotProduct w (H *ᵥ z)
      by_cases hc : c = 0
      · simpa [c] using hc
      · let t : ℝ := -c / (q z + 1)
        have ht_nonneg : 0 ≤ q z := by
          simpa [q] using hHpsd.dotProduct_mulVec_nonneg z
        have hqt_nonneg : 0 ≤ q (w + t • z) := by
          simpa [q] using hHpsd.dotProduct_mulVec_nonneg (w + t • z)
        have hqt : q (w + t • z) = 2 * t * c + t ^ 2 * q z := by
          calc
            q (w + t • z)
                = q w + dotProduct w (H *ᵥ (t • z)) + dotProduct (t • z) (H *ᵥ w) + q (t • z) := by
                    simpa using hq_add w (t • z)
            _ = 2 * t * c + t ^ 2 * q z := by
                  rw [hqw, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, hq_smul]
                  simp [c, smul_eq_mul, hcross]
                  ring
        have hden_pos : 0 < q z + 1 := by linarith
        have hden_ne : q z + 1 ≠ 0 := ne_of_gt hden_pos
        rw [hqt] at hqt_nonneg
        simp [t, div_pow] at hqt_nonneg
        field_simp [hden_ne] at hqt_nonneg
        have hc_sq_pos : 0 < c ^ 2 := by
          nlinarith [sq_pos_of_ne_zero hc]
        nlinarith
    have hHw : H *ᵥ w = 0 := by
      ext i
      have hi : dotProduct (Pi.single i (1 : ℝ) : Fin n → ℝ) (H *ᵥ w) = 0 := by
        have hi' := hw_ortho (Pi.single i (1 : ℝ) : Fin n → ℝ)
        rw [hcross] at hi'
        simpa using hi'
      simpa [dotProduct, Pi.single_apply, Matrix.mulVec] using hi
    have hpair :
        (w, (0 : Fin m → ℝ)) = (0, (0 : Fin m → ℝ)) := by
      apply hkkt_nonsingular.injective
      ext i
      · simpa [hcoord_as_mulVec, Matrix.mulVec] using congrFun hHw i
      · simpa [Matrix.mulVec] using congrFun hAw i
    exact Prod.mk.inj hpair |>.1
  -- Route correction: the remaining work is done entirely in the raw `(g, H, q, A, lam)` language,
  -- and only the final line repackages those facts into the QCQP record.
  rcases hkkt with ⟨ν, hν1, hν2⟩
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  -- Dotting the KKT equation with `Δx` identifies the Newton decrement with the Hessian quadratic form.
  have hstep_quadratic :
      q Δx = lam ^ 2 ∧ dotProduct g Δx = -(lam ^ 2) := by
    have htranspose_zero : dotProduct Δx (A.transpose *ᵥ ν) = 0 := by
      calc
        dotProduct Δx (A.transpose *ᵥ ν)
            = dotProduct (Matrix.vecMul Δx A.transpose) ν := by
                simpa using (Matrix.dotProduct_mulVec Δx A.transpose ν)
        _ = dotProduct (A *ᵥ Δx) ν := by
              simpa using congrArg (fun v => dotProduct v ν) (Matrix.vecMul_transpose A Δx)
        _ = 0 := by simp [hν2]
    have hq_eq_neg_obj : q Δx = -dotProduct g Δx := by
      have hdot := congrArg (fun v => dotProduct Δx v) hν1
      simpa [dotProduct_add, htranspose_zero, q, dotProduct_comm] using hdot
    have hq_nonneg : 0 ≤ q Δx := by
      simpa [q] using hHpsd.dotProduct_mulVec_nonneg Δx
    have hsqrt_sq : lam ^ 2 = -dotProduct g Δx := by
      have hobj_nonneg : 0 ≤ -dotProduct g Δx := by
        linarith [hq_eq_neg_obj, hq_nonneg]
      rw [show lam = Real.sqrt (-dotProduct g Δx) by
            simp [lam, newtonDecrement, g, dotProduct]]
      exact Real.sq_sqrt hobj_nonneg
    constructor
    · linarith
    · linarith
  have hqΔ : q Δx = lam ^ 2 := hstep_quadratic.1
  have hgΔ : dotProduct g Δx = -(lam ^ 2) := hstep_quadratic.2
  -- Feasible directions eliminate the transpose term in the KKT equation and rewrite the objective.
  have hobjective_of_feasible :
      ∀ z : Fin n → ℝ, A *ᵥ z = 0 → dotProduct g z = -dotProduct Δx (H *ᵥ z) := by
    intro z hAz
    have htranspose_zero : dotProduct z (A.transpose *ᵥ ν) = 0 := by
      calc
        dotProduct z (A.transpose *ᵥ ν)
            = dotProduct (Matrix.vecMul z A.transpose) ν := by
                simpa using (Matrix.dotProduct_mulVec z A.transpose ν)
        _ = dotProduct (A *ᵥ z) ν := by
              simpa using congrArg (fun v => dotProduct v ν) (Matrix.vecMul_transpose A z)
        _ = 0 := by simp [hAz]
    have hdot := congrArg (fun v => dotProduct z v) hν1
    have hraw : dotProduct z (H *ᵥ Δx) = -dotProduct g z := by
      simpa [dotProduct_add, htranspose_zero, dotProduct_comm] using hdot
    calc
      dotProduct g z = -dotProduct z (H *ᵥ Δx) := by linarith
      _ = -dotProduct Δx (H *ᵥ z) := by rw [hcross]
  -- Completing the square at `Δx - lam • z` gives the global optimality inequality.
  have hnormalized_step_optimal_raw :
      ∀ z : Fin n → ℝ,
        A *ᵥ z = 0 → q z ≤ 1 → dotProduct g (lam⁻¹ • Δx) ≤ dotProduct g z := by
    intro z hAz hqz
    let c : ℝ := dotProduct Δx (H *ᵥ z)
    have hq_nonneg : 0 ≤ q (Δx - lam • z) := by
      simpa [q] using hHpsd.dotProduct_mulVec_nonneg (Δx - lam • z)
    have hq_upper : q (Δx - lam • z) ≤ 2 * lam * (lam - c) := by
      rw [hq_sub, hqΔ]
      simp [c]
      nlinarith
    have hc_le : c ≤ lam := by
      have hbound : 0 ≤ 2 * lam * (lam - c) := by
        linarith
      nlinarith [hlam_pos, hbound]
    have hcandidate_obj : dotProduct g (lam⁻¹ • Δx) = -lam := by
      calc
        dotProduct g (lam⁻¹ • Δx) = lam⁻¹ * dotProduct g Δx := by
          rw [dotProduct_smul]
          simp [smul_eq_mul]
        _ = lam⁻¹ * (-(lam ^ 2)) := by rw [hgΔ]
        _ = -lam := by
              have hinv : lam⁻¹ * lam = 1 := by
                field_simp [hlam_ne]
              calc
                lam⁻¹ * (-(lam ^ 2)) = -((lam⁻¹ * lam) * lam) := by ring
                _ = -lam := by simp [hinv]
    have hz_obj : dotProduct g z = -c := by
      simpa [c] using hobjective_of_feasible z hAz
    linarith
  -- The normalized Newton step is feasible because the linear constraint is homogeneous and
  -- the quadratic form rescales to `1`.
  have hnormalized_step_feasible :
      A *ᵥ (lam⁻¹ • Δx) = 0 ∧ q (lam⁻¹ • Δx) ≤ 1 := by
    constructor
    · rw [Matrix.mulVec_smul, hν2, smul_zero]
    · have hq_norm : q (lam⁻¹ • Δx) = 1 := by
        calc
          q (lam⁻¹ • Δx) = (lam⁻¹) ^ 2 * q Δx := hq_smul (lam⁻¹) Δx
          _ = (lam⁻¹) ^ 2 * lam ^ 2 := by rw [hqΔ]
          _ = 1 := by
                have hinv : lam⁻¹ * lam = 1 := by
                  field_simp [hlam_ne]
                calc
                  (lam⁻¹) ^ 2 * lam ^ 2 = (lam⁻¹ * lam) * (lam⁻¹ * lam) := by ring
                  _ = 1 := by simp [hinv]
      linarith
  -- Equality in the optimality inequality forces zero gap in the square-completion estimate.
  have hzero_gap_of_optimality :
      ∀ y : Fin n → ℝ,
        A *ᵥ y = 0 →
        q y ≤ 1 →
        dotProduct g y = -lam →
        q (Δx - lam • y) = 0 := by
    intro y hAy hqy hgy
    have hcross_eq : dotProduct Δx (H *ᵥ y) = lam := by
      have hy_obj := hobjective_of_feasible y hAy
      linarith
    have hq_nonneg : 0 ≤ q (Δx - lam • y) := by
      simpa [q] using hHpsd.dotProduct_mulVec_nonneg (Δx - lam • y)
    have hq_nonpos : q (Δx - lam • y) ≤ 0 := by
      rw [hq_sub, hqΔ, hcross_eq]
      nlinarith
    linarith
  -- Package the raw feasibility, optimality, and equality-case uniqueness back into the QCQP goal.
  have hfinal_raw :
      (A *ᵥ (lam⁻¹ • Δx) = 0 ∧ q (lam⁻¹ • Δx) ≤ 1) ∧
        (∀ z : Fin n → ℝ, (A *ᵥ z = 0 ∧ q z ≤ 1) →
          dotProduct g (lam⁻¹ • Δx) ≤ dotProduct g z) ∧
        (∀ y : Fin n → ℝ, (A *ᵥ y = 0 ∧ q y ≤ 1) →
          (∀ z : Fin n → ℝ, (A *ᵥ z = 0 ∧ q z ≤ 1) → dotProduct g y ≤ dotProduct g z) →
          y = lam⁻¹ • Δx) := by
    constructor
    · exact hnormalized_step_feasible
    constructor
    · intro z hz
      exact hnormalized_step_optimal_raw z hz.1 hz.2
    · intro y hy hy_opt
      have hy_lower := hnormalized_step_optimal_raw y hy.1 hy.2
      have hy_upper := hy_opt (lam⁻¹ • Δx) hnormalized_step_feasible
      have hy_eq_obj : dotProduct g y = dotProduct g (lam⁻¹ • Δx) := by
        linarith
      have hcandidate_obj : dotProduct g (lam⁻¹ • Δx) = -lam := by
        calc
          dotProduct g (lam⁻¹ • Δx) = lam⁻¹ * dotProduct g Δx := by
            rw [dotProduct_smul]
            simp [smul_eq_mul]
          _ = lam⁻¹ * (-(lam ^ 2)) := by rw [hgΔ]
          _ = -lam := by
                have hinv : lam⁻¹ * lam = 1 := by
                  field_simp [hlam_ne]
                calc
                  lam⁻¹ * (-(lam ^ 2)) = -((lam⁻¹ * lam) * lam) := by ring
                  _ = -lam := by simp [hinv]
      have hy_obj : dotProduct g y = -lam := by
        linarith
      have hgap_zero : q (Δx - lam • y) = 0 :=
        hzero_gap_of_optimality y hy.1 hy.2 hy_obj
      have hAy_gap : A *ᵥ (Δx - lam • y) = 0 := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hν2, hy.1, smul_zero, sub_zero]
      have hgap_eq_zero : Δx - lam • y = 0 := hkernel (Δx - lam • y) hAy_gap hgap_zero
      ext i
      have hi : Δx i = lam * y i := by
        have hcoord : Δx i - lam * y i = 0 := by
          simpa [Pi.smul_apply] using congrFun hgap_eq_zero i
        linarith
      rw [Pi.smul_apply, hi]
      calc
        y i = 1 * y i := by ring
        _ = (lam⁻¹ * lam) * y i := by simp [hlam_ne]
        _ = lam⁻¹ * (lam * y i) := by ring
  have hnormalized_fun :
      (fun i => Δx i / newtonDecrement f xhat A Δx) = lam⁻¹ • Δx := by
    ext i
    simp [lam, div_eq_mul_inv, mul_comm]
  dsimp [QuadraticallyConstrainedLinearProgram.isFeasible,
    QuadraticallyConstrainedLinearProgram.objective]
  rw [hnormalized_fun]
  simpa [g, H, lam, q] using hfinal_raw

end «problem-73»
