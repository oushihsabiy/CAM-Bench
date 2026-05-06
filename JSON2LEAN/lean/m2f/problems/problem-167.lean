import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-167»

def l2Norm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, (x i) ^ 2)

/-- Squaring the Euclidean norm removes the outer square root. -/
lemma l2Norm_sub_sq_eq_sum_sq
    {n : ℕ} (y xcor : Fin n → ℝ) :
    l2Norm (y - xcor) ^ 2 = ∑ k : Fin n, (y k - xcor k) ^ 2 := by
  -- Rewrite the norm and then square the nonnegative square root.
  rw [l2Norm, Real.sq_sqrt]
  · simp
  · positivity

/-- The derivative of one coordinate-square summand has the expected linear form. -/
lemma coordinate_square_fderiv_apply
    {n : ℕ}
    (x xcor v : Fin n → ℝ)
    (k : Fin n) :
    (fderiv ℝ (fun y : Fin n → ℝ => (y k - xcor k) ^ 2) x) v =
      2 * (x k - xcor k) * v k := by
  -- The affine coordinate map has derivative given by projection onto the `k`-th coordinate.
  have hproj : fderiv ℝ (fun y : Fin n → ℝ => y k - xcor k) x = ContinuousLinearMap.proj k := by
    rw [fderiv_sub_const]
    simpa using (ContinuousLinearMap.fderiv (ContinuousLinearMap.proj k) (x := x))
  -- Apply the power rule and then evaluate the resulting continuous linear map.
  rw [fderiv_pow 2]
  · rw [hproj]
    simp [two_mul]
  · fun_prop

/-- The first directional derivative of the quadratic fidelity term is the expected coordinate
gradient entry. -/
lemma quadratic_fidelity_first_derivative_apply
    {n : ℕ}
    (x xcor : Fin n → ℝ)
    (j : Fin n) :
    (fderiv ℝ (fun y : Fin n → ℝ => l2Norm (y - xcor) ^ 2) x) (Pi.single j (1 : ℝ)) =
      2 * (x j - xcor j) := by
  -- Replace the squared norm by the coordinatewise quadratic sum.
  simp_rw [l2Norm_sub_sq_eq_sum_sq]
  have hfun :
      (fun y : Fin n → ℝ => ∑ k : Fin n, (y k - xcor k) ^ 2) =
        ∑ k : Fin n, fun y : Fin n → ℝ => (y k - xcor k) ^ 2 := by
    funext y
    simp
  rw [hfun]
  have hsum := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single j (1 : ℝ)))
    (fderiv_sum (𝕜 := ℝ) (x := x) (u := Finset.univ)
      (A := fun (k : Fin n) (y : Fin n → ℝ) => (y k - xcor k) ^ 2)
      (by
        intro k hk
        fun_prop))
  -- Evaluate the derivative of the finite sum one coordinate at a time.
  calc
    (fderiv ℝ (∑ k : Fin n, fun y : Fin n → ℝ => (y k - xcor k) ^ 2) x)
        (Pi.single j (1 : ℝ)) =
        ∑ k : Fin n, (fderiv ℝ (fun y : Fin n → ℝ => (y k - xcor k) ^ 2) x)
          (Pi.single j (1 : ℝ)) := by
            simpa [Finset.sum_apply] using hsum
    _ = 2 * (x j - xcor j) := by
      classical
      rw [Finset.sum_eq_single j]
      · simpa using coordinate_square_fderiv_apply x xcor (Pi.single j (1 : ℝ)) j
      · intro k hk hkj
        rw [coordinate_square_fderiv_apply]
        simp [hkj]
      · intro hj
        exfalso
        exact hj (Finset.mem_univ j)

/-- The quadratic fidelity term contributes `2` on the diagonal and `0` off the diagonal to the
Hessian. -/
lemma quadratic_fidelity_hessian_entry
    {n : ℕ}
    (x xcor : Fin n → ℝ)
    (i j : Fin n) :
    (fderiv ℝ
      (fun y => (fderiv ℝ (fun y : Fin n → ℝ => l2Norm (y - xcor) ^ 2) y) (Pi.single j (1 : ℝ)))
      x) (Pi.single i (1 : ℝ)) = if i = j then 2 else 0 := by
  have hfun :
      (fun y : Fin n → ℝ =>
        (fderiv ℝ (fun z : Fin n → ℝ => l2Norm (z - xcor) ^ 2) y) (Pi.single j (1 : ℝ))) =
        fun y : Fin n → ℝ => 2 * (y j - xcor j) := by
    funext y
    -- Differentiate the quadratic sum once and identify the `j`-th entry.
    rw [quadratic_fidelity_first_derivative_apply y xcor j]
  rw [hfun]
  -- Differentiate the affine coordinate map one more time.
  have hproj : fderiv ℝ (fun y : Fin n → ℝ => y j - xcor j) x = ContinuousLinearMap.proj j := by
    rw [fderiv_sub_const]
    simpa using (ContinuousLinearMap.fderiv (ContinuousLinearMap.proj j) (x := x))
  rw [fderiv_const_mul]
  · rw [hproj]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  · fun_prop

/-- The scalar ATV edge penalty has the expected first derivative. -/
lemma atv_scalar_first_derivative
    (ε t : ℝ)
    (hε : 0 < ε) :
    HasDerivAt (fun s : ℝ => Real.sqrt (ε ^ 2 + s ^ 2) - ε)
      (t / Real.sqrt (ε ^ 2 + t ^ 2)) t := by
  -- Differentiate the quadratic inside the square root.
  have hsq : HasDerivAt (fun s : ℝ => ε ^ 2 + s ^ 2) (2 * t) t := by
    simpa [two_mul] using ((hasDerivAt_id t).pow 2).const_add (ε ^ 2)
  have hpos : 0 < ε ^ 2 + t ^ 2 := by positivity
  have hneq : ε ^ 2 + t ^ 2 ≠ 0 := by linarith
  -- Apply the square-root chain rule and simplify the resulting coefficient.
  have hsqrt :
      HasDerivAt (fun s : ℝ => Real.sqrt (ε ^ 2 + s ^ 2))
        ((2 * t) / (2 * Real.sqrt (ε ^ 2 + t ^ 2))) t := by
    exact hsq.sqrt hneq
  have hsub := hsqrt.sub_const ε
  convert hsub using 1 <;> field_simp [hneq, Real.sqrt_ne_zero'.2 hpos]

/-- The derivative of the ATV edge coefficient is the stated weight. -/
lemma atv_scalar_coefficient_derivative
    (ε t : ℝ)
    (hε : 0 < ε) :
    HasDerivAt (fun s : ℝ => s / Real.sqrt (ε ^ 2 + s ^ 2))
      ((ε ^ 2) / Real.rpow (ε ^ 2 + t ^ 2) (3 / 2 : ℝ)) t := by
  have hpos : 0 < ε ^ 2 + t ^ 2 := by positivity
  have hneq : ε ^ 2 + t ^ 2 ≠ 0 := by linarith
  -- Differentiate the inverse square-root factor in product form.
  have hsq : HasDerivAt (fun s : ℝ => ε ^ 2 + s ^ 2) (2 * t) t := by
    simpa [two_mul] using ((hasDerivAt_id t).pow 2).const_add (ε ^ 2)
  have hsqrt :
      HasDerivAt (fun s : ℝ => Real.sqrt (ε ^ 2 + s ^ 2))
        ((2 * t) / (2 * Real.sqrt (ε ^ 2 + t ^ 2))) t := by
    exact hsq.sqrt hneq
  have hsqrt_ne : Real.sqrt (ε ^ 2 + t ^ 2) ≠ 0 := by
    exact Real.sqrt_ne_zero'.2 hpos
  have hinv :
      HasDerivAt (fun s : ℝ => (Real.sqrt (ε ^ 2 + s ^ 2))⁻¹)
        (-(2 * t / (2 * Real.sqrt (ε ^ 2 + t ^ 2))) / (Real.sqrt (ε ^ 2 + t ^ 2)) ^ 2) t := by
    exact hsqrt.inv hsqrt_ne
  have hmul := (hasDerivAt_id t).mul hinv
  have hbase :
      HasDerivAt (fun s : ℝ => s / Real.sqrt (ε ^ 2 + s ^ 2))
        ((ε ^ 2) / (Real.sqrt (ε ^ 2 + t ^ 2)) ^ 3) t := by
    convert hmul using 1 <;> field_simp [hneq, hsqrt_ne]
    ring_nf
    rw [Real.sq_sqrt (show 0 ≤ ε ^ 2 + t ^ 2 by positivity)]
    simp
    ring
  convert hbase using 1
  have hpow :
      (Real.sqrt (ε ^ 2 + t ^ 2)) ^ 3 = Real.rpow (ε ^ 2 + t ^ 2) (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (show 0 ≤ ε ^ 2 + t ^ 2 by positivity)]
    norm_num
  rw [hpow]

/-- Each single ATV edge term is differentiable because the quadratic under the square root stays
strictly positive. -/
lemma atv_edge_differentiableAt
    {n : ℕ}
    (hn : 2 ≤ n)
    (ε : ℝ)
    (hε : 0 < ε)
    (k : Fin (n - 1))
    (y : Fin n → ℝ) :
    DifferentiableAt ℝ
      (fun z : Fin n → ℝ =>
        Real.sqrt (ε ^ 2 + (z ⟨k.1 + 1, by omega⟩ - z ⟨k.1, by omega⟩) ^ 2) - ε) y := by
  let delta : (Fin n → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) ⟨k.1 + 1, by omega⟩) -
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) ⟨k.1, by omega⟩)
  -- Compose the scalar derivative of the edge penalty with the linear coordinate-difference map.
  have hdelta : HasFDerivAt (fun z : Fin n → ℝ => delta z) delta y := by
    simpa [delta] using (ContinuousLinearMap.hasFDerivAt delta (x := y))
  exact ((atv_scalar_first_derivative ε (delta y) hε).comp_hasFDerivAt y hdelta).differentiableAt

/-- Evaluating the edge difference map on a basis vector produces the usual signed tridiagonal
stencil. -/
lemma edge_sigma_value
    {n : ℕ}
    (hn : 2 ≤ n)
    (k : Fin (n - 1))
    (i : Fin n) :
    let kp1 : Fin n := ⟨k.1 + 1, by omega⟩
    let k0 : Fin n := ⟨k.1, by omega⟩
    let delta : (Fin n → ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) kp1) -
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k0)
    delta (Pi.single i (1 : ℝ)) = if i = kp1 then 1 else if i = k0 then -1 else 0 := by
  dsimp
  -- Split by whether the basis vector hits the upper endpoint, the lower endpoint, or neither.
  by_cases h1 : i = ⟨k.1 + 1, by omega⟩
  · subst h1
    simp
  · by_cases h0 : i = ⟨k.1, by omega⟩
    · subst h0
      simp [h1]
    · simp [h1, h0]

/-- A single ATV edge contributes the expected rank-one local stencil to the Hessian entry. -/
lemma single_edge_hessian_entry
    {n : ℕ}
    (hn : 2 ≤ n)
    (ε : ℝ)
    (hε : 0 < ε)
    (x : Fin n → ℝ)
    (k : Fin (n - 1))
    (i j : Fin n) :
    let kp1 : Fin n := ⟨k.1 + 1, by omega⟩
    let k0 : Fin n := ⟨k.1, by omega⟩
    let delta : (Fin n → ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) kp1) -
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k0)
    let sigma : Fin n → ℝ := fun a => delta (Pi.single a (1 : ℝ))
    (fderiv ℝ
      (fun y : Fin n → ℝ =>
        (fderiv ℝ (fun z : Fin n → ℝ => Real.sqrt (ε ^ 2 + (delta z) ^ 2) - ε) y)
          (Pi.single j (1 : ℝ))) x)
      (Pi.single i (1 : ℝ)) =
      ((ε ^ 2) / Real.rpow (ε ^ 2 + (delta x) ^ 2) (3 / 2 : ℝ)) * sigma i * sigma j := by
  dsimp
  let delta : (Fin n → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) ⟨k.1 + 1, by omega⟩) -
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) ⟨k.1, by omega⟩)
  let sigma : Fin n → ℝ := fun a => delta (Pi.single a (1 : ℝ))
  change
    (fderiv ℝ
      (fun y : Fin n → ℝ =>
        (fderiv ℝ (fun z : Fin n → ℝ => Real.sqrt (ε ^ 2 + (delta z) ^ 2) - ε) y)
          (Pi.single j (1 : ℝ))) x)
      (Pi.single i (1 : ℝ)) =
      ((ε ^ 2) / Real.rpow (ε ^ 2 + (delta x) ^ 2) (3 / 2 : ℝ)) * sigma i * sigma j
  -- Route correction: the stable route is to keep the full Hessian identity inline and isolate
  -- only the closed one-edge calculation here.
  have hdelta : HasFDerivAt (fun y : Fin n → ℝ => delta y) delta x := by
    simpa [delta] using (ContinuousLinearMap.hasFDerivAt delta (x := x))
  have hfirst :
      (fun y : Fin n → ℝ =>
        (fderiv ℝ (fun z : Fin n → ℝ => Real.sqrt (ε ^ 2 + (delta z) ^ 2) - ε) y)
          (Pi.single j (1 : ℝ))) =
        fun y : Fin n → ℝ => sigma j * ((delta y) / Real.sqrt (ε ^ 2 + (delta y) ^ 2)) := by
    funext y
    -- First differentiate the scalar edge penalty, then evaluate that linear map on `e_j`.
    have hdelta_y : HasFDerivAt (fun z : Fin n → ℝ => delta z) delta y := by
      simpa [delta] using (ContinuousLinearMap.hasFDerivAt delta (x := y))
    have hedge0 := (atv_scalar_first_derivative ε (delta y) hε).comp_hasFDerivAt y hdelta_y
    have hedgeF :
        fderiv ℝ ((fun s : ℝ => Real.sqrt (ε ^ 2 + s ^ 2) - ε) ∘ fun z : Fin n → ℝ => delta z) y =
          (((delta y) / Real.sqrt (ε ^ 2 + (delta y) ^ 2)) • delta) := by
      simpa using hedge0.fderiv
    have happly := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single j (1 : ℝ))) hedgeF
    simpa [sigma, mul_comm, mul_left_comm, mul_assoc] using happly
  rw [hfirst]
  -- Differentiate the scalar coefficient and keep the constant `sigma j` outside.
  have hcoeff :
      HasFDerivAt
        (fun y : Fin n → ℝ => (delta y) / Real.sqrt (ε ^ 2 + (delta y) ^ 2))
        (((ε ^ 2) / Real.rpow (ε ^ 2 + (delta x) ^ 2) (3 / 2 : ℝ)) • delta) x := by
    simpa using (atv_scalar_coefficient_derivative ε (delta x) hε).comp_hasFDerivAt x hdelta
  have hfinal :
      fderiv ℝ (fun y : Fin n → ℝ => sigma j * ((delta y) / Real.sqrt (ε ^ 2 + (delta y) ^ 2))) x =
        sigma j • (((ε ^ 2) / Real.rpow (ε ^ 2 + (delta x) ^ 2) (3 / 2 : ℝ)) • delta) := by
    simpa using (hcoeff.const_mul (sigma j)).fderiv
  -- Evaluating the resulting linear map on `e_i` gives the rank-one stencil entry.
  have happly := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single i (1 : ℝ))) hfinal
  simpa [sigma, ContinuousLinearMap.smul_apply, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
    happly

/-- Evaluating the first derivative of one ATV edge on a basis vector gives the explicit signed
endpoint coefficient times the scalar edge coefficient. -/
lemma single_edge_first_derivative_function
    {n : ℕ}
    (hn : 2 ≤ n)
    (ε : ℝ)
    (hε : 0 < ε)
    (k : Fin (n - 1))
    (j : Fin n) :
    let kp1 : Fin n := ⟨k.1 + 1, by omega⟩
    let k0 : Fin n := ⟨k.1, by omega⟩
    let delta : (Fin n → ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) kp1) -
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k0)
    (fun y : Fin n → ℝ =>
      (fderiv ℝ (fun z : Fin n → ℝ => Real.sqrt (ε ^ 2 + (delta z) ^ 2) - ε) y)
        (Pi.single j (1 : ℝ))) =
      fun y : Fin n → ℝ =>
        (if j = kp1 then 1 else if j = k0 then -1 else 0) *
          ((delta y) / Real.sqrt (ε ^ 2 + (delta y) ^ 2)) := by
  dsimp
  let delta : (Fin n → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) ⟨k.1 + 1, by omega⟩) -
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) ⟨k.1, by omega⟩)
  have hsigma :
      delta (Pi.single j (1 : ℝ)) =
        if j = ⟨k.1 + 1, by omega⟩ then 1 else if j = ⟨k.1, by omega⟩ then -1 else 0 := by
    simpa [delta] using (edge_sigma_value hn k j)
  funext y
  -- Differentiate the scalar edge penalty and then evaluate its linear derivative on `e_j`.
  have hdelta : HasFDerivAt (fun z : Fin n → ℝ => delta z) delta y := by
    simpa [delta] using (ContinuousLinearMap.hasFDerivAt delta (x := y))
  have hedge0 := (atv_scalar_first_derivative ε (delta y) hε).comp_hasFDerivAt y hdelta
  have hedgeF :
      fderiv ℝ (fun z : Fin n → ℝ => Real.sqrt (ε ^ 2 + (delta z) ^ 2) - ε) y =
        (((delta y) / Real.sqrt (ε ^ 2 + (delta y) ^ 2)) • delta) := by
    simpa using hedge0.fderiv
  have happly := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single j (1 : ℝ))) hedgeF
  calc
    (fderiv ℝ (fun z : Fin n → ℝ => Real.sqrt (ε ^ 2 + (delta z) ^ 2) - ε) y)
        (Pi.single j (1 : ℝ)) =
        ((delta y) / Real.sqrt (ε ^ 2 + (delta y) ^ 2)) * delta (Pi.single j (1 : ℝ)) := by
          simpa [ContinuousLinearMap.smul_apply, mul_comm, mul_left_comm, mul_assoc] using happly
    _ =
        (if j = ⟨k.1 + 1, by omega⟩ then 1 else if j = ⟨k.1, by omega⟩ then -1 else 0) *
          ((delta y) / Real.sqrt (ε ^ 2 + (delta y) ^ 2)) := by
          rw [hsigma]
          ring

/-- The ATV Hessian entry is the weighted signed edge-incidence sum. -/
lemma atv_hessian_entry_as_edge_sum
    {n : ℕ}
    (hn : 2 ≤ n)
    (x : Fin n → ℝ)
    (ε : ℝ)
    (hε : 0 < ε)
    (i j : Fin n) :
    let φ_atv : (Fin n → ℝ) → ℝ := fun y =>
      ∑ k : Fin (n - 1),
        (Real.sqrt (ε ^ 2 + (y ⟨k.1 + 1, by omega⟩ - y ⟨k.1, by omega⟩) ^ 2) - ε)
    let w : Fin (n - 1) → ℝ := fun k =>
      (ε ^ 2) /
        Real.rpow
          (ε ^ 2 + (x ⟨k.1 + 1, by omega⟩ - x ⟨k.1, by omega⟩) ^ 2)
          (3 / 2 : ℝ)
    (fderiv ℝ (fun y => (fderiv ℝ φ_atv y) (Pi.single j (1 : ℝ))) x)
      (Pi.single i (1 : ℝ)) =
      ∑ k : Fin (n - 1),
        w k *
          (if i = ⟨k.1 + 1, by omega⟩ then 1 else if i = ⟨k.1, by omega⟩ then -1 else 0) *
          (if j = ⟨k.1 + 1, by omega⟩ then 1 else if j = ⟨k.1, by omega⟩ then -1 else 0) := by
  dsimp
  let edge : Fin (n - 1) → (Fin n → ℝ) → ℝ := fun k y =>
    Real.sqrt (ε ^ 2 + (y ⟨k.1 + 1, by omega⟩ - y ⟨k.1, by omega⟩) ^ 2) - ε
  have hfirst :
      (fun y : Fin n → ℝ =>
        (fderiv ℝ (fun z : Fin n → ℝ => ∑ k : Fin (n - 1), edge k z) y)
          (Pi.single j (1 : ℝ))) =
        ∑ k : Fin (n - 1), fun y : Fin n → ℝ =>
          (fderiv ℝ (edge k) y) (Pi.single j (1 : ℝ)) := by
    funext y
    -- First expand the ATV derivative as the sum of the one-edge derivatives.
    have hsum := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single j (1 : ℝ)))
      (fderiv_sum (𝕜 := ℝ) (x := y) (u := Finset.univ)
        (A := edge)
        (by
          intro k hk
          simpa [edge] using atv_edge_differentiableAt hn ε hε k y))
    have hfun :
        (fun z : Fin n → ℝ => ∑ k : Fin (n - 1), edge k z) = ∑ k : Fin (n - 1), edge k := by
      funext z
      simp
    rw [hfun]
    simpa [Finset.sum_apply] using hsum
  rw [hfirst]
  have hsummand_diff :
      ∀ k : Fin (n - 1),
        DifferentiableAt ℝ
          (fun y : Fin n → ℝ => (fderiv ℝ (edge k) y) (Pi.single j (1 : ℝ))) x := by
    intro k
    let delta : (Fin n → ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) ⟨k.1 + 1, by omega⟩) -
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) ⟨k.1, by omega⟩)
    have hrewrite :
        (fun y : Fin n → ℝ => (fderiv ℝ (edge k) y) (Pi.single j (1 : ℝ))) =
          fun y : Fin n → ℝ =>
            (if j = ⟨k.1 + 1, by omega⟩ then 1 else if j = ⟨k.1, by omega⟩ then -1 else 0) *
              ((delta y) / Real.sqrt (ε ^ 2 + (delta y) ^ 2)) := by
      -- Route correction: rewrite the first derivative into an explicit scalar function before
      -- differentiating it a second time, so the outer `fderiv_sum` sees only stable scalar terms.
      simpa [edge, delta] using (single_edge_first_derivative_function hn ε hε k j)
    rw [hrewrite]
    have hdelta : HasFDerivAt (fun y : Fin n → ℝ => delta y) delta x := by
      simpa [delta] using (ContinuousLinearMap.hasFDerivAt delta (x := x))
    have hcoeff :
        HasFDerivAt
          (fun y : Fin n → ℝ => (delta y) / Real.sqrt (ε ^ 2 + (delta y) ^ 2))
          (((ε ^ 2) / Real.rpow (ε ^ 2 + (delta x) ^ 2) (3 / 2 : ℝ)) • delta) x := by
      simpa using (atv_scalar_coefficient_derivative ε (delta x) hε).comp_hasFDerivAt x hdelta
    exact (hcoeff.differentiableAt).const_mul _
  have hsum := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single i (1 : ℝ)))
    (fderiv_sum (𝕜 := ℝ) (x := x) (u := Finset.univ)
      (A := fun k : Fin (n - 1) => fun y : Fin n → ℝ =>
        (fderiv ℝ (edge k) y) (Pi.single j (1 : ℝ)))
      (by
        intro k hk
        exact hsummand_diff k))
  calc
    (fderiv ℝ
      (∑ k : Fin (n - 1), fun y : Fin n → ℝ => (fderiv ℝ (edge k) y) (Pi.single j (1 : ℝ))) x)
        (Pi.single i (1 : ℝ)) =
        ∑ k : Fin (n - 1),
          (fderiv ℝ (fun y : Fin n → ℝ => (fderiv ℝ (edge k) y) (Pi.single j (1 : ℝ))) x)
            (Pi.single i (1 : ℝ)) := by
          simpa [Finset.sum_apply] using hsum
    _ = ∑ k : Fin (n - 1),
          ((ε ^ 2) /
            Real.rpow
              (ε ^ 2 + (x ⟨k.1 + 1, by omega⟩ - x ⟨k.1, by omega⟩) ^ 2)
              (3 / 2 : ℝ)) *
            (if i = ⟨k.1 + 1, by omega⟩ then 1 else if i = ⟨k.1, by omega⟩ then -1 else 0) *
            (if j = ⟨k.1 + 1, by omega⟩ then 1 else if j = ⟨k.1, by omega⟩ then -1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          -- Collapse the one-edge second derivative to the weighted signed stencil formula.
          let kp1 : Fin n := ⟨k.1 + 1, by omega⟩
          let k0 : Fin n := ⟨k.1, by omega⟩
          let delta : (Fin n → ℝ) →L[ℝ] ℝ :=
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) kp1) -
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k0)
          let sigma : Fin n → ℝ := fun a => delta (Pi.single a (1 : ℝ))
          have hentry :
              (fderiv ℝ
                (fun y : Fin n → ℝ =>
                  (fderiv ℝ (edge k) y) (Pi.single j (1 : ℝ))) x)
                (Pi.single i (1 : ℝ)) =
                ((ε ^ 2) / Real.rpow (ε ^ 2 + (delta x) ^ 2) (3 / 2 : ℝ)) * sigma i * sigma j := by
            simpa [edge, kp1, k0, delta, sigma] using (single_edge_hessian_entry hn ε hε x k i j)
          have hsigi :
              sigma i = if i = kp1 then 1 else if i = k0 then -1 else 0 := by
            simpa [kp1, k0, delta, sigma] using (edge_sigma_value hn k i)
          have hsigj :
              sigma j = if j = kp1 then 1 else if j = k0 then -1 else 0 := by
            simpa [kp1, k0, delta, sigma] using (edge_sigma_value hn k j)
          rw [hentry, hsigi, hsigj]
          simpa [kp1, k0, delta, mul_assoc, mul_left_comm, mul_comm]

/-- The first directional derivative of the ATV term is differentiable, because it is a finite sum
of the explicit one-edge scalar coefficient functions. -/
lemma atv_first_directional_differentiableAt
    {n : ℕ}
    (hn : 2 ≤ n)
    (x : Fin n → ℝ)
    (ε : ℝ)
    (hε : 0 < ε)
    (j : Fin n) :
    let φ_atv : (Fin n → ℝ) → ℝ := fun y =>
      ∑ k : Fin (n - 1),
        (Real.sqrt (ε ^ 2 + (y ⟨k.1 + 1, by omega⟩ - y ⟨k.1, by omega⟩) ^ 2) - ε)
    DifferentiableAt ℝ (fun y => (fderiv ℝ φ_atv y) (Pi.single j (1 : ℝ))) x := by
  dsimp
  let edge : Fin (n - 1) → (Fin n → ℝ) → ℝ := fun k y =>
    Real.sqrt (ε ^ 2 + (y ⟨k.1 + 1, by omega⟩ - y ⟨k.1, by omega⟩) ^ 2) - ε
  have hfirst :
      (fun y : Fin n → ℝ =>
        (fderiv ℝ (fun z : Fin n → ℝ => ∑ k : Fin (n - 1), edge k z) y)
          (Pi.single j (1 : ℝ))) =
        ∑ k : Fin (n - 1), fun y : Fin n → ℝ =>
          (fderiv ℝ (edge k) y) (Pi.single j (1 : ℝ)) := by
    funext y
    -- Expand the first directional derivative of the ATV sum edge by edge.
    have hsum := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single j (1 : ℝ)))
      (fderiv_sum (𝕜 := ℝ) (x := y) (u := Finset.univ)
        (A := edge)
        (by
          intro k hk
          simpa [edge] using atv_edge_differentiableAt hn ε hε k y))
    have hfun :
        (fun z : Fin n → ℝ => ∑ k : Fin (n - 1), edge k z) = ∑ k : Fin (n - 1), edge k := by
      funext z
      simp
    rw [hfun]
    simpa [Finset.sum_apply] using hsum
  rw [hfirst]
  refine DifferentiableAt.sum ?_
  intro k hk
  let delta : (Fin n → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) ⟨k.1 + 1, by omega⟩) -
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) ⟨k.1, by omega⟩)
  have hrewrite :
      (fun y : Fin n → ℝ => (fderiv ℝ (edge k) y) (Pi.single j (1 : ℝ))) =
        fun y : Fin n → ℝ =>
          (if j = ⟨k.1 + 1, by omega⟩ then 1 else if j = ⟨k.1, by omega⟩ then -1 else 0) *
            ((delta y) / Real.sqrt (ε ^ 2 + (delta y) ^ 2)) := by
    -- Route correction: normalize each edge derivative into an explicit scalar formula before the
    -- second derivative step, so the proof stays in the stable scalar calculus API.
    simpa [edge, delta] using (single_edge_first_derivative_function hn ε hε k j)
  rw [hrewrite]
  have hdelta : HasFDerivAt (fun y : Fin n → ℝ => delta y) delta x := by
    simpa [delta] using (ContinuousLinearMap.hasFDerivAt delta (x := x))
  have hcoeff :
      HasFDerivAt
        (fun y : Fin n → ℝ => (delta y) / Real.sqrt (ε ^ 2 + (delta y) ^ 2))
        (((ε ^ 2) / Real.rpow (ε ^ 2 + (delta x) ^ 2) (3 / 2 : ℝ)) • delta) x := by
    simpa using (atv_scalar_coefficient_derivative ε (delta x) hε).comp_hasFDerivAt x hdelta
  exact (hcoeff.differentiableAt).const_mul _

/-
For a twice differentiable function f, a vector p ∈ ℝ^n is a Newton direction at x if it satisfies
∇^2 f(x) p = - ∇ f(x).
-/
def IsNewtonDirectionAt
    {n : ℕ}
    (hess : Matrix (Fin n) (Fin n) ℝ)
    (grad : Fin n → ℝ)
    (p : Fin n → ℝ) : Prop :=
  hess.mulVec p = fun i => -grad i

macro_rules
  | `(IsNewtonDirectionAt $hess $grad $_compat $p) =>
      `(Exercise_8_6__b_.IsNewtonDirectionAt $hess $grad $p)

/-
A matrix A ∈ ℝ^{n×n} is symmetric tridiagonal if A = Aᵀ and A_{ij} = 0 whenever |i - j| > 1.
-/
def IsSymmetricTridiagonal
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A.IsSymm ∧ ∀ i j : Fin n, 1 < Int.natAbs (i.1 - j.1) → A i j = 0

/-
A linear system is a system of equations of the form Ax = b, where A ∈ ℝ^{m × n}, x ∈ ℝ^n, and b ∈
ℝ^m.
-/
def IsLinearSystem
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ)
    (b : Fin m → ℝ) : Prop :=
  A.mulVec x = b

/-
For a symmetric positive definite banded matrix A, banded Cholesky is the factorization A = LLᵀ
computed by exploiting the bandwidth, where L is lower triangular and has the same bandwidth as A.
-/
def IsBandedCholeskyFactorization
    {n : ℕ}
    (A L : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ k : ℕ,
    A.IsSymm ∧
    (∀ x : Fin n → ℝ, x ≠ 0 → 0 < dotProduct x (A.mulVec x)) ∧
    (∀ i j : Fin n, k < Int.natAbs (i.1 - j.1) → A i j = 0) ∧
    A = L * L.transpose ∧
    (∀ i j : Fin n, i.1 < j.1 → L i j = 0) ∧
    ∀ i j : Fin n, k < Int.natAbs (i.1 - j.1) → L i j = 0

/-
A Thomas - type method is a specialized Gaussian elimination algorithm for solving a tridiagonal
linear system Ax = b in O(n) arithmetic operations.
-/
def thomasTypeOperationCount (n : ℕ) : ℕ :=
  8 * n + 3

def IsThomasTypeMethod
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) : Prop :=
  -- Precondition: A is tridiagonal
  (∀ i j : Fin n, 1 < Int.natAbs (i.1 - j.1) → A i j = 0) ∧
  -- There exists a solver for this n-dimensional tridiagonal system whose cost is measured by the
  -- fixed Thomas-type operation count model.
  ∃ (solve : Matrix (Fin n) (Fin n) ℝ → (Fin n → ℝ) → Fin n → ℝ) (C : ℕ),
    IsLinearSystem A (solve A b) b ∧
    thomasTypeOperationCount n ≤ C * n + C

/-
Let n ∈ ℕ with n ≥ 2, let x^{cor} ∈ ℝ^n, and let μ > 0 and ε > 0. For x = (x₁, ..., xₙ) ∈ ℝ^n,
define
φ_{atv}(x) = \sum_{i = 1}^{n - 1}(\sqrt{ε^2 + (x_{i + 1} - xᵢ)^2} - ε), and psi(x) =
‖x - x^{cor}‖_2^2 + μφ_{atv}(x). For each i = 1, ..., n - 1, set wᵢ = ε^2{(ε^2 + (x_{i + 1} -
xᵢ)^2)^{3/2}}. Let
H = ∇^2psi(x) be the Hessian of psi at x, and let the Newton direction p∈ℝ^n satisfy H p = - ∇
psi(x). Prove that H is the symmetric tridiagonal matrix H = 2I + μ T, where T∈ℝ^{n×n} has entries
(T)_{ii} = cases w₁, & i = 1,; w_{i - 1} + wᵢ, & 2 ≤ i ≤ n - 1,; w_{n - 1}, & i = n, cases (T)_{i, i
+ 1} =
(T)_{i + 1, i} = - wᵢ (1 ≤ i ≤ n - 1), and all other entries equal to zero. Deduce that the Newton
direction can therefore be computed by solving a symmetric tridiagonal linear system, which requires
O(n) flops using a banded Cholesky or Thomas - type method, whereas a generic dense linear solve
would
require O(n^3) flops.
-/
theorem hessian_of_atv_objective_is_symmetric_tridiagonal_and_newton_system_linear_time
    {n : ℕ}
    (hn : 2 ≤ n)
    (x xcor : Fin n → ℝ)
    (μ ε : ℝ)
    (hμ : 0 < μ)
    (hε : 0 < ε) :
    let φ_atv : (Fin n → ℝ) → ℝ := fun y =>
      ∑ i : Fin (n - 1),
        (Real.sqrt (ε ^ 2 + (y ⟨i.1 + 1, by omega⟩ - y ⟨i.1, by omega⟩) ^ 2) - ε)
    let ψ : (Fin n → ℝ) → ℝ := fun y =>
      l2Norm (y - xcor) ^ 2 + μ * φ_atv y
    let w : Fin (n - 1) → ℝ := fun i =>
      (ε ^ 2) /
        Real.rpow
          (ε ^ 2 + (x ⟨i.1 + 1, by omega⟩ - x ⟨i.1, by omega⟩) ^ 2)
          (3 / 2 : ℝ)
    let grad : Fin n → ℝ := fun i : Fin n =>
      (fderiv ℝ ψ x) (Pi.single i (1 : ℝ))
    let H : Matrix (Fin n) (Fin n) ℝ := fun i j =>
      (fderiv ℝ (fun y => (fderiv ℝ ψ y) (Pi.single j (1 : ℝ))) x)
        (Pi.single i (1 : ℝ))
    let T : Matrix (Fin n) (Fin n) ℝ := fun i j =>
      if hdiag : i = j then
        if hi0 : i.1 = 0 then
          w ⟨0, by omega⟩
        else if hlast : i.1 + 1 = n then
          w ⟨n - 2, by omega⟩
        else
          w ⟨i.1 - 1, by omega⟩ + w ⟨i.1, by omega⟩
      else if hij1 : j.1 = i.1 + 1 then
        -w ⟨i.1, by omega⟩
      else if hji1 : i.1 = j.1 + 1 then
        -w ⟨j.1, by omega⟩
      else
        0
    -- H is the stated symmetric tridiagonal matrix (unconditional)
    H = 2 • (1 : Matrix (Fin n) (Fin n) ℝ) + μ • T ∧
    IsSymmetricTridiagonal H ∧
    (∀ i : Fin n, i.1 = 0 → T i i = w ⟨0, by omega⟩) ∧
    (∀ i : Fin n, ∀ hi1 : 1 ≤ i.1, ∀ hi2 : i.1 + 1 < n,
      T i i = w ⟨i.1 - 1, by omega⟩ + w ⟨i.1, by omega⟩) ∧
    (∀ i : Fin n, i.1 + 1 = n → T i i = w ⟨n - 2, by omega⟩) ∧
    (∀ i : Fin (n - 1), T ⟨i.1, by omega⟩ ⟨i.1 + 1, by omega⟩ = -w i) ∧
    (∀ i : Fin (n - 1), T ⟨i.1 + 1, by omega⟩ ⟨i.1, by omega⟩ = -w i) ∧
    (∀ i j : Fin n, 1 < Int.natAbs (i.1 - j.1) → T i j = 0) ∧
    -- Deduction: any Newton direction can be found in O(n) by a tridiagonal solver
    ∀ p : Fin n → ℝ,
      IsNewtonDirectionAt H grad p →
      ((∃ L : Matrix (Fin n) (Fin n) ℝ, IsBandedCholeskyFactorization H L) ∨
        IsThomasTypeMethod H (fun i => -grad i)) := by
  classical
  let φ_atv : (Fin n → ℝ) → ℝ := fun y =>
    ∑ i : Fin (n - 1),
      (Real.sqrt (ε ^ 2 + (y ⟨i.1 + 1, by omega⟩ - y ⟨i.1, by omega⟩) ^ 2) - ε)
  let ψ : (Fin n → ℝ) → ℝ := fun y =>
    l2Norm (y - xcor) ^ 2 + μ * φ_atv y
  let w : Fin (n - 1) → ℝ := fun i =>
    (ε ^ 2) /
      Real.rpow
        (ε ^ 2 + (x ⟨i.1 + 1, by omega⟩ - x ⟨i.1, by omega⟩) ^ 2)
        (3 / 2 : ℝ)
  let grad : Fin n → ℝ := fun i : Fin n =>
    (fderiv ℝ ψ x) (Pi.single i (1 : ℝ))
  let H : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    (fderiv ℝ (fun y => (fderiv ℝ ψ y) (Pi.single j (1 : ℝ))) x)
      (Pi.single i (1 : ℝ))
  let T : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    if hdiag : i = j then
      if hi0 : i.1 = 0 then
        w ⟨0, by omega⟩
      else if hlast : i.1 + 1 = n then
        w ⟨n - 2, by omega⟩
      else
        w ⟨i.1 - 1, by omega⟩ + w ⟨i.1, by omega⟩
    else if hij1 : j.1 = i.1 + 1 then
      -w ⟨i.1, by omega⟩
    else if hji1 : i.1 = j.1 + 1 then
      -w ⟨j.1, by omega⟩
    else
      0
  change
    H = 2 • (1 : Matrix (Fin n) (Fin n) ℝ) + μ • T ∧
    IsSymmetricTridiagonal H ∧
    (∀ i : Fin n, i.1 = 0 → T i i = w ⟨0, by omega⟩) ∧
    (∀ i : Fin n, ∀ hi1 : 1 ≤ i.1, ∀ hi2 : i.1 + 1 < n,
      T i i = w ⟨i.1 - 1, by omega⟩ + w ⟨i.1, by omega⟩) ∧
    (∀ i : Fin n, i.1 + 1 = n → T i i = w ⟨n - 2, by omega⟩) ∧
    (∀ i : Fin (n - 1), T ⟨i.1, by omega⟩ ⟨i.1 + 1, by omega⟩ = -w i) ∧
    (∀ i : Fin (n - 1), T ⟨i.1 + 1, by omega⟩ ⟨i.1, by omega⟩ = -w i) ∧
    (∀ i j : Fin n, 1 < Int.natAbs (i.1 - j.1) → T i j = 0) ∧
    ∀ p : Fin n → ℝ,
      IsNewtonDirectionAt H grad p →
      ((∃ L : Matrix (Fin n) (Fin n) ℝ, IsBandedCholeskyFactorization H L) ∨
        IsThomasTypeMethod H (fun i => -grad i))
  -- Route correction: the one-edge derivative normalization is now proved above.
  -- The remaining blocker is the finite-support collapse from the normalized edge sum to the
  -- explicit tridiagonal matrix `T`, especially the interior two-edge diagonal case.
  let edgeTerm : Fin n → Fin n → Fin (n - 1) → ℝ := fun i j k =>
    w k *
      (if i = ⟨k.1 + 1, by omega⟩ then 1 else if i = ⟨k.1, by omega⟩ then -1 else 0) *
      (if j = ⟨k.1 + 1, by omega⟩ then 1 else if j = ⟨k.1, by omega⟩ then -1 else 0)
  let edgeSum : Fin n → Fin n → ℝ := fun i j => ∑ k : Fin (n - 1), edgeTerm i j k
  let edge : Fin (n - 1) → (Fin n → ℝ) → ℝ := fun k y =>
    Real.sqrt (ε ^ 2 + (y ⟨k.1 + 1, by omega⟩ - y ⟨k.1, by omega⟩) ^ 2) - ε
  have hATVEntry :
      ∀ i j : Fin n,
        (fderiv ℝ (fun y => (fderiv ℝ φ_atv y) (Pi.single j (1 : ℝ))) x)
          (Pi.single i (1 : ℝ)) = edgeSum i j := by
    intro i j
    simpa [φ_atv, w, edgeTerm, edgeSum] using (atv_hessian_entry_as_edge_sum hn x ε hε i j)
  have hT_diag_zero :
      ∀ i : Fin n, i.1 = 0 → T i i = w ⟨0, by omega⟩ := by
    intro i hi0
    -- Unfolding `T` on the left endpoint keeps only the first diagonal weight.
    simp [T, hi0]
  have hT_diag_mid :
      ∀ i : Fin n, ∀ hi1 : 1 ≤ i.1, ∀ hi2 : i.1 + 1 < n,
        T i i = w ⟨i.1 - 1, by omega⟩ + w ⟨i.1, by omega⟩ := by
    intro i hi1 hi2
    have hi0 : i.1 ≠ 0 := by omega
    have hlast : i.1 + 1 ≠ n := by omega
    -- Interior vertices see the two incident edge weights on the diagonal.
    simp [T, hi0, hlast]
  have hT_diag_last :
      ∀ i : Fin n, i.1 + 1 = n → T i i = w ⟨n - 2, by omega⟩ := by
    intro i hlast
    have hi0 : i.1 ≠ 0 := by omega
    -- At the right endpoint only the final edge contributes.
    simp [T, hi0, hlast]
  have hT_super :
      ∀ i : Fin (n - 1), T ⟨i.1, by omega⟩ ⟨i.1 + 1, by omega⟩ = -w i := by
    intro i
    -- The first superdiagonal is exactly the negative edge weight.
    simp [T]
  have hT_sub :
      ∀ i : Fin (n - 1), T ⟨i.1 + 1, by omega⟩ ⟨i.1, by omega⟩ = -w i := by
    intro i
    -- The first subdiagonal matches the same negative edge weight by symmetry of the stencil.
    have hdiag : (⟨i.1 + 1, by omega⟩ : Fin n) ≠ ⟨i.1, by omega⟩ := by
      intro h
      have hval : i.1 + 1 = i.1 := by simpa using congrArg Fin.val h
      omega
    have hij1 : (⟨i.1, by omega⟩ : Fin n).1 ≠ (⟨i.1 + 1, by omega⟩ : Fin n).1 + 1 := by
      show i.1 ≠ i.1 + 2
      omega
    have hji1 : (⟨i.1 + 1, by omega⟩ : Fin n).1 = (⟨i.1, by omega⟩ : Fin n).1 + 1 := by
      simp
    simp [T, hdiag, hij1, hji1]
  have hT_far :
      ∀ i j : Fin n, 1 < Int.natAbs (i.1 - j.1) → T i j = 0 := by
    intro i j hij
    have hdiag : i ≠ j := by
      intro hij_eq
      subst hij_eq
      simpa using hij
    have hij1 : j.1 ≠ i.1 + 1 := by omega
    have hji1 : i.1 ≠ j.1 + 1 := by omega
    -- Away from the diagonal and first off-diagonals, `T` is zero by definition.
    simp [T, hdiag, hij1, hji1]
  have hEdgeTerm_zero_of_nonincident_left :
      ∀ i j : Fin n, ∀ k : Fin (n - 1),
        i ≠ ⟨k.1 + 1, by omega⟩ →
        i ≠ ⟨k.1, by omega⟩ →
        edgeTerm i j k = 0 := by
    intro i j k hik1 hik0
    -- If the left index misses both endpoints of edge `k`, the whole contribution vanishes.
    simp [edgeTerm, hik1, hik0]
  have hEdgeTerm_zero_of_nonincident_right :
      ∀ i j : Fin n, ∀ k : Fin (n - 1),
        j ≠ ⟨k.1 + 1, by omega⟩ →
        j ≠ ⟨k.1, by omega⟩ →
        edgeTerm i j k = 0 := by
    intro i j k hjk1 hjk0
    -- The same support statement holds for the right index.
    simp [edgeTerm, hjk1, hjk0]
  have hEdgeTerm_symm :
      ∀ i j : Fin n, ∀ k : Fin (n - 1), edgeTerm i j k = edgeTerm j i k := by
    intro i j k
    -- Swapping the two signed incidence factors does not change their product.
    dsimp [edgeTerm]
    ring
  have hEdgeSum_symm :
      ∀ i j : Fin n, edgeSum i j = edgeSum j i := by
    intro i j
    -- Sum the pointwise edge symmetry over all edges.
    unfold edgeSum
    refine Finset.sum_congr rfl ?_
    intro k hk
    exact hEdgeTerm_symm i j k
  have hEdgeSum_diag_zero :
      ∀ i : Fin n, i.1 = 0 → edgeSum i i = w ⟨0, by omega⟩ := by
    intro i hi0
    have hi : i = ⟨0, by omega⟩ := by
      apply Fin.ext
      change i.1 = 0
      omega
    have hstep : edgeSum ⟨0, by omega⟩ ⟨0, by omega⟩ = w ⟨0, by omega⟩ := by
      -- Only the first edge touches the left endpoint.
      unfold edgeSum
      rw [Finset.sum_eq_single ⟨0, by omega⟩]
      · simp [edgeTerm]
      · intro k hk hk0
        have hk_ne_zero : k.1 ≠ 0 := by
          intro hk_zero
          apply hk0
          apply Fin.ext
          simpa using hk_zero
        have hk0' : (⟨0, by omega⟩ : Fin n) ≠ ⟨k.1, by omega⟩ := by
          intro h
          have hval : 0 = k.1 := by simpa using congrArg Fin.val h
          exact hk_ne_zero hval.symm
        have hk1' : (⟨0, by omega⟩ : Fin n) ≠ ⟨k.1 + 1, by omega⟩ := by
          intro h
          have hval : 0 = k.1 + 1 := by simpa using congrArg Fin.val h
          omega
        exact hEdgeTerm_zero_of_nonincident_left _ _ _ hk1' hk0'
      · intro hk
        exfalso
        exact hk (Finset.mem_univ _)
    simpa [hi] using hstep
  have hEdgeSum_diag_mid :
      ∀ i : Fin n, ∀ hi1 : 1 ≤ i.1, ∀ hi2 : i.1 + 1 < n,
        edgeSum i i = w ⟨i.1 - 1, by omega⟩ + w ⟨i.1, by omega⟩ := by
    intro i hi1 hi2
    let km1 : Fin (n - 1) := ⟨i.1 - 1, by omega⟩
    let ki : Fin (n - 1) := ⟨i.1, by omega⟩
    have hsubset : ({km1, ki} : Finset (Fin (n - 1))) ⊆ Finset.univ := by
      intro k hk
      simp
    have hrestrict :
        ∑ k ∈ ({km1, ki} : Finset (Fin (n - 1))), edgeTerm i i k =
          ∑ k : Fin (n - 1), edgeTerm i i k := by
      -- Route correction: restrict the sum to the two incident edges before evaluating it.
      refine Finset.sum_subset hsubset ?_
      intro k hk hknot
      have hk_ne_km1 : k ≠ km1 := by
        intro hk_eq
        exact hknot (by simp [hk_eq])
      have hk_ne_ki : k ≠ ki := by
        intro hk_eq
        exact hknot (by simp [hk_eq])
      have hik1 : i ≠ ⟨k.1 + 1, by omega⟩ := by
        intro h
        have hk_eq : k = km1 := by
          apply Fin.ext
          dsimp [km1]
          have hval : i.1 = k.1 + 1 := by simpa using congrArg Fin.val h
          omega
        exact hk_ne_km1 hk_eq
      have hik0 : i ≠ ⟨k.1, by omega⟩ := by
        intro h
        have hk_eq : k = ki := by
          apply Fin.ext
          dsimp [ki]
          have hval : i.1 = k.1 := by simpa using congrArg Fin.val h
          omega
        exact hk_ne_ki hk_eq
      exact hEdgeTerm_zero_of_nonincident_left _ _ _ hik1 hik0
    have hkm1_ne_ki : km1 ≠ ki := by
      intro h
      have hval : km1.1 = ki.1 := by simpa using congrArg Fin.val h
      dsimp [km1, ki] at hval
      omega
    have hkm1_hit : i = ⟨km1.1 + 1, by omega⟩ := by
      apply Fin.ext
      dsimp [km1]
      omega
    have hki_hit : i = ⟨ki.1, by omega⟩ := by
      simpa [ki]
    have hki_miss : i ≠ ⟨ki.1 + 1, by omega⟩ := by
      intro h
      have hneq : (⟨ki.1, by omega⟩ : Fin n) ≠ ⟨ki.1 + 1, by omega⟩ := by
        intro hEq
        have hval : ki.1 = ki.1 + 1 := by simpa using congrArg Fin.val hEq
        omega
      exact hneq (hki_hit.symm.trans h)
    have hkm1_val : edgeTerm i i km1 = w km1 := by
      simp [edgeTerm, hkm1_hit]
    have hki_val : edgeTerm i i ki = w ki := by
      simp [edgeTerm, hki_hit, hki_miss]
    -- After restriction, the two surviving singleton terms evaluate to the desired weights.
    calc
      edgeSum i i = ∑ k ∈ ({km1, ki} : Finset (Fin (n - 1))), edgeTerm i i k := by
        symm
        simpa [edgeSum] using hrestrict
      _ = edgeTerm i i km1 + edgeTerm i i ki := by
        rw [Finset.sum_pair hkm1_ne_ki]
      _ = w km1 + w ki := by
        rw [hkm1_val, hki_val]
  have hEdgeSum_diag_last :
      ∀ i : Fin n, i.1 + 1 = n → edgeSum i i = w ⟨n - 2, by omega⟩ := by
    intro i hlast
    have hi : i = ⟨n - 1, by omega⟩ := by
      apply Fin.ext
      change i.1 = n - 1
      omega
    have hstep : edgeSum ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ = w ⟨n - 2, by omega⟩ := by
      -- Only the final edge touches the right endpoint.
      unfold edgeSum
      rw [Finset.sum_eq_single ⟨n - 2, by omega⟩]
      · have hhit : (⟨n - 1, by omega⟩ : Fin n) = ⟨(⟨n - 2, by omega⟩ : Fin (n - 1)).1 + 1, by omega⟩ := by
          apply Fin.ext
          change n - 1 = (⟨n - 2, by omega⟩ : Fin (n - 1)).1 + 1
          simp
          omega
        simp [edgeTerm, hhit]
      · intro k hk hk_last
        have hk1' : (⟨n - 1, by omega⟩ : Fin n) ≠ ⟨k.1 + 1, by omega⟩ := by
          intro h
          have hk_eq : k = ⟨n - 2, by omega⟩ := by
            apply Fin.ext
            have hval : n - 1 = k.1 + 1 := by simpa using congrArg Fin.val h
            change k.1 = n - 2
            omega
          exact hk_last hk_eq
        have hk0' : (⟨n - 1, by omega⟩ : Fin n) ≠ ⟨k.1, by omega⟩ := by
          intro h
          have hval : n - 1 = k.1 := by simpa using congrArg Fin.val h
          omega
        exact hEdgeTerm_zero_of_nonincident_left _ _ _ hk1' hk0'
      · intro hk
        exfalso
        exact hk (Finset.mem_univ _)
    simpa [hi] using hstep
  have hEdgeSum_super :
      ∀ i : Fin (n - 1), edgeSum ⟨i.1, by omega⟩ ⟨i.1 + 1, by omega⟩ = -w i := by
    intro i
    -- The adjacent pair is connected by exactly one edge, namely edge `i`.
    unfold edgeSum
    rw [Finset.sum_eq_single i]
    · have hi0 : (⟨i.1, by omega⟩ : Fin n) ≠ ⟨i.1 + 1, by omega⟩ := by
        intro h
        have hval : i.1 = i.1 + 1 := by simpa using congrArg Fin.val h
        omega
      simp [edgeTerm, hi0]
    · intro k hk hk_ne
      by_cases hj1 : (⟨i.1 + 1, by omega⟩ : Fin n) = ⟨k.1 + 1, by omega⟩
      · have hk_eq : k = i := by
          apply Fin.ext
          have hval : i.1 + 1 = k.1 + 1 := by simpa using congrArg Fin.val hj1
          omega
        exact (hk_ne hk_eq).elim
      · by_cases hj0 : (⟨i.1 + 1, by omega⟩ : Fin n) = ⟨k.1, by omega⟩
        · have hik1 : (⟨i.1, by omega⟩ : Fin n) ≠ ⟨k.1 + 1, by omega⟩ := by
            intro h
            have hval : i.1 = k.1 + 1 := by simpa using congrArg Fin.val h
            have hj0val : i.1 + 1 = k.1 := by simpa using congrArg Fin.val hj0
            omega
          have hik0 : (⟨i.1, by omega⟩ : Fin n) ≠ ⟨k.1, by omega⟩ := by
            intro h
            have hval : i.1 = k.1 := by simpa using congrArg Fin.val h
            have hj0val : i.1 + 1 = k.1 := by simpa using congrArg Fin.val hj0
            omega
          exact hEdgeTerm_zero_of_nonincident_left _ _ _ hik1 hik0
        · exact hEdgeTerm_zero_of_nonincident_right _ _ _ hj1 hj0
    · intro hi
      exfalso
      exact hi (Finset.mem_univ _)
  have hEdgeSum_sub :
      ∀ i : Fin (n - 1), edgeSum ⟨i.1 + 1, by omega⟩ ⟨i.1, by omega⟩ = -w i := by
    intro i
    -- The lower adjacent entry is the symmetric counterpart of the upper one.
    rw [hEdgeSum_symm]
    exact hEdgeSum_super i
  have hEdgeSum_far :
      ∀ i j : Fin n,
        i ≠ j →
        j.1 ≠ i.1 + 1 →
        i.1 ≠ j.1 + 1 →
        edgeSum i j = 0 := by
    intro i j hij hij1 hji1
    -- If the vertices are neither equal nor adjacent, no edge is incident to both.
    unfold edgeSum
    refine Finset.sum_eq_zero ?_
    intro k hk
    by_cases hjk1 : j = ⟨k.1 + 1, by omega⟩
    · have hik1 : i ≠ ⟨k.1 + 1, by omega⟩ := by
        intro h
        exact hij (h.trans hjk1.symm)
      have hik0 : i ≠ ⟨k.1, by omega⟩ := by
        intro h
        have hival : i.1 = k.1 := by simpa using congrArg Fin.val h
        have hjval : j.1 = k.1 + 1 := by simpa using congrArg Fin.val hjk1
        exact hij1 (by omega)
      exact hEdgeTerm_zero_of_nonincident_left _ _ _ hik1 hik0
    · by_cases hjk0 : j = ⟨k.1, by omega⟩
      · have hik1 : i ≠ ⟨k.1 + 1, by omega⟩ := by
          intro h
          have hival : i.1 = k.1 + 1 := by simpa using congrArg Fin.val h
          have hjval : j.1 = k.1 := by simpa using congrArg Fin.val hjk0
          exact hji1 (by omega)
        have hik0 : i ≠ ⟨k.1, by omega⟩ := by
          intro h
          exact hij (h.trans hjk0.symm)
        exact hEdgeTerm_zero_of_nonincident_left _ _ _ hik1 hik0
      · exact hEdgeTerm_zero_of_nonincident_right _ _ _ hjk1 hjk0
  have hEdgeSum_eq_T :
      ∀ i j : Fin n, edgeSum i j = T i j := by
    intro i j
    by_cases hdiag : i = j
    · cases hdiag
      by_cases hi0 : i.1 = 0
      · rw [hEdgeSum_diag_zero _ hi0, hT_diag_zero _ hi0]
      · by_cases hlast : i.1 + 1 = n
        · rw [hEdgeSum_diag_last _ hlast, hT_diag_last _ hlast]
        · have hi1 : 1 ≤ i.1 := by omega
          have hi2 : i.1 + 1 < n := by omega
          rw [hEdgeSum_diag_mid _ hi1 hi2, hT_diag_mid _ hi1 hi2]
    · by_cases hij1 : j.1 = i.1 + 1
      · have hj : j = ⟨i.1 + 1, by omega⟩ := by
          apply Fin.ext
          omega
        have hstep : edgeSum i ⟨i.1 + 1, by omega⟩ = T i ⟨i.1 + 1, by omega⟩ := by
          rw [hEdgeSum_super ⟨i.1, by omega⟩, hT_super ⟨i.1, by omega⟩]
        simpa [hj] using hstep
      · by_cases hji1 : i.1 = j.1 + 1
        · have hi' : i = ⟨j.1 + 1, by omega⟩ := by
            apply Fin.ext
            omega
          have hstep : edgeSum ⟨j.1 + 1, by omega⟩ j = T ⟨j.1 + 1, by omega⟩ j := by
            rw [hEdgeSum_sub ⟨j.1, by omega⟩, hT_sub ⟨j.1, by omega⟩]
          simpa [hi'] using hstep
        · rw [hEdgeSum_far _ _ hdiag hij1 hji1]
          simp [T, hdiag, hij1, hji1]
  have hT_symm : T.IsSymm := by
    -- Transport symmetry from the edge-incidence formula to the explicit stencil `T`.
    apply Matrix.IsSymm.ext
    intro i j
    rw [← hEdgeSum_eq_T j i, ← hEdgeSum_eq_T i j, hEdgeSum_symm]
  have hH_entry :
      ∀ i j : Fin n, H i j = (if i = j then 2 else 0) + μ * edgeSum i j := by
    intro i j
    let q : (Fin n → ℝ) → ℝ := fun y => l2Norm (y - xcor) ^ 2
    have hqDiff :
        ∀ y : Fin n → ℝ, DifferentiableAt ℝ q y := by
      intro y
      -- The quadratic fidelity term is a finite sum of differentiable coordinate squares.
      have hqfun :
          q = ∑ k : Fin n, fun z : Fin n → ℝ => (z k - xcor k) ^ 2 := by
        funext z
        simp [q, l2Norm_sub_sq_eq_sum_sq]
      rw [hqfun]
      refine DifferentiableAt.sum ?_
      intro k hk
      fun_prop
    have hφDiff :
        ∀ y : Fin n → ℝ, DifferentiableAt ℝ φ_atv y := by
      intro y
      -- The ATV term is a finite sum of differentiable edge penalties.
      have hφfun :
          φ_atv =
            ∑ k : Fin (n - 1), fun z : Fin n → ℝ =>
              (Real.sqrt (ε ^ 2 + (z ⟨k.1 + 1, by omega⟩ - z ⟨k.1, by omega⟩) ^ 2) - ε) := by
        funext z
        simp [φ_atv]
      rw [hφfun]
      refine DifferentiableAt.sum ?_
      intro k hk
      simpa using atv_edge_differentiableAt hn ε hε k y
    have hψSplit :
        (fun y : Fin n → ℝ => (fderiv ℝ ψ y) (Pi.single j (1 : ℝ))) =
          fun y : Fin n → ℝ =>
            (fderiv ℝ q y) (Pi.single j (1 : ℝ)) +
              μ * (fderiv ℝ φ_atv y) (Pi.single j (1 : ℝ)) := by
      funext y
      -- Split the first derivative of `ψ = q + μ • φ_atv` into its quadratic and ATV parts.
      have hdiffq : DifferentiableAt ℝ q y := hqDiff y
      have hdiffφ : DifferentiableAt ℝ φ_atv y := hφDiff y
      have hadd :
          fderiv ℝ ψ y =
            fderiv ℝ q y + fderiv ℝ (fun z : Fin n → ℝ => μ * φ_atv z) y := by
        simpa [ψ, q] using
          (fderiv_add (f := q) (g := fun z : Fin n → ℝ => μ * φ_atv z) (x := y)
            hdiffq (hdiffφ.const_mul μ))
      have hsmul :
          fderiv ℝ (fun z : Fin n → ℝ => μ * φ_atv z) y = μ • fderiv ℝ φ_atv y := by
        simpa using (fderiv_const_mul hdiffφ μ)
      calc
        (fderiv ℝ ψ y) (Pi.single j (1 : ℝ)) =
            (fderiv ℝ q y + fderiv ℝ (fun z : Fin n → ℝ => μ * φ_atv z) y)
              (Pi.single j (1 : ℝ)) := by rw [hadd]
        _ = (fderiv ℝ q y) (Pi.single j (1 : ℝ)) +
              μ * (fderiv ℝ φ_atv y) (Pi.single j (1 : ℝ)) := by
            rw [hsmul]
            simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    have hqfun :
        (fun y : Fin n → ℝ => (fderiv ℝ q y) (Pi.single j (1 : ℝ))) =
          fun y : Fin n → ℝ => 2 * (y j - xcor j) := by
      funext y
      simpa [q] using quadratic_fidelity_first_derivative_apply y xcor j
    have hqDirDiff :
        DifferentiableAt ℝ (fun y : Fin n → ℝ => (fderiv ℝ q y) (Pi.single j (1 : ℝ))) x := by
      rw [hqfun]
      fun_prop
    have hφDirDiff :
        DifferentiableAt ℝ (fun y : Fin n → ℝ => (fderiv ℝ φ_atv y) (Pi.single j (1 : ℝ))) x := by
      simpa [φ_atv] using atv_first_directional_differentiableAt hn x ε hε j
    -- Differentiate the split first-derivative formula one more time at `x`.
    unfold H
    rw [hψSplit]
    have hadd :
        fderiv ℝ
            (fun y : Fin n → ℝ =>
              (fderiv ℝ q y) (Pi.single j (1 : ℝ)) +
                μ * (fderiv ℝ φ_atv y) (Pi.single j (1 : ℝ))) x =
          fderiv ℝ (fun y : Fin n → ℝ => (fderiv ℝ q y) (Pi.single j (1 : ℝ))) x +
            fderiv ℝ
              (fun y : Fin n → ℝ => μ * (fderiv ℝ φ_atv y) (Pi.single j (1 : ℝ))) x := by
      simpa using
        (fderiv_add
          (f := fun y : Fin n → ℝ => (fderiv ℝ q y) (Pi.single j (1 : ℝ)))
          (g := fun y : Fin n → ℝ => μ * (fderiv ℝ φ_atv y) (Pi.single j (1 : ℝ)))
          (x := x) hqDirDiff (hφDirDiff.const_mul μ))
    have hsmul :
        fderiv ℝ (fun y : Fin n → ℝ => μ * (fderiv ℝ φ_atv y) (Pi.single j (1 : ℝ))) x =
          μ • fderiv ℝ (fun y : Fin n → ℝ => (fderiv ℝ φ_atv y) (Pi.single j (1 : ℝ))) x := by
      simpa using (fderiv_const_mul hφDirDiff μ)
    calc
      (fderiv ℝ
          (fun y : Fin n → ℝ =>
            (fderiv ℝ q y) (Pi.single j (1 : ℝ)) +
              μ * (fderiv ℝ φ_atv y) (Pi.single j (1 : ℝ))) x)
          (Pi.single i (1 : ℝ)) =
          (fderiv ℝ (fun y : Fin n → ℝ => (fderiv ℝ q y) (Pi.single j (1 : ℝ))) x)
              (Pi.single i (1 : ℝ)) +
            (fderiv ℝ (fun y : Fin n → ℝ => μ * (fderiv ℝ φ_atv y) (Pi.single j (1 : ℝ))) x)
              (Pi.single i (1 : ℝ)) := by
              rw [hadd]
              simp [ContinuousLinearMap.add_apply]
      _ =
          (fderiv ℝ (fun y : Fin n → ℝ => (fderiv ℝ q y) (Pi.single j (1 : ℝ))) x)
              (Pi.single i (1 : ℝ)) +
            μ *
              (fderiv ℝ (fun y : Fin n → ℝ => (fderiv ℝ φ_atv y) (Pi.single j (1 : ℝ))) x)
                (Pi.single i (1 : ℝ)) := by
              rw [hsmul]
              simp [ContinuousLinearMap.smul_apply]
      _ = (if i = j then 2 else 0) + μ * edgeSum i j := by
        rw [quadratic_fidelity_hessian_entry, hATVEntry]
  have hH :
      H = 2 • (1 : Matrix (Fin n) (Fin n) ℝ) + μ • T := by
    -- Identify every Hessian entry with the quadratic diagonal plus the tridiagonal ATV stencil.
    apply Matrix.ext
    intro i j
    rw [hH_entry, hEdgeSum_eq_T]
    simp_rw [Matrix.add_apply, Matrix.smul_apply]
    by_cases hij : i = j
    · simp [hij, Matrix.one_apply]
    · simp [hij, Matrix.one_apply]
  have hH_far :
      ∀ i j : Fin n, 1 < Int.natAbs (i.1 - j.1) → H i j = 0 := by
    intro i j hij
    have hdiag : i ≠ j := by
      intro hij_eq
      subst hij_eq
      simpa using hij
    -- The Hessian inherits the far-off-diagonal vanishing from `T`.
    rw [hH]
    simp_rw [Matrix.add_apply, Matrix.smul_apply]
    have hone : ((1 : Matrix (Fin n) (Fin n) ℝ) i j) = 0 := by
      simp [Matrix.one_apply, hdiag]
    simp [hone, hT_far _ _ hij]
  have hHSymm : H.IsSymm := by
    -- Symmetry comes from `H = 2 • 1 + μ • T` and the symmetry of both summands.
    rw [hH]
    exact (Matrix.isSymm_one : (1 : Matrix (Fin n) (Fin n) ℝ).IsSymm).smul 2 |>.add (hT_symm.smul μ)
  have hHtridiag : IsSymmetricTridiagonal H := by
    -- Collect the symmetry and far-off-diagonal vanishing into the tridiagonal predicate.
    exact ⟨hHSymm, hH_far⟩
  refine ⟨hH, hHtridiag, hT_diag_zero, hT_diag_mid, hT_diag_last, hT_super, hT_sub, hT_far, ?_⟩
  intro p hp
  -- A Newton direction already solves the tridiagonal linear system, so it witnesses the
  -- Thomas-type branch directly.
  right
  refine ⟨hH_far, ?_⟩
  refine ⟨fun _ _ => p, thomasTypeOperationCount n, ?_, ?_⟩
  · simpa [IsLinearSystem, IsNewtonDirectionAt] using hp
  · simp [thomasTypeOperationCount]

end «problem-167»
