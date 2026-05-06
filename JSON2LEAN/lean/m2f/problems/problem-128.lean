import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-128»
/-
Given a differentiable function f: ℝ^n → ℝ, an iterative method is called a ∇descent iteration if it
generates points by x^(k + 1) = x^(k) - α_k ∇ f(x^(k)), with step sizes α_k > 0.
-/
def IsGradientDescentIteration {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (_hf : Differentiable ℝ f) (x : ℕ → Fin n → ℝ) (α : ℕ → ℝ) : Prop :=
  ∀ k : ℕ,
    x (k + 1) = x k - α k • (fun i => (fderiv ℝ f (x k)) (Pi.single i (1 : ℝ))) ∧ 0 < α k

/-
Given x ∈ ℝ^n and a search direction p ∈ ℝ^n, an exact line search chooses α ∈ ℝ such that f(x + α
p) = min_t ∈ ℝ f(x + tp).
-/
def IsExactLineSearch {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x p : Fin n → ℝ) (α : ℝ) : Prop :=
  ∀ t : ℝ, f (x + α • p) ≤ f (x + t • p)

/-
Exercise 8.1 - (b) | 8 | algo

Starting from x^{(0)} = (γ, 1), consider the ∇descent iteration with exact line search: x^{(k + 1)}
=
x^{(k)} - αₖ ∇f(x^{(k)}), k ≥ 0, where αₖ ∈ ℝ satisfies f(x^{(k)} - αₖ ∇f(x^{(k)})) = min_{α ∈ ℝ}
f(x^{(k)} - α ∇f(x^{(k)})).
-/
structure GradientDescentWithExactLineSearch where
  γ : ℝ
  f : (Fin 2 → ℝ) → ℝ
  hf : Differentiable ℝ f
  x : ℕ → Fin 2 → ℝ
  α : ℕ → ℝ
  x0 : x 0 = ![γ, 1]
  gradient_descent : IsGradientDescentIteration f hf x α
  exact_line_search : ∀ k : ℕ,
    IsExactLineSearch f (x k)
      (-(fun i => (fderiv ℝ f (x k)) (Pi.single i (1 : ℝ))))
      (α k)

/-- The second coordinate directional derivative of `γ * x₀^2 - x₁^2` is `-2 * x₁`. -/
lemma second_directional_derivative
    (γ : ℝ) (x : Fin 2 → ℝ) :
    (fderiv ℝ (fun y : Fin 2 → ℝ => γ * (y 0)^2 - (y 1)^2) x)
      (Pi.single 1 (1 : ℝ)) = -2 * x 1 := by
  let proj0 : (Fin 2 → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0)
  let proj1 : (Fin 2 → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)
  -- Differentiate the first coordinate square through the coordinate projection.
  have hsq0 : HasDerivAt (fun r : ℝ => γ * r^2) (γ * (2 * x 0)) (x 0) := by
    simpa [pow_two, two_mul, mul_assoc, mul_left_comm, mul_comm] using
      ((hasDerivAt_id (x 0)).pow 2).const_mul γ
  have happly0 : HasFDerivAt (fun y : Fin 2 → ℝ => y 0) proj0 x := by
    simpa [proj0] using (hasFDerivAt_apply 0 x)
  have h0 :
      HasFDerivAt (fun y : Fin 2 → ℝ => γ * (y 0)^2) ((γ * (2 * x 0)) • proj0) x := by
    simpa [Function.comp, proj0] using hsq0.comp_hasFDerivAt x happly0
  -- Differentiate the second coordinate square through the other projection.
  have hsq1 : HasDerivAt (fun r : ℝ => (r : ℝ)^2) (2 * x 1) (x 1) := by
    simpa [pow_two, two_mul, mul_assoc, mul_left_comm, mul_comm] using
      ((hasDerivAt_id (x 1)).pow 2)
  have happly1 : HasFDerivAt (fun y : Fin 2 → ℝ => y 1) proj1 x := by
    simpa [proj1] using (hasFDerivAt_apply 1 x)
  have h1 : HasFDerivAt (fun y : Fin 2 → ℝ => (y 1)^2) ((2 * x 1) • proj1) x := by
    simpa [Function.comp, proj1] using hsq1.comp_hasFDerivAt x happly1
  -- Combine the two one-variable derivatives into the derivative of the full quadratic.
  have hmain :
      HasFDerivAt (fun y : Fin 2 → ℝ => γ * (y 0)^2 - (y 1)^2)
        (((γ * (2 * x 0)) • proj0) - ((2 * x 1) • proj1)) x := by
    simpa [sub_eq_add_neg] using h0.sub h1
  have hfderiv :
      fderiv ℝ (fun y : Fin 2 → ℝ => γ * (y 0)^2 - (y 1)^2) x =
        ((γ * (2 * x 0)) • proj0) - ((2 * x 1) • proj1) := hmain.fderiv
  -- Evaluate the resulting linear map on the `e₁` direction.
  have happly :=
    congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L (Pi.single 1 (1 : ℝ))) hfderiv
  simpa [proj0, proj1] using happly

/-- The first coordinate directional derivative of `γ * x₀^2 - x₁^2` is `2 * γ * x₀`. -/
lemma first_directional_derivative
    (γ : ℝ) (x : Fin 2 → ℝ) :
    (fderiv ℝ (fun y : Fin 2 → ℝ => γ * (y 0)^2 - (y 1)^2) x)
      (Pi.single 0 (1 : ℝ)) = 2 * γ * x 0 := by
  let proj0 : (Fin 2 → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0)
  let proj1 : (Fin 2 → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)
  -- Differentiate the first coordinate square through the coordinate projection.
  have hsq0 : HasDerivAt (fun r : ℝ => γ * r^2) (γ * (2 * x 0)) (x 0) := by
    simpa [pow_two, two_mul, mul_assoc, mul_left_comm, mul_comm] using
      ((hasDerivAt_id (x 0)).pow 2).const_mul γ
  have happly0 : HasFDerivAt (fun y : Fin 2 → ℝ => y 0) proj0 x := by
    simpa [proj0] using (hasFDerivAt_apply 0 x)
  have h0 :
      HasFDerivAt (fun y : Fin 2 → ℝ => γ * (y 0)^2) ((γ * (2 * x 0)) • proj0) x := by
    simpa [Function.comp, proj0] using hsq0.comp_hasFDerivAt x happly0
  -- Differentiate the second coordinate square through the other projection.
  have hsq1 : HasDerivAt (fun r : ℝ => (r : ℝ)^2) (2 * x 1) (x 1) := by
    simpa [pow_two, two_mul, mul_assoc, mul_left_comm, mul_comm] using
      ((hasDerivAt_id (x 1)).pow 2)
  have happly1 : HasFDerivAt (fun y : Fin 2 → ℝ => y 1) proj1 x := by
    simpa [proj1] using (hasFDerivAt_apply 1 x)
  have h1 : HasFDerivAt (fun y : Fin 2 → ℝ => (y 1)^2) ((2 * x 1) • proj1) x := by
    simpa [Function.comp, proj1] using hsq1.comp_hasFDerivAt x happly1
  -- Combine the two one-variable derivatives into the derivative of the full quadratic.
  have hmain :
      HasFDerivAt (fun y : Fin 2 → ℝ => γ * (y 0)^2 - (y 1)^2)
        (((γ * (2 * x 0)) • proj0) - ((2 * x 1) • proj1)) x := by
    simpa [sub_eq_add_neg] using h0.sub h1
  have hfderiv :
      fderiv ℝ (fun y : Fin 2 → ℝ => γ * (y 0)^2 - (y 1)^2) x =
        ((γ * (2 * x 0)) • proj0) - ((2 * x 1) • proj1) := hmain.fderiv
  -- Evaluate the resulting linear map on the `e₀` direction.
  have happly :=
    congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L (Pi.single 0 (1 : ℝ))) hfderiv
  simpa [proj0, proj1, two_mul, mul_assoc, mul_left_comm, mul_comm] using happly

/-- For `γ > 1`, the denominator `γ^5 - 1` is positive. -/
lemma gamma_five_sub_one_pos {γ : ℝ} (hγ : 1 < γ) : 0 < γ ^ 5 - 1 := by
  have hγm1 : 0 < γ - 1 := by
    linarith
  have hsum : 0 < γ ^ 4 + γ ^ 3 + γ ^ 2 + γ + 1 := by
    have hγpos : 0 < γ := by
      linarith
    positivity
  have hfactor : γ ^ 5 - 1 = (γ - 1) * (γ ^ 4 + γ ^ 3 + γ ^ 2 + γ + 1) := by
    ring
  rw [hfactor]
  positivity

/-- For `γ > 1`, the factor `γ^3 - 1` is positive. -/
lemma gamma_three_sub_one_pos {γ : ℝ} (hγ : 1 < γ) : 0 < γ ^ 3 - 1 := by
  have hγm1 : 0 < γ - 1 := by
    linarith
  have hsum : 0 < γ ^ 2 + γ + 1 := by
    have hγpos : 0 < γ := by
      linarith
    positivity
  have hfactor : γ ^ 3 - 1 = (γ - 1) * (γ ^ 2 + γ + 1) := by
    ring
  rw [hfactor]
  positivity

/-- Along the negative-gradient line, the quadratic model reduces to an explicit scalar quadratic. -/
lemma model_line_search_expansion
    (γ : ℝ) (x : Fin 2 → ℝ) (t : ℝ) :
    (fun y : Fin 2 → ℝ => γ * (y 0)^2 - (y 1)^2)
      (x + t • (-(fun i => (fderiv ℝ (fun y : Fin 2 → ℝ => γ * (y 0)^2 - (y 1)^2) x)
        (Pi.single i (1 : ℝ)))))
      =
        γ * (x 0)^2 - (x 1)^2
          - 4 * (γ^2 * (x 0)^2 + (x 1)^2) * t
          + 4 * (γ^3 * (x 0)^2 - (x 1)^2) * t^2 := by
  -- Expand both coordinates of the search line using the directional derivative formulas.
  have h0 := first_directional_derivative γ x
  have h1 := second_directional_derivative γ x
  have h0' :
      (fderiv ℝ (fun y : Fin 2 → ℝ => γ * (y 0)^2 + -(y 1)^2) x)
        (Pi.single 0 (1 : ℝ)) = 2 * γ * x 0 := by
    simpa [sub_eq_add_neg] using h0
  have h1' :
      (fderiv ℝ (fun y : Fin 2 → ℝ => γ * (y 0)^2 + -(y 1)^2) x)
        (Pi.single 1 (1 : ℝ)) = -2 * x 1 := by
    simpa [sub_eq_add_neg] using h1
  have hcoord0 :
      (x + t • (-(fun i => (fderiv ℝ (fun y : Fin 2 → ℝ => γ * (y 0)^2 - (y 1)^2) x)
        (Pi.single i (1 : ℝ))))) 0
        =
          x 0 - t * (2 * γ * x 0) := by
    simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, h0', sub_eq_add_neg]
  have hcoord1 :
      (x + t • (-(fun i => (fderiv ℝ (fun y : Fin 2 → ℝ => γ * (y 0)^2 - (y 1)^2) x)
        (Pi.single i (1 : ℝ))))) 1
        =
          x 1 - t * (-2 * x 1) := by
    simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, h1', sub_eq_add_neg]
  change
    γ * ((x + t • (-(fun i => (fderiv ℝ (fun y : Fin 2 → ℝ => γ * (y 0)^2 - (y 1)^2) x)
      (Pi.single i (1 : ℝ))))) 0) ^ 2
      - ((x + t • (-(fun i => (fderiv ℝ (fun y : Fin 2 → ℝ => γ * (y 0)^2 - (y 1)^2) x)
        (Pi.single i (1 : ℝ))))) 1) ^ 2
      =
        γ * (x 0)^2 - (x 1)^2
          - 4 * (γ^2 * (x 0)^2 + (x 1)^2) * t
          + 4 * (γ^3 * (x 0)^2 - (x 1)^2) * t^2
  rw [hcoord0, hcoord1]
  ring

/-- A globally minimizing exact line search can only occur in a nonnegative-curvature region. -/
lemma exact_line_search_nonnegative_curvature
    (γ α : ℝ) (x : Fin 2 → ℝ)
    (hsearch : IsExactLineSearch
      (fun y : Fin 2 → ℝ => γ * (y 0)^2 - (y 1)^2)
      x
      (-(fun i => (fderiv ℝ (fun y : Fin 2 → ℝ => γ * (y 0)^2 - (y 1)^2) x)
        (Pi.single i (1 : ℝ))))
      α) :
    0 ≤ γ ^ 3 * (x 0)^2 - (x 1)^2 := by
  -- Compare the minimizing value with its two neighboring points `α ± 1`.
  have hplus := hsearch (α + 1)
  have hminus := hsearch (α - 1)
  rw [model_line_search_expansion γ x α, model_line_search_expansion γ x (α + 1)] at hplus
  rw [model_line_search_expansion γ x α, model_line_search_expansion γ x (α - 1)] at hminus
  have hsum := add_le_add hplus hminus
  nlinarith

/-- The first coordinate update for the quadratic model at the initial iterate. -/
lemma initial_first_coordinate_update
    (A : GradientDescentWithExactLineSearch)
    (hf : A.f = fun x : Fin 2 → ℝ => A.γ * (x 0)^2 - (x 1)^2) :
    A.x 1 0 = A.γ - 2 * A.γ^2 * A.α 0 := by
  -- Expand the `k = 0` gradient-descent recurrence on the first coordinate.
  obtain ⟨hstep, _hα⟩ := A.gradient_descent 0
  have hstep0 :
      A.x 1 0 = (A.x 0 - A.α 0 • fun i => (fderiv ℝ A.f (A.x 0)) (Pi.single i 1)) 0 := by
    exact congrFun hstep 0
  -- Rewrite the model function and the initial point, then compute the derivative explicitly.
  rw [hf, A.x0] at hstep0
  simp [Pi.sub_apply, Pi.smul_apply, first_directional_derivative] at hstep0
  linarith

/-- The first gradient-descent step forces the second coordinate to move upward. -/
lemma initial_second_coordinate_update
    (A : GradientDescentWithExactLineSearch)
    (hf : A.f = fun x : Fin 2 → ℝ => A.γ * (x 0)^2 - (x 1)^2) :
    A.x 1 1 = 1 + 2 * A.α 0 := by
  -- Expand the `k = 0` gradient-descent recurrence on the second coordinate.
  obtain ⟨hstep, _hα⟩ := A.gradient_descent 0
  have hstep1 :
      A.x 1 1 = (A.x 0 - A.α 0 • fun i => (fderiv ℝ A.f (A.x 0)) (Pi.single i 1)) 1 := by
    exact congrFun hstep 1
  -- Rewrite the model function and the initial point, then compute the derivative explicitly.
  rw [hf, A.x0] at hstep1
  simp [Pi.sub_apply, Pi.smul_apply, second_directional_derivative] at hstep1
  linarith

/-- Exact line search at the initial point determines the first step size uniquely. -/
lemma initial_exact_line_search_step
    (A : GradientDescentWithExactLineSearch) (hγ : 1 < A.γ)
    (hf : A.f = fun x : Fin 2 → ℝ => A.γ * (x 0)^2 - (x 1)^2) :
    A.α 0 = (A.γ ^ 4 + 1) / (2 * (A.γ ^ 5 - 1)) := by
  have hden : 0 < A.γ ^ 5 - 1 := gamma_five_sub_one_pos hγ
  have htwo_den : 2 * (A.γ ^ 5 - 1) ≠ 0 := by
    nlinarith
  set tStar : ℝ := (A.γ ^ 4 + 1) / (2 * (A.γ ^ 5 - 1)) with htStar
  -- Exact line search compares the actual step with the scalar minimizer of the quadratic model.
  have hexact := A.exact_line_search 0 tStar
  rw [hf, A.x0] at hexact
  rw [model_line_search_expansion A.γ ![A.γ, 1] (A.α 0),
    model_line_search_expansion A.γ ![A.γ, 1] tStar] at hexact
  simp at hexact
  have hnonneg : 0 ≤ 4 * (A.γ ^ 5 - 1) * (A.α 0 - tStar) ^ 2 := by
    positivity
  have hnonpos : 4 * (A.γ ^ 5 - 1) * (A.α 0 - tStar) ^ 2 ≤ 0 := by
    have hrewritten :
        4 * (A.γ ^ 5 - 1) * (A.α 0 - tStar) ^ 2
          =
            (A.γ ^ 3 - 1 - 4 * (A.γ ^ 4 + 1) * A.α 0 + 4 * (A.γ ^ 5 - 1) * (A.α 0) ^ 2) -
            (A.γ ^ 3 - 1 - 4 * (A.γ ^ 4 + 1) * tStar + 4 * (A.γ ^ 5 - 1) * tStar ^ 2) := by
      rw [htStar]
      field_simp [hden.ne', htwo_den]
      ring
    rw [hrewritten]
    linarith
  have hsq : (A.α 0 - tStar) ^ 2 = 0 := by
    nlinarith
  have hzero : A.α 0 - tStar = 0 := by
    exact sq_eq_zero_iff.mp hsq
  have hfinal : A.α 0 = tStar := sub_eq_zero.mp hzero
  simpa [htStar] using hfinal

/-- The first iterate has an explicit first coordinate under the quadratic model. -/
lemma initial_first_coordinate_closed_form
    (A : GradientDescentWithExactLineSearch) (hγ : 1 < A.γ)
    (hf : A.f = fun x : Fin 2 → ℝ => A.γ * (x 0)^2 - (x 1)^2) :
    A.x 1 0 = -A.γ * (A.γ + 1) / (A.γ ^ 5 - 1) := by
  have hden : A.γ ^ 5 - 1 ≠ 0 := (gamma_five_sub_one_pos hγ).ne'
  -- Substitute the exact initial step size into the first-coordinate update.
  rw [initial_first_coordinate_update A hf, initial_exact_line_search_step A hγ hf]
  field_simp [hden]
  ring

/-- The first iterate has an explicit second coordinate under the quadratic model. -/
lemma initial_second_coordinate_closed_form
    (A : GradientDescentWithExactLineSearch) (hγ : 1 < A.γ)
    (hf : A.f = fun x : Fin 2 → ℝ => A.γ * (x 0)^2 - (x 1)^2) :
    A.x 1 1 = A.γ ^ 4 * (A.γ + 1) / (A.γ ^ 5 - 1) := by
  have hden : A.γ ^ 5 - 1 ≠ 0 := (gamma_five_sub_one_pos hγ).ne'
  -- Substitute the exact initial step size into the second-coordinate update.
  rw [initial_second_coordinate_update A hf, initial_exact_line_search_step A hγ hf]
  field_simp [hden]
  ring

/-- After the first step, the next line-search quadratic has negative leading coefficient. -/
lemma first_iterate_has_negative_curvature
    (A : GradientDescentWithExactLineSearch) (hγ : 1 < A.γ)
    (hf : A.f = fun x : Fin 2 → ℝ => A.γ * (x 0)^2 - (x 1)^2) :
    A.γ ^ 3 * (A.x 1 0)^2 - (A.x 1 1)^2 < 0 := by
  have hden_pos : 0 < A.γ ^ 5 - 1 := gamma_five_sub_one_pos hγ
  have hden : A.γ ^ 5 - 1 ≠ 0 := hden_pos.ne'
  have hγ3 : 0 < A.γ ^ 3 - 1 := gamma_three_sub_one_pos hγ
  have hfactor : 0 < A.γ ^ 5 * (A.γ + 1) ^ 2 := by
    have hγpos : 0 < A.γ := by
      linarith
    positivity
  -- Rewrite the first iterate in closed form and clear the positive denominator square.
  rw [initial_first_coordinate_closed_form A hγ hf, initial_second_coordinate_closed_form A hγ hf]
  field_simp [hden]
  nlinarith

/-- The claimed closed form makes the second coordinate negative already at `k = 1`. -/
lemma claimed_second_coordinate_at_one_is_negative
    (A : GradientDescentWithExactLineSearch) (hγ : 1 < A.γ)
    (hcoords :
      ∀ k : ℕ,
        A.x k 0 = A.γ * ((A.γ - 1) / (A.γ + 1)) ^ k ∧
        A.x k 1 = (-((A.γ - 1) / (A.γ + 1))) ^ k) :
    A.x 1 1 < 0 := by
  -- Positivity of the ratio turns the `k = 1` closed form into a negative number.
  have hnum : 0 < A.γ - 1 := sub_pos.mpr hγ
  have hden : 0 < A.γ + 1 := by
    linarith
  have hratio : 0 < (A.γ - 1) / (A.γ + 1) := by
    positivity
  have h1 : A.x 1 1 = -((A.γ - 1) / (A.γ + 1)) := by
    simpa using (hcoords 1).2
  rw [h1]
  linarith

/-- The advertised coordinate formula contradicts the first gradient-descent update. -/
lemma coordinates_formula_contradiction
    (A : GradientDescentWithExactLineSearch) (hγ : 1 < A.γ)
    (hf : A.f = fun x : Fin 2 → ℝ => A.γ * (x 0)^2 - (x 1)^2)
    (hcoords :
      ∀ k : ℕ,
        A.x k 0 = A.γ * ((A.γ - 1) / (A.γ + 1)) ^ k ∧
        A.x k 1 = (-((A.γ - 1) / (A.γ + 1))) ^ k) :
    False := by
  -- The recurrence gives a strictly positive second coordinate after one step.
  have hα0 : 0 < A.α 0 := (A.gradient_descent 0).2
  have hpos_eq := initial_second_coordinate_update A hf
  have hpos : 0 < A.x 1 1 := by
    rw [hpos_eq]
    linarith
  -- The claimed formula gives the opposite sign at the same iterate.
  have hneg : A.x 1 1 < 0 := claimed_second_coordinate_at_one_is_negative A hγ hcoords
  linarith

theorem gradient_descent_with_exact_line_search_coordinates
    (A : GradientDescentWithExactLineSearch) (hγ : 1 < A.γ)
    (hf : A.f = fun x : Fin 2 → ℝ => A.γ * (x 0)^2 - (x 1)^2) :
    ∀ k : ℕ,
      A.x k 0 = A.γ * ((A.γ - 1) / (A.γ + 1)) ^ k ∧
      A.x k 1 = (-((A.γ - 1) / (A.γ + 1))) ^ k := by
  -- Route correction: the stronger issue is that the hypotheses are already inconsistent.
  -- Exact line search at `k = 1` forces nonnegative curvature, but the first step enters
  -- a region where the same quadratic has negative curvature.
  have hcurv :
      0 ≤ A.γ ^ 3 * (A.x 1 0)^2 - (A.x 1 1)^2 := by
    -- Rewrite the line-search model at `k = 1` and apply the quadratic comparison lemma.
    have hsearch := A.exact_line_search 1
    rw [hf] at hsearch
    exact exact_line_search_nonnegative_curvature A.γ (A.α 1) (A.x 1) hsearch
  have hbad : A.γ ^ 3 * (A.x 1 0)^2 - (A.x 1 1)^2 < 0 := by
    -- The explicit first iterate lies in the negative-curvature region.
    exact first_iterate_has_negative_curvature A hγ hf
  have hFalse : False := by
    linarith
  exact False.elim hFalse

/-
Let γ ≥ 1, and define f: ℝ^2 → ℝ by f(x₁, x₂) = γ x₁^2 - x₂^2. Starting from x^{(0)} = (γ, 1),
consider ∇descent with exact line search: x^{(k + 1)} = x^{(k)} - α_k ∇ f(x^{(k)}), k ≥ 0, where α_k
∈ ℝ
satisfies f(x^{(k)} - α_k ∇ f(x^{(k)})) = min_{α ∈ ℝ} f(x^{(k)} - α ∇ f(x^{(k)})). Show that x^{(k)}
→
(0, 0) and that f is unbounded below.
-/
theorem gradient_descent_with_exact_line_search_converges_to_zero_and_unbounded_below
    (A : GradientDescentWithExactLineSearch) (hγ : 1 < A.γ)
    (hf : A.f = fun x : Fin 2 → ℝ => A.γ * (x 0)^2 - (x 1)^2)
    (hcoords :
      ∀ k : ℕ,
        A.x k 0 = A.γ * ((A.γ - 1) / (A.γ + 1)) ^ k ∧
        A.x k 1 = (-((A.γ - 1) / (A.γ + 1))) ^ k) :
    Tendsto A.x atTop (𝓝 0) ∧
    ∀ M : ℝ, ∃ x : Fin 2 → ℝ, A.f x < M := by
  -- The supplied coordinate formula is already inconsistent with the first update.
  have hFalse : False := coordinates_formula_contradiction A hγ hf hcoords
  exact False.elim hFalse
end «problem-128»
