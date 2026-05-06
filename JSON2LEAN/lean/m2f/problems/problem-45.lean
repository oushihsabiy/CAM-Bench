import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-45»
/-
For a problem with objective function f₀ and inequality constraint functions fᵢ, the dual function
is the map g: ℝ^m → ℝ cup {- ∞} defined by g(λ) = inf_x∈ ℝ^n(f₀(x) + sum_i = 1^m λ_i fᵢ(x)).
-/
def dualFeasible {m : ℕ} (lam : Fin m → ℝ) : Prop :=
  ∀ i : Fin m, 0 ≤ lam i

/-
For t > 0, the centering problem is to minimize the logarithmic barrier objective x mapsto t
f₀(x) - sum_i = 1^m log(- fᵢ(x)) over the strict feasible set {x∈ ℝ^n| fᵢ(x) < 0 ∀ i}.
-/
def strictFeasibleSet {α : Type*} {m : ℕ} (fi : Fin m → α → ℝ) : Set α :=
  {x | ∀ i : Fin m, fi i x < 0}

def centeringObjective {α : Type*} {m : ℕ} (t : ℝ) (f0 : α → ℝ)
    (fi : Fin m → α → ℝ) (x : α) : EReal :=
  if _ : 0 < t then
    if _ : ∀ i : Fin m, fi i x < 0 then
      (t * f0 x : EReal) - ∑ i : Fin m, (Real.log (-fi i x) : EReal)
    else
      ⊤
  else
    ⊤

/-
Given inequality constraint functions fᵢ, the logarithmic barrier is the extended - real - valued
function B defined by B(x) = - sum_i = 1^m log(- fᵢ(x)) for points satisfying fᵢ(x) < 0 for all i,
and
B(x) = + ∞ otherwise.
-/
structure ConvexInequalityConstrainedProblem (m : ℕ) where
  n : ℕ
  f0 : (Fin n → ℝ) → ℝ
  fi : Fin m → (Fin n → ℝ) → ℝ

def ConvexInequalityConstrainedProblem.isFeasible {m : ℕ}
    (P : ConvexInequalityConstrainedProblem m) (x : Fin P.n → ℝ) : Prop :=
  ∀ i : Fin m, P.fi i x ≤ 0

def ConvexInequalityConstrainedProblem.feasibleSet {m : ℕ}
    (P : ConvexInequalityConstrainedProblem m) : Set (Fin P.n → ℝ) :=
  {x | P.isFeasible x}

def ConvexInequalityConstrainedProblem.objective {m : ℕ}
    (P : ConvexInequalityConstrainedProblem m) : (Fin P.n → ℝ) → ℝ :=
  P.f0

/-
Its dual problem is maximize & g(λ); subject to & λ_i ≥ 0, i = 1, ..., m. array
-/

/-- On the strict feasible set with `t > 0`, the barrier objective is the expected real-valued
expression. -/
lemma centeringObjective_eq_on_strictFeasibleSet
    {α : Type*} {m : ℕ} {t : ℝ} {f0 : α → ℝ} {fi : Fin m → α → ℝ} {x : α}
    (ht : 0 < t) (hx : x ∈ strictFeasibleSet fi) :
    centeringObjective t f0 fi x =
      (((t * f0 x) - ∑ i : Fin m, Real.log (-fi i x) : ℝ) : EReal) := by
  -- Open both `if` branches using positivity of `t` and strict feasibility of `x`.
  have hfi : ∀ i : Fin m, fi i x < 0 := hx
  have hsum :
      ((∑ i : Fin m, Real.log (-fi i x) : ℝ) : EReal) =
        ∑ i : Fin m, (Real.log (-fi i x) : EReal) := by
    classical
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty =>
        simp
    | @insert a s ha hs =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, hs]
  rw [centeringObjective, dif_pos ht, dif_pos hfi, ← hsum, ← EReal.coe_mul, ← EReal.coe_sub]

/-- The scalar inequality that lower-bounds one logarithmic barrier term. -/
lemma one_add_log_le_mul_sub_log {a u : ℝ} (ha : 0 < a) (hu : 0 < u) :
    1 + Real.log a ≤ a * u - Real.log u := by
  -- Apply the standard bound to `a * u` and split the logarithm of the product.
  have hau : 0 < a * u := mul_pos ha hu
  have hlog : Real.log (a * u) ≤ a * u - 1 := Real.log_le_sub_one_of_pos hau
  have hmul : Real.log (a * u) = Real.log a + Real.log u := by
    rw [Real.log_mul (ne_of_gt ha) (ne_of_gt hu)]
  linarith

/-- Scaling the affine Lagrangian lower bound by a positive parameter gives the form needed for
the barrier estimate. -/
lemma scaled_lagrangian_lower_bound
    {m : ℕ} (P : ConvexInequalityConstrainedProblem m) {lam : Fin m → ℝ} {γ t : ℝ}
    {x : Fin P.n → ℝ}
    (hγ : γ ≤ P.f0 x + ∑ i : Fin m, lam i * P.fi i x) (ht : 0 < t) :
    t * γ + ∑ i : Fin m, (t * lam i) * (-P.fi i x) ≤ t * P.f0 x := by
  -- First scale the given affine lower bound by the positive scalar `t`.
  have ht_nonneg : 0 ≤ t := le_of_lt ht
  have hscaled : t * γ ≤ t * (P.f0 x + ∑ i : Fin m, lam i * P.fi i x) :=
    mul_le_mul_of_nonneg_left hγ ht_nonneg
  have hscaled' : t * γ ≤ t * P.f0 x + t * ∑ i : Fin m, lam i * P.fi i x := by
    nlinarith
  -- Then rewrite the constraint contribution so it can be moved to the left-hand side.
  have hsum_eq : ∑ i : Fin m, (t * lam i) * (-P.fi i x) = -(t * ∑ i : Fin m, lam i * P.fi i x) := by
    calc
      ∑ i : Fin m, (t * lam i) * (-P.fi i x)
          = ∑ i : Fin m, -(t * (lam i * P.fi i x)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
      _ = - ∑ i : Fin m, t * (lam i * P.fi i x) := by
            rw [Finset.sum_neg_distrib]
      _ = -(t * ∑ i : Fin m, lam i * P.fi i x) := by
            rw [Finset.mul_sum]
  rw [hsum_eq]
  nlinarith

/-- The real-valued lower bound for the centering objective on the strict feasible set. -/
lemma strictFeasible_real_lower_bound
    {m : ℕ} (P : ConvexInequalityConstrainedProblem m) {lam : Fin m → ℝ} {γ t : ℝ}
    (hlam_pos : ∀ i : Fin m, 0 < lam i)
    (hγ : ∀ x : Fin P.n → ℝ, γ ≤ P.f0 x + ∑ i : Fin m, lam i * P.fi i x)
    (ht : 0 < t) {x : Fin P.n → ℝ} (hx : x ∈ strictFeasibleSet P.fi) :
    t * γ + ∑ i : Fin m, (1 + Real.log (t * lam i)) ≤
      t * P.f0 x - ∑ i : Fin m, Real.log (-P.fi i x) := by
  -- Strict feasibility gives positivity for every barrier argument.
  have hxlt : ∀ i : Fin m, P.fi i x < 0 := hx
  have hterm :
      ∀ i : Fin m,
        1 + Real.log (t * lam i) ≤
          (t * lam i) * (-P.fi i x) - Real.log (-P.fi i x) := by
    intro i
    have htlami : 0 < t * lam i := mul_pos ht (hlam_pos i)
    have hneg_fi : 0 < -P.fi i x := by
      linarith [hxlt i]
    exact one_add_log_le_mul_sub_log htlami hneg_fi
  -- Sum the scalar estimates and combine them with the scaled affine lower bound.
  have hsum :
      ∑ i : Fin m, (1 + Real.log (t * lam i)) ≤
        ∑ i : Fin m, ((t * lam i) * (-P.fi i x) - Real.log (-P.fi i x)) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hterm i
  have hlag :
      t * γ + ∑ i : Fin m, (t * lam i) * (-P.fi i x) ≤ t * P.f0 x :=
    scaled_lagrangian_lower_bound (P := P) (hγ x) ht
  calc
    t * γ + ∑ i : Fin m, (1 + Real.log (t * lam i))
        ≤ t * γ + ∑ i : Fin m, ((t * lam i) * (-P.fi i x) - Real.log (-P.fi i x)) := by
            simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hsum (t * γ)
    _ = (t * γ + ∑ i : Fin m, (t * lam i) * (-P.fi i x)) -
          ∑ i : Fin m, Real.log (-P.fi i x) := by
          rw [Finset.sum_sub_distrib, add_sub_assoc]
    _ ≤ t * P.f0 x - ∑ i : Fin m, Real.log (-P.fi i x) := by
          exact sub_le_sub_right hlag _

theorem centeringObjective_bounded_below_on_strictFeasibleSet
    {m : ℕ} (P : ConvexInequalityConstrainedProblem m)
    (hf0_convex : ConvexOn ℝ Set.univ P.f0)
    (hfi_convex : ∀ i : Fin m, ConvexOn ℝ Set.univ (P.fi i))
    (hlag_bounded :
      ∃ lam : Fin m → ℝ,
        dualFeasible lam ∧
        (∀ i : Fin m, 0 < lam i) ∧
        ∃ γ : ℝ, ∀ x : Fin P.n → ℝ,
          γ ≤ P.f0 x + ∑ i : Fin m, lam i * P.fi i x) :
    ∀ t : ℝ, 0 < t →
      ∃ C : EReal, ∀ x ∈ strictFeasibleSet P.fi, C ≤ centeringObjective t P.f0 P.fi x := by
  intro t ht
  rcases hlag_bounded with ⟨lam, _hdual, hlam_pos, γ, hγ⟩
  refine ⟨((t * γ + ∑ i : Fin m, (1 + Real.log (t * lam i)) : ℝ) : EReal), ?_⟩
  intro x hx
  -- Reduce the extended-real goal to the real lower bound established above.
  rw [centeringObjective_eq_on_strictFeasibleSet (t := t) (f0 := P.f0) (fi := P.fi) ht hx]
  exact EReal.coe_le_coe <| strictFeasible_real_lower_bound (P := P) hlam_pos hγ ht hx

end «problem-45»
