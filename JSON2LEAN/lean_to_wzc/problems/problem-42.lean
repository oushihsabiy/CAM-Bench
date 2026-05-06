import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-42»
/-
Let C be a convex set. A function f: C → ℝ U {+ infinity} is quasiconvex if for all x, y in C and
all
θ in [0, 1], f(θ x + (1 - θ) y) < = max{f(x), f(y)}.
-/
def QuasiconvexOn {E : Type*} [AddCommMonoid E] [Module ℝ E] (C : Set E)
    (hC : Convex ℝ C) (f : C → WithTop ℝ) : Prop :=
  ∀ (x y : C) (θ : ℝ), ∀ hθ : θ ∈ Set.Icc (0 : ℝ) 1,
    f ⟨θ • (x : E) + (1 - θ) • (y : E), by
      exact hC x.property y.property hθ.1 (sub_nonneg.mpr hθ.2) (by ring)
    ⟩ ≤
      max (f x) (f y)

/-
Let c ∈ ℝ^n, d ∈ ℝ, A ∈ ℝ^(p x n), and b ∈ ℝ^p. Let f₀, f₁, ..., fₘ: ℝ^n → ℝ U {+ infinity} be
convex
functions, and let dom f₀ = {x ∈ ℝ^n | f₀(x) < + infinity}. Define S = {x ∈ ℝ^n | fᵢ(x) < = 0 for
all
i = 1, ..., m, Ax = b, x in dom f₀, cᵀ x + d > 0}. Show that S is convex.
-/
theorem convex_feasibleSet_of_quasiconvex_constraints
    {n p m : ℕ}
    (A : Matrix (Fin p) (Fin n) ℝ)
    (b : Fin p → ℝ)
    (c : Fin n → ℝ)
    (d : ℝ)
    (f0 : (Fin n → ℝ) → WithTop ℝ)
    (f : Fin m → (Fin n → ℝ) → WithTop ℝ)
    (hf0 : Convex ℝ {xt : (Fin n → ℝ) × ℝ | f0 xt.1 ≤ (xt.2 : WithTop ℝ)})
    (hf : ∀ i : Fin m,
      Convex ℝ {xt : (Fin n → ℝ) × ℝ | f i xt.1 ≤ (xt.2 : WithTop ℝ)}) :
    Convex ℝ
      {x : Fin n → ℝ |
        (∀ i : Fin m, f i x ≤ (0 : WithTop ℝ)) ∧
        Matrix.mulVec A x = b ∧
        f0 x < ⊤ ∧
        (∑ j : Fin n, c j * x j) + d > 0} := by
  sorry

/-
Let c ∈ ℝ^n and d ∈ ℝ. Let f₀, f₁, ..., fₘ: ℝ^n → ℝ U {+ infinity} be convex functions, and let dom
f₀
= {x ∈ ℝ^n | f₀(x) < + infinity}. Show that the function x - > f₀(x) / (cᵀ x + d) is quasiconvex on
the domain {x in dom f₀ | cᵀ x + d > 0}.
-/
theorem quasiconvexOn_perspective_of_convex
    {n : ℕ}
    (c : Fin n → ℝ)
    (d : ℝ)
    (f0 : (Fin n → ℝ) → WithTop ℝ)
    (hf0 : Convex ℝ {xt : (Fin n → ℝ) × ℝ | f0 xt.1 ≤ (xt.2 : WithTop ℝ)})
    (hC :
      Convex ℝ
        {x : Fin n → ℝ | f0 x < ⊤ ∧ 0 < (∑ j : Fin n, c j * x j) + d}) :
    QuasiconvexOn
      {x : Fin n → ℝ | f0 x < ⊤ ∧ 0 < (∑ j : Fin n, c j * x j) + d}
      hC
      (fun x => ((f0 x.1).getD 0 / ((∑ j : Fin n, c j * x.1 j) + d) : ℝ)) := by
  sorry

/-
Let D = {p ∈ ℝ_ + ^m | a_iᵀ p > 0 for i = 1, ..., n}. Define f(p) = max_{i = 1, ..., n} |log(a_iᵀ p)
-
log(I_des)| for p in D, where aᵢ ∈ ℝ^m for i = 1, ..., n and I_des > 0. Show that the function p - >
exp(f(p)) is convex on D.
-/
open scoped RealInnerProductSpace

theorem exp_max_log_deviation_convexOn
    {m n : ℕ} [NeZero n]
    (a : Fin n → EuclideanSpace ℝ (Fin m)) {I_des : ℝ} (hI_des : 0 < I_des) :
    ConvexOn ℝ
      {p : EuclideanSpace ℝ (Fin m) |
        (∀ j : Fin m, 0 ≤ p j) ∧ ∀ i : Fin n, 0 < ⟪a i, p⟫}
      (fun p =>
        Real.exp
          (Finset.univ.sup' Finset.univ_nonempty
            (fun i : Fin n => |Real.log ⟪a i, p⟫ - Real.log I_des|))) := by
  sorry
end «problem-42»