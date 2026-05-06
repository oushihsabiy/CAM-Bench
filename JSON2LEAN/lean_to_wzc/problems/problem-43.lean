import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-43»
/-
A cone K ⊆ ℝ^m is a proper convex cone if it is convex, closed, has nonempty interior, and is
pointed, i. e. K cap (- K) = {0}.
-/
def IsProperConvexCone (K : Set (Fin m → ℝ)) : Prop :=
  (∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x : Fin m → ℝ⦄, x ∈ K → a • x ∈ K) ∧
  Convex ℝ K ∧
  IsClosed K ∧
  Set.Nonempty (interior K) ∧
  K ∩ {x | -x ∈ K} = {0}

/-
Given a cone K ⊆ ℝ^m, the generalized inequality induced by K is the relation y preceq_K z defined
by z - y ∈ K.
-/
def GeneralizedInequality (K : Set (Fin m → ℝ)) (y z : Fin m → ℝ) : Prop :=
  z - y ∈ K

/-
For a map f: ℝ^n → ℝ^m, its K - epigraph is epi_K f = {(x, t) ∈ ℝ^n × ℝ^m | f(x) preceq_K t}.
-/
def KEpigraph (K : Set (Fin m → ℝ)) (f : (Fin n → ℝ) → Fin m → ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ)) :=
  {p | GeneralizedInequality K (f p.1) p.2}

/-
A function f: ℝ^n → ℝ^m is K - convex if for all x, y ∈ ℝ^n and all θ ∈ [0, 1], f(θ x + (1 - θ)y)
preceq_K θ f(x) + (1 - θ)f(y).
-/
def IsKConvex (K : Set (Fin m → ℝ)) (f : (Fin n → ℝ) → Fin m → ℝ) : Prop :=
  ∀ ⦃x y : Fin n → ℝ⦄, ∀ ⦃θ : ℝ⦄,
    0 ≤ θ → θ ≤ 1 →
      GeneralizedInequality K
        (f (θ • x + (1 - θ) • y))
        (θ • f x + (1 - θ) • f y)

/-
Let K ⊆ ℝ^m be a proper convex cone, and define the generalized inequality preceq_K on ℝ^m by y
preceq_K z if z - y ∈ K. Let f: ℝ^n → ℝ^m, and define its K - epigraph by epi_K f = {(x, t)∈ ℝ^n×
ℝ^m |
f(x)preceq_K t}. A function f is called K - convex if for all x, y∈ ℝ^n and all θ∈[0, 1], f(θ
x + (1 - θ)y)preceq_K θ f(x) + (1 - θ)f(y). Show that f is K - convex if and only if epi_K f is a
convex set.
-/
theorem isKConvex_iff_convex_KEpigraph
    {K : Set (Fin m → ℝ)} {f : (Fin n → ℝ) → Fin m → ℝ}
    (hK : IsProperConvexCone K) :
    IsKConvex K f ↔ Convex ℝ (KEpigraph K f) := by
  sorry
end «problem-43»