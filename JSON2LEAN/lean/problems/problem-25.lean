import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-25»
/-
A function f: ℝ^n → ℝ is called convex and twice continuously differentiable if it is convex and
belongs to C^2(ℝ^n), that is, all second - order partial derivatives of f exist and are continuous
on
ℝ^n.
-/
def IsConvexC2Function {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → ℝ) : Prop :=
  ConvexOn ℝ (Set.univ : Set E) f ∧ ContDiff ℝ 2 f

/-
The convex conjugate of a function f: ℝ^n → ℝ cup {+ ∞} is the function f*: ℝ^n → ℝ cup {+ ∞}
defined
by f*(y) = sup_{z ∈ ℝ^n} (yᵀ z - f(z)).
-/
def convexConjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → EReal) : E → EReal :=
  fun y => sSup (Set.range fun z : E => (⟪y, z⟫ : ℝ) - f z)

/-
A function g: ℝ^n → ℝ is differentiable at y ∈ ℝ^n if there exists a vector a ∈ ℝ^n such that lim_{h
→ 0} (g(y + h) - g(y) - aᵀ h)/(‖h‖) = 0; in this case, a is denoted by ∇ g(y).
-/
def IsDifferentiableAtWithGradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → ℝ) (y a : E) : Prop :=
  HasFDerivAt g ((InnerProductSpace.toDual ℝ E) a) y

/-
Let f: ℝ^n → ℝ be a convex twice continuously differentiable function. Let x ∈ ℝ^n, set y = ∇ f(x),
and assume that the Hessian ∇^2 f(x) is positive definite. Define the convex conjugate f*: ℝ^n → ℝ +
∞
by f*(y) = sup_{z∈ℝ^n}(yᵀ z - f(z)). Show that there is an open neighborhood of y on which f* is
represented by a real-valued function that is differentiable at y with gradient x.
-/
theorem gradient_convexConjugate_at_gradient_eq_point
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → ℝ)
    (x : E)
    (hf : IsConvexC2Function f)
    (hpd : ∀ v : E, v ≠ 0 →
      0 < (fderiv ℝ (fun z : E => fderiv ℝ f z v) x) v)
    (y : E)
    (hy : y = (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)) :
    ∃ s : Set E, IsOpen s ∧ y ∈ s ∧
      ∃ g : E → ℝ,
        (∀ y' : E, y' ∈ s → convexConjugate (fun z : E => (f z : EReal)) y' = (g y' : EReal)) ∧
        IsDifferentiableAtWithGradient g y x := by
  sorry


end «problem-25»
