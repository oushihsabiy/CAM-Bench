import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-94»

/-
A mapping f: S_{+ +}^n → S^n is matrix convex if for all X, Y ∈ S_{+ +}^n and all θ ∈ [0, 1], f(θ X
+
(1 - θ)Y) ≤ θ f(X) + (1 - θ)f(Y), where A ≤ B means that B - A is positive semidefinite.
-/
def MatrixConvex
    (f : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ ⦃X : Matrix (Fin n) (Fin n) ℝ⦄, X.IsSymm → X.PosDef → (f X).IsSymm) ∧
  ∀ ⦃X Y : Matrix (Fin n) (Fin n) ℝ⦄,
    X.IsSymm → X.PosDef → Y.IsSymm → Y.PosDef →
    ∀ ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 →
      (θ • X + (1 - θ) • Y).IsSymm ∧
      (θ • X + (1 - θ) • Y).PosDef ∧
      (θ • f X + (1 - θ) • f Y - f (θ • X + (1 - θ) • Y)).PosSemidef

/-
Let S^n be the space of real symmetric n × n matrices, and let S_{+ +}^n = {X ∈ S^n: X is positive
definite}. For X ∈ S_{+ +}^n, define f(X) = X^{- 1}. A mapping f: S_{+ +}^n → S^n is matrix convex
if
for all X, Y ∈ S_{+ +}^n and all θ ∈ [0, 1], f(θ X + (1 - θ)Y) ≤ θ f(X) + (1 - θ)f(Y), where A ≤ B
means
that B - A is positive semidefinite. Show that the mapping f: S_{+ +}^n → S^n defined by f(X) = X^{-
1}
is matrix convex on S_{+ +}^n. The statement includes the boundary cases θ = 0 and θ = 1 and the
zero-dimensional case; it also explicitly records that the positive-definite cone is closed under
the convex combination used in the Jensen inequality, so the inverse is only evaluated on its
intended positive-definite domain.
-/
theorem inverse_matrixConvex {n : ℕ} :
    MatrixConvex (fun X : Matrix (Fin n) (Fin n) ℝ => X⁻¹) := by
  sorry



end «problem-94»
