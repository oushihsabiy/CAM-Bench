import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-189»

/- [BLOCK Exercise 2.15 | 17 | defn]
A sequence (xₖ) converges Q-superlinearly to x* if xₖ → x* and
lim_k→∞ frac{‖x_k+1-x*‖}{‖x_k-x*‖}=0,
whenever the denominator is nonzero for all sufficiently large k.
-/
def QSuperlinearlyConverges {E : Type*} [NormedAddCommGroup E] (x : ℕ → E) (xStar : E) : Prop :=
  Tendsto x atTop (𝓝 xStar) ∧
    ((∀ᶠ k in atTop, x k ≠ xStar) →
      Tendsto
        (fun k => ‖x (k + 1) - xStar‖ / ‖x k - xStar‖)
        atTop
        (𝓝 0))

/- [BLOCK Exercise 2.15 | 18 | defn]
A sequence (xₖ) converges Q-quadratically to x* if there exist constants M>0 and k₀∈N such
that, for all k≥ k₀,
‖x_k+1-x*‖≤ M‖x_k-x*‖^2.
-/
def QQuadraticallyConverges {E : Type*} [NormedAddCommGroup E] (x : ℕ → E) (xStar : E) : Prop :=
  Tendsto x atTop (𝓝 xStar) ∧
    ∃ (M : ℝ) (k₀ : ℕ), 0 < M ∧ ∀ k ≥ k₀, ‖x (k + 1) - xStar‖ ≤ M * ‖x k - xStar‖ ^ 2

/-
Exercise 2.15 | 19 | thm

Let (xₖ)_{k ∈ ℕ} be the sequence defined by xₖ = 1/k!, ℕ = {1, 2, 3, …}, k! = 1 · 2 · … · k. Using
the definition lim_{k → ∞} |x_{k+1}| / |xₖ| = 0 for Q-superlinear convergence to 0, show that the
sequence xₖ = 1/k! converges Q-superlinearly.
-/
theorem factorialInverse_qsuperlinearlyConverges :
    QSuperlinearlyConverges (fun k : ℕ => ((k + 1).factorial : ℝ)⁻¹) 0 := by
  sorry

/-
Exercise 2.15 | 20 | thm

Let (xₖ)_{k ∈ ℕ} be the sequence defined by xₖ = 1/(k!), ℕ = {1, 2, 3, …}, k! = 1 · 2 · … · k. Using
the definition ∃ M > 0 ∃ k₀ ∈ ℕ ∀ k ≥ k₀: |x_{k+1}| ≤ M|xₖ|² for Q-quadratic convergence to 0,
determine whether it converges Q-quadratically.
-/
theorem factorialInverse_not_qquadraticallyConverges :
    ¬ QQuadraticallyConverges (fun k : ℕ => ((k + 1).factorial : ℝ)⁻¹) 0 := by
  sorry

end «problem-189»
