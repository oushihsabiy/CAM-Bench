import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-110»
/-
Let A₀, …, Aₙ be real symmetric m×m matrices and define M(x) = A₀ + x₁A₁ + ··· + x_nA_n. On the
domain {x:
M(x) ≻ 0}, define f(x) = −(det M(x))^(1/m). Prove that f is convex on this domain.
-/
open scoped BigOperators Matrix

theorem neg_det_root_convexOn_posDef_domain
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin (n + 1) → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ i, (A i)ᵀ = A i) :
    ConvexOn ℝ
      {x : Fin n → ℝ | Matrix.PosDef (A 0 + ∑ i : Fin n, (x i) • A i.succ)}
      (fun x => -Real.rpow (Matrix.det (A 0 + ∑ i : Fin n, (x i) • A i.succ)) (1 / (m : ℝ))) := by
  sorry

end «problem-110»