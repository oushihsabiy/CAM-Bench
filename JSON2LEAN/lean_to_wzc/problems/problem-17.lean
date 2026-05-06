import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-17»
/-
For a twice differentiable function f: ℝ^n → ℝ, the Hessian at x is the matrix ∇^2 f(x) ∈ S^n with
entries (∇^2 f(x))_ij = ∂^2 f / (∂ xᵢ ∂ xⱼ)(x).
-/
def Hessian {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (_hC2 : ContDiffAt ℝ 2 f x) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) x)
      (Pi.single i (1 : ℝ))


/-
Let f: ℝ^n → ℝ be twice differentiable at x ∈ dom f. Let ∇ f(x) be the ∇of f at x, ∇^2 f(x) the
Hessian at x, and S^n the set of n × n real symmetric matrices. For M ∈ S^n, write M succeq 0 when M
is positive semidefinite, and let λ_n(M) denote the smallest eigenvalue of M. Define H(x) = [ ∇^2
f(x) & ∇ f(x); ∇ f(x)ᵀ & 0 ]. Prove that the condition ∀ y ∈ ℝ^n, yᵀ ∇ f(x) = 0 implies yᵀ ∇^2 f(x)y
≥ 0 holds if and only if either ∇ f(x) = 0 and ∇^2 f(x)succeq 0, or ∇ f(x)! = 0 and H(x) has exactly
one negative eigenvalue.
-/
theorem hessian_tangent_nonneg_iff_gradient_zero_psd_or_one_negative_eigenvalue
    {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hC2 : ContDiffAt ℝ 2 f x)
    (hHess_symm : (Hessian f x hC2).IsSymm) :
    (∀ y : Fin n → ℝ,
      (∑ i, y i * deriv (fun t : ℝ => f (Function.update x i t)) (x i) = 0) →
        0 ≤ ∑ i, ∑ j, y i * (Hessian f x hC2) i j * y j) ↔
      ((∀ i, deriv (fun t : ℝ => f (Function.update x i t)) (x i) = 0) ∧
        Matrix.PosSemidef (Hessian f x hC2)) ∨
      ((¬ ∀ i, deriv (fun t : ℝ => f (Function.update x i t)) (x i) = 0) ∧
        let H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
          fun i j =>
            if hi : i.1 < n then
              if hj : j.1 < n then
                (Hessian f x hC2) ⟨i.1, hi⟩ ⟨j.1, hj⟩
              else
                deriv (fun t : ℝ => f (Function.update x ⟨i.1, hi⟩ t)) (x ⟨i.1, hi⟩)
            else if hj : j.1 < n then
              deriv (fun t : ℝ => f (Function.update x ⟨j.1, hj⟩ t)) (x ⟨j.1, hj⟩)
            else
              0
        ∃ hHsymm : H.IsSymm,
          let hHherm : H.IsHermitian := by
            simpa using hHsymm
          ∃ k : Fin (n + 1), hHherm.eigenvalues k < 0 ∧
            ∀ j : Fin (n + 1), j ≠ k → 0 ≤ hHherm.eigenvalues j) := by
  sorry

/-
Let f: ℝ^n → ℝ be twice differentiable at x ∈ dom f. Let ∇ f(x) be the ∇of f at x, ∇^2 f(x) the
Hessian at x, and S^n the set of n × n real symmetric matrices. For M ∈ S^n, write M succeq 0 when M
is positive semidefinite, and let λ_n(M) denote the smallest eigenvalue of M. Define H(x) = [ ∇^2
f(x) & ∇ f(x); ∇ f(x)ᵀ & 0 ]. Prove that the condition ∀ y ∈ ℝ^n, y ≠ 0 and yᵀ ∇ f(x) = 0 implies yᵀ
∇^2 f(x)y > 0 holds if and only if H(x) has exactly one nonpositive eigenvalue.
-/
theorem hessian_strict_tangent_pos_iff_H_has_exactly_one_nonpositive_eigenvalue
    {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hC2 : ContDiffAt ℝ 2 f x)
    (hHess_symm : (Hessian f x hC2).IsSymm) :
    (∀ y : Fin n → ℝ,
      y ≠ 0 →
      (∑ i, y i * deriv (fun t : ℝ => f (Function.update x i t)) (x i) = 0) →
      0 < ∑ i, ∑ j, y i * (Hessian f x hC2) i j * y j) ↔
    let H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      fun i j =>
        if hi : i.1 < n then
          if hj : j.1 < n then
            (Hessian f x hC2) ⟨i.1, hi⟩ ⟨j.1, hj⟩
          else
            deriv (fun t : ℝ => f (Function.update x ⟨i.1, hi⟩ t)) (x ⟨i.1, hi⟩)
        else if hj : j.1 < n then
          deriv (fun t : ℝ => f (Function.update x ⟨j.1, hj⟩ t)) (x ⟨j.1, hj⟩)
        else
          0
    ∃ hHsymm : H.IsSymm,
      let hHherm : H.IsHermitian := by
        simpa using hHsymm
      ∃ k : Fin (n + 1),
        hHherm.eigenvalues k ≤ 0 ∧
        ∀ j : Fin (n + 1), j ≠ k → 0 < hHherm.eigenvalues j := by
  sorry

/-
If B ∈ S^n and a ∈ ℝ^n, then λ_n([ B & a; aᵀ & 0 ]) ≤ λ_n(B).
-/
theorem smallest_eigenvalue_block_arrow_le_smallest_eigenvalue
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hn : 0 < n)
    (hB : Matrix.IsSymm B) :
    let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      fun i j =>
        if h1 : i.1 < n then
          if h2 : j.1 < n then
            B ⟨i.1, h1⟩ ⟨j.1, h2⟩
          else
            a ⟨i.1, h1⟩
        else
          if h2 : j.1 < n then
            a ⟨j.1, h2⟩
          else
            0
    ∃ hA : A.IsSymm,
      let hAHerm : A.IsHermitian := by
        simpa using hA
      let hBHerm : B.IsHermitian := by
        simpa using hB
      hAHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.last n)) ≤
        hBHerm.eigenvalues₀
          (Fin.cast (by simp) ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩) := by
  sorry

end «problem-17»
