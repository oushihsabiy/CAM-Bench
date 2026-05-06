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
  sorry

end «problem-167»
