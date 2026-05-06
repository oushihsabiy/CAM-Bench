import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-24»

def l2Norm {m : ℕ} (z : Fin m → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin m, z i ^ 2)

def linfNorm {m : ℕ} (z : Fin m → ℝ) : ℝ :=
  sSup (Set.range fun i : Fin m => |z i|)

/-
Given A∈ℝ^m× n and b∈ℝ^m, a (linear) least - squares solution is any minimizer
x_ls∈argmin_x∈ℝ^n‖Ax - b‖_2.
-/
def IsLeastSquaresSolution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x_ls : Fin n → ℝ) : Prop :=
  IsMinOn (fun x : Fin n → ℝ => l2Norm (A.mulVec x - b)) Set.univ x_ls

/-
For a function f on a set X, argmin_x∈X f(x) denotes the set of minimizers {x∈X: f(x) ≤ f(y) ∀ y∈X}
(and when used as a point, it denotes a chosen element of this set).
-/
def argmin {α β : Type*} [Preorder β] (f : α → β) (s : Set α) : Set α :=
  {x | x ∈ s ∧ ∀ y ∈ s, f x ≤ f y}

/-
For all z∈ℝ^m, 1{m}‖z‖_2 ≤ ‖z‖_∞ ≤ ‖z‖_2.
-/
def norm_equivalence_l2_linf (m : ℕ) : Prop :=
  0 < m ∧
  ∀ z : Fin m → ℝ,
    (1 / Real.sqrt (m : ℝ)) * l2Norm z ≤ linfNorm z ∧
    linfNorm z ≤ l2Norm z

/-
Let A ∈ ℝ^m × n and b ∈ ℝ^m with rank(A) = n. Consider the problem min_x ∈ ℝ^n ‖Ax - b‖_∞. For z =
(z₁, ..., zₘ) ∈ ℝ^m, ‖z‖_∞ = max₁ ≤ i ≤ m|zᵢ| and ‖z‖_2 = (sum_i = 1^m zᵢ^2)^1/2.
-/
structure ChebyshevRegressionProblem where
  m : ℕ
  n : ℕ
  m_pos : 0 < m
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  rank_eq : Module.finrank ℝ (LinearMap.range A.toLin') = n

def ChebyshevRegressionProblem.objective (p : ChebyshevRegressionProblem) : (Fin p.n → ℝ) → ℝ :=
  fun x => linfNorm (p.A.mulVec x - p.b)

def ChebyshevRegressionProblem.feasibleSet (p : ChebyshevRegressionProblem) : Set (Fin p.n → ℝ) :=
  Set.univ

def ChebyshevRegressionProblem.minimizers (p : ChebyshevRegressionProblem) : Set (Fin p.n → ℝ) :=
  argmin p.objective p.feasibleSet

def ChebyshevRegressionProblem.residual (p : ChebyshevRegressionProblem) (x : Fin p.n → ℝ) :
    Fin p.m → ℝ :=
  p.A.mulVec x - p.b

theorem leastSquares_residual_linf_le_sqrt_m_mul_chebyshev_optimal
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hrank : Module.finrank ℝ (LinearMap.range A.toLin') = n)
    (x_ch x_ls : Fin n → ℝ)
    (hxch : IsMinOn (fun y : Fin n → ℝ => linfNorm (A.mulVec y - b)) Set.univ x_ch)
    (hxls : IsLeastSquaresSolution A b x_ls)
    (hnorm : norm_equivalence_l2_linf m) :
    linfNorm (A.mulVec x_ls - b) ≤
      Real.sqrt (m : ℝ) *
        linfNorm (A.mulVec x_ch - b) := by
  -- Compare the least-squares residual to the residual at the Chebyshev candidate in `l2`.
  have hls_l2 :
      l2Norm (A.mulVec x_ls - b) ≤ l2Norm (A.mulVec x_ch - b) := by
    unfold IsLeastSquaresSolution at hxls
    rw [isMinOn_univ_iff] at hxls
    exact hxls x_ch
  -- The norm-equivalence hypothesis gives the upper comparison `linf ≤ l2` on the least-squares residual.
  have hls_linf_le_l2 :
      linfNorm (A.mulVec x_ls - b) ≤ l2Norm (A.mulVec x_ls - b) :=
    (hnorm.2 (A.mulVec x_ls - b)).2
  -- Positivity of `sqrt m` is needed to rescale the lower norm-equivalence bound.
  have hsqrt_pos : 0 < Real.sqrt (m : ℝ) := by
    exact Real.sqrt_pos.2 (Nat.cast_pos.2 hnorm.1)
  -- Rewrite the lower bound `(1 / sqrt m) * ‖z‖₂ ≤ ‖z‖∞` into `‖z‖₂ ≤ sqrt m * ‖z‖∞`.
  have hch_l2_le :
      l2Norm (A.mulVec x_ch - b) ≤ Real.sqrt (m : ℝ) * linfNorm (A.mulVec x_ch - b) := by
    have hch_scaled :
        (1 / Real.sqrt (m : ℝ)) * l2Norm (A.mulVec x_ch - b) ≤
          linfNorm (A.mulVec x_ch - b) :=
      (hnorm.2 (A.mulVec x_ch - b)).1
    rw [one_div] at hch_scaled
    exact (inv_mul_le_iff₀ hsqrt_pos).1 hch_scaled
  -- Chain the three comparisons to bound the least-squares residual in `linf`.
  exact hls_linf_le_l2.trans (hls_l2.trans hch_l2_le)

end «problem-24»
