import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-60»

def l2Norm {m : ℕ} (u : Fin m → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin m, (u i) ^ 2)

def l1Norm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, |x j|

def linfNorm {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  sSup (Set.range fun j : Fin n => |z j|)

/-
Given a primal problem with Lagrangian $L(x, lambda)$, the dual function is $g(lambda) = inf_x L(x,
lambda)$. The Lagrange dual problem is to maximize $g(lambda)$ over the admissible dual variables.
-/
def lagrangeDualFunction {X Lam : Type*} (L : X → Lam → ℝ) : Lam → EReal :=
  fun lam => sInf (Set.range fun x : X => (L x lam : EReal))

structure L2L1PrimalProblem where
  m : ℕ
  n : ℕ
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  γ : ℝ

def L2L1PrimalProblem.objective (p : L2L1PrimalProblem) :
    ((Fin p.n → ℝ) × (Fin p.m → ℝ)) → ℝ :=
  fun xy => l2Norm xy.2 + p.γ * l1Norm xy.1

def L2L1PrimalProblem.feasibleSet (p : L2L1PrimalProblem) :
    Set ((Fin p.n → ℝ) × (Fin p.m → ℝ)) :=
  {xy | p.A.mulVec xy.1 - p.b = xy.2}

/-
Let (A in mathbf{R}^{m \times n}), (b in mathbf{R}^m), and (gamma > 0). For (u in mathbf{R}^m),
define (|u |_2 = (\sum_{i = 1}^m u_i^2)^{1/2}); for (x in mathbf{R}^n), define (|x |_1 = \sum_{j =
1}^n |x_j|); and for (z in mathbf{R}^n), define (|z |_ infty = max_{1 le j le n} |z_j|).
Consider the primal ll2 - ll1 problem. Prove that its Lagrange dual problem is [ begin{array}{ll}
mbox{maximize} & - b^T nu mbox{subject to} & | nu |_2 le 1, & |A^T nu |_ infty le gamma, end{array}
] with dual variable (nu in mathbf{R}^m).
-/
theorem l2l1_primalProblem_has_lagrangeDual
    (p : L2L1PrimalProblem) (hγ : 0 < p.γ) :
    -- The dual objective is g(ν) = - bᵀν for all admissible ν
    ∀ ν : Fin p.m → ℝ,
      l2Norm ν ≤ 1 →
      linfNorm (Matrix.mulVec p.Aᵀ ν) ≤ p.γ →
      lagrangeDualFunction
        (fun xy : (Fin p.n → ℝ) × (Fin p.m → ℝ) => fun ν : Fin p.m → ℝ =>
          l2Norm xy.2 + p.γ * l1Norm xy.1 +
            ∑ i : Fin p.m, ν i * ((p.A.mulVec xy.1 - p.b - xy.2) i))
        ν =
      (-∑ i : Fin p.m, p.b i * ν i : ℝ) := by
  sorry

end «problem-60»
