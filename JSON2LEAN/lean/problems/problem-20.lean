import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-20»
/-
For a differentiable optimization problem with equality constraints (h(x) = 0), the first - order
optimality conditions are that there exists a multiplier (lambda) such that (nabla f(x^
star) + Dh(x^ star)^T lambda = 0) and (h(x^ star) = 0).
-/
structure EquivalentGeometricConvexProgram where
  n : ℕ
  A : Fin n → Fin n → ℝ
  c : Fin n → ℝ
  d : Fin n → ℝ

def EquivalentGeometricConvexProgram.geometricObjective
    (P : EquivalentGeometricConvexProgram) :
    (Fin P.n → ℝ) → (Fin P.n → ℝ) → ℝ :=
  fun x y => ∑ i : Fin P.n, ∑ j : Fin P.n, x i * P.A i j * y j

def EquivalentGeometricConvexProgram.phi
    (P : EquivalentGeometricConvexProgram) :
    (Fin P.n → ℝ) → (Fin P.n → ℝ) → ℝ :=
  fun u v =>
    Real.log (∑ i : Fin P.n, ∑ j : Fin P.n, Real.exp (u i) * P.A i j * Real.exp (v j))

def EquivalentGeometricConvexProgram.xOfU
    (P : EquivalentGeometricConvexProgram) :
    (Fin P.n → ℝ) → (Fin P.n → ℝ) :=
  fun u i => Real.exp (u i)

def EquivalentGeometricConvexProgram.yOfV
    (P : EquivalentGeometricConvexProgram) :
    (Fin P.n → ℝ) → (Fin P.n → ℝ) :=
  fun v j => Real.exp (v j)

def EquivalentGeometricConvexProgram.geometricFeasible
    (P : EquivalentGeometricConvexProgram) :
    ((Fin P.n → ℝ) × (Fin P.n → ℝ)) → Prop :=
  fun xv =>
    (∀ i : Fin P.n, 0 < xv.1 i) ∧
      (∀ j : Fin P.n, 0 < xv.2 j) ∧
      (∏ i : Fin P.n, Real.rpow (xv.1 i) (P.c i) = 1) ∧
      (∏ j : Fin P.n, Real.rpow (xv.2 j) (P.d j) = 1)

def EquivalentGeometricConvexProgram.convexFeasible
    (P : EquivalentGeometricConvexProgram) :
    ((Fin P.n → ℝ) × (Fin P.n → ℝ)) → Prop :=
  fun uv =>
    (∑ i : Fin P.n, P.c i * uv.1 i = 0) ∧
      (∑ j : Fin P.n, P.d j * uv.2 j = 0)

def EquivalentGeometricConvexProgram.rowWeight
    (P : EquivalentGeometricConvexProgram) (u v : Fin P.n → ℝ) (i : Fin P.n) : ℝ :=
  let x := P.xOfU u
  let y := P.yOfV v
  x i * (∑ j : Fin P.n, P.A i j * y j) / P.geometricObjective x y

def EquivalentGeometricConvexProgram.colWeight
    (P : EquivalentGeometricConvexProgram) (u v : Fin P.n → ℝ) (j : Fin P.n) : ℝ :=
  let x := P.xOfU u
  let y := P.yOfV v
  y j * (∑ i : Fin P.n, P.A i j * x i) / P.geometricObjective x y

def EquivalentGeometricConvexProgram.scaledMatrix
    (P : EquivalentGeometricConvexProgram) (u v : Fin P.n → ℝ) :
    Fin P.n → Fin P.n → ℝ :=
  let x := P.xOfU u
  let y := P.yOfV v
  fun i j => x i * P.A i j * y j / P.geometricObjective x y

/-
Let (A in mathbf{R}^{n \times n}) have strictly positive entries, and let (c, d in mathbf{R}^n) be
strictly positive vectors such that (mathbf{1}^T c = 1) and (mathbf{1}^T d = 1), where (
mathbf{1} in mathbf{R}^n) is the all - ones vector. For (z in mathbf{R}^n), let (
operatorname{diag}(z)) denote the diagonal matrix with diagonal entries (z_1, ..., z_n). For (u, v
in mathbf{R}^n), define [ phi(u, v) = log !(\sum_{i = 1}^n\sum_{j = 1}^n A_{ij} e^{u_i + v_j}). ]
Consider the convexified problem of minimizing phi subject to
\sum_i c_i u_i = 0 and \sum_j d_j v_j = 0. If ((u, v)) is optimal and
x_i = e^{u_i}, y_j = e^{v_j}, then the first-order optimality conditions imply
[
  \frac{x_i (Ay)_i}{x^T A y} = c_i,\qquad
  \frac{y_j (A^T x)_j}{x^T A y} = d_j.
]
Equivalently, for B = diag(x) A diag(y) / (x^T A y), one has
B 1 = c and B^T 1 = d.
-/
theorem optimality_conditions_for_equivalent_geometric_convex_program
    (P : EquivalentGeometricConvexProgram)
    (hn : 0 < P.n)
    (hApos : ∀ i j : Fin P.n, 0 < P.A i j)
    (hcpos : ∀ i : Fin P.n, 0 < P.c i)
    (hdpos : ∀ j : Fin P.n, 0 < P.d j)
    (hcsum : ∑ i : Fin P.n, P.c i = 1)
    (hdsum : ∑ j : Fin P.n, P.d j = 1)
    (u v : Fin P.n → ℝ)
    (hopt :
      IsMinOn
        (fun uv : (Fin P.n → ℝ) × (Fin P.n → ℝ) => P.phi uv.1 uv.2)
        {uv | P.convexFeasible uv}
        (u, v)) :
    (∀ i : Fin P.n, P.rowWeight u v i = P.c i) ∧
    (∀ j : Fin P.n, P.colWeight u v j = P.d j) ∧
    (∀ i : Fin P.n, ∑ j : Fin P.n, P.scaledMatrix u v i j = P.c i) ∧
    (∀ j : Fin P.n, ∑ i : Fin P.n, P.scaledMatrix u v i j = P.d j) := by
  sorry

end «problem-20»
