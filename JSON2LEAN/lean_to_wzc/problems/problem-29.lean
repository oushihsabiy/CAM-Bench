import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-29»
/-
For a directed graph with node - arc incidence matrix B ∈ ℝ^m × b, a reduced incidence matrix is any
matrix obtained by deleting one row of B.
-/
structure CircuitCurrentConvexProgram (b m : ℕ) where
  A : Matrix (Fin m) (Fin b) ℝ
  ψ : (Fin b → ℝ) → ℝ

def CircuitCurrentConvexProgram.IsFeasible {b m : ℕ} (P : CircuitCurrentConvexProgram b m)
    (i : Fin b → ℝ) : Prop :=
  P.A.mulVec i = 0

def CircuitCurrentConvexProgram.ObjectiveValue {b m : ℕ} (P : CircuitCurrentConvexProgram b m)
    (i : Fin b → ℝ) : ℝ :=
  P.ψ i

def CircuitCurrentConvexProgram.IsOptimal {b m : ℕ} (P : CircuitCurrentConvexProgram b m)
    (i : Fin b → ℝ) : Prop :=
  P.IsFeasible i ∧ ∀ j : Fin b → ℝ, P.IsFeasible j → P.ObjectiveValue i ≤ P.ObjectiveValue j

/-
Let b, n ∈ ℕ. Let A ∈ ℝ^{n× b} be the reduced incidence matrix of the circuit, and for each j =
1, ..., b, let φ_j: ℝ→ℝ be continuous and nondecreasing. Define psi: ℝ^b→ℝ by psi(i₁, ..., i_b) =
\sum_{j = 1}^b int₀^{iⱼ} φ_j(u)du. Prove that psi is convex, and that if i^star∈ℝ^b solves the
convex
optimization problem circuit current convex program, then, assuming the standard optimality
conditions hold, there exists e^star∈ℝ^n such that Aᵀ e^star = big(φ_1(i₁^star), ...,
φ_b(i_b^star)big). Therefore, with v^star = Aᵀ e^star, the triple (v^star, i^star, e^star) satisfies
all circuit equations Ai^star = 0, v^star = Aᵀ e^star, vⱼ^star = φ_j(iⱼ^star), j = 1, ..., b.
-/
theorem exists_potential_for_optimal_circuit_current
    {b a : ℕ} (P : CircuitCurrentConvexProgram b a)
    (phi : Fin b → ℝ → ℝ)
    (hpsi :
      ∀ i : Fin b → ℝ,
        P.ψ i = ∑ j : Fin b, ∫ u in (0)..(i j), phi j u)
    (hphi_mono : ∀ j : Fin b, Monotone (phi j))
    (hphi_cont : ∀ j : Fin b, Continuous (phi j))
    (istar : Fin b → ℝ)
    (hiopt : P.IsOptimal istar)
    (hKKT :
      ∃ estar : Fin a → ℝ,
        (fun j : Fin b => ∑ k : Fin a, P.A k j * estar k)
          = (fun j : Fin b => phi j (istar j))) :
    ConvexOn ℝ Set.univ P.ψ ∧
      ∃ estar : Fin a → ℝ,
        (fun j : Fin b => ∑ k : Fin a, P.A k j * estar k) = (fun j : Fin b => phi j (istar j)) ∧
        let vstar : Fin b → ℝ := fun j : Fin b => ∑ k : Fin a, P.A k j * estar k
        P.A.mulVec istar = 0 ∧
        vstar = (fun j : Fin b => ∑ k : Fin a, P.A k j * estar k) ∧
        ∀ j : Fin b, vstar j = phi j (istar j) := by
  sorry

end «problem-29»