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
  let primitive : Fin b → ℝ → ℝ := fun j x => ∫ u in (0)..x, phi j u
  have hprimitive_convex : ∀ j : Fin b, ConvexOn ℝ Set.univ (primitive j) := by
    intro j
    have hprimitive_deriv : deriv (primitive j) = phi j := by
      -- The fundamental theorem of calculus identifies the derivative of the integral primitive.
      funext x
      simpa [primitive] using (Continuous.deriv_integral (phi j) (hphi_cont j) 0 x)
    -- Convexity follows because the primitive is differentiable and its derivative is monotone.
    refine Monotone.convexOn_univ_of_deriv ?_ ?_
    · simpa [primitive] using
        (intervalIntegral.differentiable_integral_of_continuous (a := (0 : ℝ)) (hphi_cont j))
    · simpa [hprimitive_deriv] using hphi_mono j
  have hcoordinate_convex :
      ∀ j : Fin b, ConvexOn ℝ Set.univ (fun i : Fin b → ℝ => primitive j (i j)) := by
    intro j
    -- Compose the scalar convex primitive with the coordinate projection onto edge `j`.
    simpa [primitive, LinearMap.proj_apply] using
      (hprimitive_convex j).comp_linearMap
        (LinearMap.proj (R := ℝ) (φ := fun _ : Fin b => ℝ) j)
  let objectiveSum : Finset (Fin b) → (Fin b → ℝ) → ℝ :=
    fun s i => s.sum fun j => primitive j (i j)
  have hsum_convex :
      ∀ s : Finset (Fin b), ConvexOn ℝ Set.univ (objectiveSum s) := by
    classical
    intro s
    -- Sum the coordinatewise convex contributions over the chosen set of branches.
    refine Finset.induction_on s ?_ ?_
    · -- The empty sum is the constant zero function, hence convex.
      refine ⟨convex_univ, ?_⟩
      intro x hx y hy a b ha hb hab
      simp [objectiveSum]
    · intro j s hj hs
      -- Adding one more convex summand preserves convexity.
      simpa [objectiveSum, Finset.sum_insert hj] using (hcoordinate_convex j).add hs
  have hconvex_psi : ConvexOn ℝ Set.univ P.ψ := by
    -- Rewrite the explicit integral formula back into the program objective.
    refine (hsum_convex Finset.univ).congr ?_
    intro i hi
    simpa [objectiveSum, primitive] using (hpsi i).symm
  constructor
  · exact hconvex_psi
  · rcases hKKT with ⟨estar, hestar⟩
    refine ⟨estar, hestar, ?_⟩
    dsimp
    -- Feasibility comes from optimality, and the circuit equations follow by unfolding `vstar`.
    refine ⟨by simpa [CircuitCurrentConvexProgram.IsFeasible] using hiopt.1, rfl, ?_⟩
    intro j
    exact congrFun hestar j

end «problem-29»
