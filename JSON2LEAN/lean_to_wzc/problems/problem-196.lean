import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-196»

/- [BLOCK Exercise 15.2-(c) | 5 | thm]
Let n ∈ ℕ with n ≥ 1. Let W ∈ S^n satisfy w_{ij} ≥ 0 for all i,j and w_{ii}=0 for i=1,dots,n, where
S^n is the set of real symmetric n × n matrices. Let 1 ∈ ℝ^n be the all-one vector, and for v ∈
ℝ^n, let diag(v) be the diagonal matrix with diagonal entries v₁,dots,vₙ. Define L(W) = -W +
diag(W1). Prove the standard SDP reformulation for algebraic connectivity:
inf_{x ⟂ 1, ‖x‖₂ = 1} xᵀLx = sup { t | L - t(I - (1/n)11ᵀ) ⪰ 0 }.
-/
theorem eigenvalue_minimization_sdp_reformulation {n : ℕ} (hn : 2 ≤ n)
    (W : Matrix (Fin n) (Fin n) ℝ)
    (hW_symm : Wᵀ = W)
    (hW_nonneg : ∀ i j, 0 ≤ W i j)
    (hW_diag : ∀ i : Fin n, W i i = 0) :
    let one : Fin n → ℝ := fun _ => 1
    let L : Matrix (Fin n) (Fin n) ℝ :=
      -W + Matrix.diagonal (fun i => ∑ j : Fin n, W i j * one j)
    sInf {r : ℝ | ∃ x : Fin n → ℝ,
      (∑ i : Fin n, x i) = 0 ∧
      (∑ i : Fin n, x i ^ 2) = 1 ∧
      r = ∑ i : Fin n, ∑ j : Fin n, x i * L i j * x j} =
    sSup {t : ℝ |
      Matrix.PosSemidef
        (L - t • ((1 : Matrix (Fin n) (Fin n) ℝ) -
          ((1 / (n : ℝ)) • Matrix.vecMulVec one one)))} := by
  sorry

end «problem-196»
