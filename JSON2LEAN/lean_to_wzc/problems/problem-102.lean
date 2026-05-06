import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-102»
/-
minimize & \sum_{i = 1}^m α_k rᵢ^k; subject to & ‖xⱼ - cᵢ‖_2 ≤ rᵢ, i = 1, ..., m, j ∈ Gᵢ,; & rᵢ ≥ 0,
i =
1, ..., m, with variables x₁, ..., xₙ ∈ ℝ^k, c₁, ..., cₘ ∈ ℝ^k, and r₁, ..., rₘ ∈ ℝ.
-/
structure MinimumEnclosingBallsProgram (k n m : ℕ) where
  G : Fin m → Set (Fin n)
  α : ℕ → ℝ
  c : Fin m → EuclideanSpace ℝ (Fin k)
  x : Fin n → EuclideanSpace ℝ (Fin k)
  r : Fin m → ℝ

def MinimumEnclosingBallsProgram.IsFeasible {k n m : ℕ}
    (p : MinimumEnclosingBallsProgram k n m) : Prop :=
  (∀ i : Fin m, ∀ j : Fin n, j ∈ p.G i → ‖p.x j - p.c i‖ ≤ p.r i) ∧
  ∀ i : Fin m, 0 ≤ p.r i

def MinimumEnclosingBallsProgram.objective {k n m : ℕ}
    (p : MinimumEnclosingBallsProgram k n m) : ℝ :=
  ∑ i : Fin m, p.α k * (p.r i) ^ k

/-
Let n, m, k ∈ ℕ with n, m, k ≥ 1. Let G₁, ..., Gₘ ⊆ {1, ..., n} be given nonempty index sets, and
let
α_k > 0. For decision variables x₁, ..., xₙ ∈ ℝ^k, introduce additional variables cᵢ ∈ ℝ^k and rᵢ ∈
ℝ
for i = 1, ..., m. For each i, let Vᵢ be the volume of the smallest closed Euclidean ball containing
{xⱼ | j ∈ Gᵢ}, and let V = \sum_{i = 1}^m Vᵢ. Prove that minimizing V over x₁, ..., xₙ is equivalent
to the convex optimization problem minimum enclosing balls program.
-/
theorem minimum_total_volume_equiv_minimum_enclosing_balls_program
    {k n m : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (G : Fin m → Set (Fin n))
    (hG_nonempty : ∀ i : Fin m, Set.Nonempty (G i))
    (α : ℕ → ℝ)
    (hα_pos : 0 < α k)
    (hα_volume : ∀ r : ℝ, 0 ≤ r →
      ∃ Vball : ℝ, Vball = α k * r ^ k)
    (hVidx_nonempty :
      ∀ x : Fin n → EuclideanSpace ℝ (Fin k), ∀ i : Fin m,
        Set.Nonempty {V_i : ℝ |
          ∃ c_i : EuclideanSpace ℝ (Fin k), ∃ r_i : ℝ,
            0 ≤ r_i ∧
            (∀ j : Fin n, j ∈ G i → ‖x j - c_i‖ ≤ r_i) ∧
            (∃ Vball : ℝ, Vball = α k * r_i ^ k ∧ V_i = Vball)})
    (hVidx_bddBelow :
      ∀ x : Fin n → EuclideanSpace ℝ (Fin k), ∀ i : Fin m,
        BddBelow {V_i : ℝ |
          ∃ c_i : EuclideanSpace ℝ (Fin k), ∃ r_i : ℝ,
            0 ≤ r_i ∧
            (∀ j : Fin n, j ∈ G i → ‖x j - c_i‖ ≤ r_i) ∧
            (∃ Vball : ℝ, Vball = α k * r_i ^ k ∧ V_i = Vball)})
    (hleft_nonempty :
      Set.Nonempty {V : ℝ | ∃ x : Fin n → EuclideanSpace ℝ (Fin k),
        ∃ Vidx : Fin m → ℝ,
          (∀ i : Fin m,
            Vidx i =
              sInf {V_i : ℝ |
                ∃ c_i : EuclideanSpace ℝ (Fin k), ∃ r_i : ℝ,
                  0 ≤ r_i ∧
                  (∀ j : Fin n, j ∈ G i → ‖x j - c_i‖ ≤ r_i) ∧
                  (∃ Vball : ℝ, Vball = α k * r_i ^ k ∧ V_i = Vball)}) ∧
          V = ∑ i : Fin m, Vidx i})
    (hleft_bddBelow :
      BddBelow {V : ℝ | ∃ x : Fin n → EuclideanSpace ℝ (Fin k),
        ∃ Vidx : Fin m → ℝ,
          (∀ i : Fin m,
            Vidx i =
              sInf {V_i : ℝ |
                ∃ c_i : EuclideanSpace ℝ (Fin k), ∃ r_i : ℝ,
                  0 ≤ r_i ∧
                  (∀ j : Fin n, j ∈ G i → ‖x j - c_i‖ ≤ r_i) ∧
                  (∃ Vball : ℝ, Vball = α k * r_i ^ k ∧ V_i = Vball)}) ∧
          V = ∑ i : Fin m, Vidx i})
    (hright_nonempty :
      Set.Nonempty {v : ℝ | ∃ p : MinimumEnclosingBallsProgram k n m,
        p.G = G ∧ p.α = α ∧ p.IsFeasible ∧ p.objective = v})
    (hright_bddBelow :
      BddBelow {v : ℝ | ∃ p : MinimumEnclosingBallsProgram k n m,
        p.G = G ∧ p.α = α ∧ p.IsFeasible ∧ p.objective = v}) :
    (sInf {V : ℝ | ∃ x : Fin n → EuclideanSpace ℝ (Fin k),
      ∃ Vidx : Fin m → ℝ,
        (∀ i : Fin m,
          Vidx i =
            sInf {V_i : ℝ |
              ∃ c_i : EuclideanSpace ℝ (Fin k), ∃ r_i : ℝ,
                0 ≤ r_i ∧
                (∀ j : Fin n, j ∈ G i → ‖x j - c_i‖ ≤ r_i) ∧
                (∃ Vball : ℝ, Vball = α k * r_i ^ k ∧ V_i = Vball)}) ∧
        V = ∑ i : Fin m, Vidx i}) =
    sInf {v : ℝ | ∃ p : MinimumEnclosingBallsProgram k n m,
      p.G = G ∧ p.α = α ∧ p.IsFeasible ∧ p.objective = v} := by
  sorry

/-
Let n, m, k ∈ ℕ with n, m, k ≥ 1. Let G₁, ..., Gₘ ⊆ {1, ..., n} be given nonempty index sets, and
let
α_k > 0. For decision variables x₁, ..., xₙ ∈ ℝ^k, introduce additional variables cᵢ ∈ ℝ^k and rᵢ ∈
ℝ
for i = 1, ..., m. Moreover, prove that the minimum enclosing balls program is convex, i.e., the
objective function \sum_{i = 1}^m α_k rᵢ^k is convex on {r ∈ ℝ^m | rᵢ ≥ 0}, and each constraint
function (x₁, ..., xₙ, c₁, ..., cₘ, r₁, ..., rₘ) mapsto ‖xⱼ - cᵢ‖_2 - rᵢ is convex.
-/
theorem minimum_enclosing_balls_program_is_convex
    {k n m : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (p : MinimumEnclosingBallsProgram k n m)
    (hG_nonempty : ∀ i : Fin m, Set.Nonempty (p.G i))
    (hα_pos : 0 < p.α k) :
    ConvexOn ℝ {r : Fin m → ℝ | ∀ i : Fin m, 0 ≤ r i}
      (fun r => ∑ i : Fin m, p.α k * (r i) ^ k) ∧
    ∀ i : Fin m, ∀ j : Fin n,
      ConvexOn ℝ Set.univ
        (fun z :
          (Fin n → EuclideanSpace ℝ (Fin k)) ×
            (Fin m → EuclideanSpace ℝ (Fin k)) × (Fin m → ℝ) =>
          ‖z.1 j - z.2.1 i‖ - z.2.2 i) := by
  sorry
end «problem-102»
