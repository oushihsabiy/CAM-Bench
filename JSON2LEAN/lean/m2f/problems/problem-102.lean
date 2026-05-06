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
  classical
  let S : (Fin n → EuclideanSpace ℝ (Fin k)) → Fin m → Set ℝ :=
    fun x i => {V_i : ℝ |
      ∃ c_i : EuclideanSpace ℝ (Fin k), ∃ r_i : ℝ,
        0 ≤ r_i ∧
        (∀ j : Fin n, j ∈ G i → ‖x j - c_i‖ ≤ r_i) ∧
        (∃ Vball : ℝ, Vball = α k * r_i ^ k ∧ V_i = Vball)}
  let L : Set ℝ := {V : ℝ | ∃ x : Fin n → EuclideanSpace ℝ (Fin k),
    ∃ Vidx : Fin m → ℝ,
      (∀ i : Fin m, Vidx i = sInf (S x i)) ∧
      V = ∑ i : Fin m, Vidx i}
  let R : Set ℝ := {v : ℝ | ∃ p : MinimumEnclosingBallsProgram k n m,
    p.G = G ∧ p.α = α ∧ p.IsFeasible ∧ p.objective = v}
  have hS_nonempty : ∀ x : Fin n → EuclideanSpace ℝ (Fin k), ∀ i : Fin m, Set.Nonempty (S x i) := by
    intro x i
    simpa [S] using hVidx_nonempty x i
  have hS_bddBelow : ∀ x : Fin n → EuclideanSpace ℝ (Fin k), ∀ i : Fin m, BddBelow (S x i) := by
    intro x i
    simpa [S] using hVidx_bddBelow x i
  have hleft_nonempty' : Set.Nonempty L := by
    simpa [L, S] using hleft_nonempty
  have hleft_bddBelow' : BddBelow L := by
    simpa [L, S] using hleft_bddBelow
  have hright_nonempty' : Set.Nonempty R := by
    simpa [R] using hright_nonempty
  have hright_bddBelow' : BddBelow R := by
    simpa [R] using hright_bddBelow
  change sInf L = sInf R
  refine le_antisymm ?_ ?_
  · -- Any feasible program gives an upper bound for the left-side witness built from componentwise infima.
    refine le_csInf hright_nonempty' ?_
    intro v hv
    rcases hv with ⟨p, hpG, hpα, hpFeasible, rfl⟩
    have hleft_mem : (∑ i : Fin m, sInf (S p.x i)) ∈ L := by
      refine ⟨p.x, fun i => sInf (S p.x i), ?_, rfl⟩
      intro i
      rfl
    have hcomponent_le : ∀ i : Fin m, sInf (S p.x i) ≤ α k * (p.r i) ^ k := by
      intro i
      apply csInf_le (hS_bddBelow p.x i)
      refine ⟨p.c i, p.r i, hpFeasible.2 i, ?_, α k * (p.r i) ^ k, rfl, rfl⟩
      intro j hj
      have hj' : j ∈ p.G i := by
        simpa [hpG] using hj
      exact hpFeasible.1 i j hj'
    have hsum_le : ∑ i : Fin m, sInf (S p.x i) ≤ p.objective := by
      simpa [MinimumEnclosingBallsProgram.objective, hpα] using
        Finset.sum_le_sum (fun i _ => hcomponent_le i)
    exact (csInf_le hleft_bddBelow' hleft_mem).trans hsum_le
  · -- Route correction: we avoid any attainment argument and use epsilon-near minimizers for each component.
    refine le_csInf hleft_nonempty' ?_
    intro V hV
    rcases hV with ⟨x, Vidx, hVidx, rfl⟩
    -- It suffices to beat every `ε > 0` by assembling one feasible program from near-minimizers.
    refine le_of_forall_pos_lt_add ?_
    intro ε hε
    have hm_pos_nat : 0 < m := Nat.succ_le_iff.mp hm
    have hm_pos : (0 : ℝ) < m := by
      exact_mod_cast hm_pos_nat
    let δ : ℝ := ε / (m : ℝ)
    have hδ_pos : 0 < δ := by
      exact div_pos hε hm_pos
    have happrox :
        ∀ i : Fin m,
          ∃ c_i : EuclideanSpace ℝ (Fin k), ∃ r_i : ℝ, ∃ V_i : ℝ,
            0 ≤ r_i ∧
            (∀ j : Fin n, j ∈ G i → ‖x j - c_i‖ ≤ r_i) ∧
            V_i = α k * r_i ^ k ∧
            V_i < sInf (S x i) + δ := by
      intro i
      obtain ⟨V_i, hV_i_mem, hV_i_lt⟩ := Real.lt_sInf_add_pos (hS_nonempty x i) hδ_pos
      rcases hV_i_mem with ⟨c_i, r_i, hr_i_nonneg, hcover, Vball, hVball, hV_i_eq⟩
      refine ⟨c_i, r_i, V_i, hr_i_nonneg, hcover, ?_, hV_i_lt⟩
      calc
        V_i = Vball := hV_i_eq
        _ = α k * r_i ^ k := hVball
    choose c r V' hr_nonneg hcover hVeq hVlt using happrox
    let p : MinimumEnclosingBallsProgram k n m :=
      { G := G, α := α, c := c, x := x, r := r }
    have hpFeasible : p.IsFeasible := by
      constructor
      · intro i j hj
        simpa [p] using hcover i j hj
      · intro i
        simpa [p] using hr_nonneg i
    have hp_mem : p.objective ∈ R := by
      refine ⟨p, rfl, rfl, hpFeasible, rfl⟩
    have hsInfR_le : sInf R ≤ p.objective := by
      exact csInf_le hright_bddBelow' hp_mem
    have hp_objective : p.objective = ∑ i : Fin m, V' i := by
      calc
        p.objective = ∑ i : Fin m, α k * (r i) ^ k := by
          rfl
        _ = ∑ i : Fin m, V' i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact (hVeq i).symm
    have i0 : Fin m := ⟨0, hm_pos_nat⟩
    have hsum_lt : (∑ i : Fin m, V' i) < ∑ i : Fin m, (sInf (S x i) + δ) := by
      refine Finset.sum_lt_sum (fun i _ => (hVlt i).le) ?_
      exact ⟨i0, by simp, hVlt i0⟩
    have hsum_delta : (∑ _i : Fin m, δ) = ε := by
      calc
        (∑ _i : Fin m, δ) = (m : ℝ) * δ := by
          simp [Finset.sum_const, Fintype.card_fin]
        _ = (m : ℝ) * (ε / (m : ℝ)) := by
          rfl
        _ = ε := by
          field_simp [δ, hm_pos.ne']
    have hsum_sInf_eq : (∑ i : Fin m, sInf (S x i)) = ∑ i : Fin m, Vidx i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact (hVidx i).symm
    have hp_lt : p.objective < ∑ i : Fin m, Vidx i + ε := by
      calc
        p.objective = ∑ i : Fin m, V' i := hp_objective
        _ < ∑ i : Fin m, (sInf (S x i) + δ) := hsum_lt
        _ = (∑ i : Fin m, sInf (S x i)) + ∑ _i : Fin m, δ := by
          rw [Finset.sum_add_distrib]
        _ = (∑ i : Fin m, sInf (S x i)) + ε := by
          rw [hsum_delta]
        _ = ∑ i : Fin m, Vidx i + ε := by
          rw [hsum_sInf_eq]
    exact hsInfR_le.trans_lt hp_lt

/-
Let n, m, k ∈ ℕ with n, m, k ≥ 1. Let G₁, ..., Gₘ ⊆ {1, ..., n} be given nonempty index sets, and
let
α_k > 0. For decision variables x₁, ..., xₙ ∈ ℝ^k, introduce additional variables cᵢ ∈ ℝ^k and rᵢ ∈
ℝ
for i = 1, ..., m. Moreover, prove that the minimum enclosing balls program is convex, i.e., the
objective function \sum_{i = 1}^m α_k rᵢ^k is convex on {r ∈ ℝ^m | rᵢ ≥ 0}, and each constraint
function (x₁, ..., xₙ, c₁, ..., cₘ, r₁, ..., rₘ) mapsto ‖xⱼ - cᵢ‖_2 - rᵢ is convex.
-/
/-- The nonnegative orthant in the radius coordinates is convex. -/
lemma nonnegative_radius_orthant_convex {m : ℕ} :
    Convex ℝ {r : Fin m → ℝ | ∀ i : Fin m, 0 ≤ r i} := by
  -- Check coordinatewise that nonnegativity is preserved by convex combinations.
  intro x hx y hy a b ha hb hab i
  simpa [smul_eq_mul] using add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))

/-- Each coordinate power term of the objective is convex on the nonnegative orthant. -/
lemma convexOn_radius_power_term {k m : ℕ} (i : Fin m) {a : ℝ} (ha : 0 ≤ a) :
    ConvexOn ℝ {r : Fin m → ℝ | ∀ j : Fin m, 0 ≤ r j} (fun r => a * (r i) ^ k) := by
  have hpow :
      ConvexOn ℝ {r : Fin m → ℝ | 0 ≤ r i} (fun r => (r i) ^ k) := by
    -- Pull back the one-variable convexity of `x ↦ x ^ k` along the coordinate projection.
    simpa using
      (convexOn_pow k).comp_linearMap (LinearMap.proj i : (Fin m → ℝ) →ₗ[ℝ] ℝ)
  have hpow_restricted :
      ConvexOn ℝ {r : Fin m → ℝ | ∀ j : Fin m, 0 ≤ r j} (fun r => (r i) ^ k) := by
    -- Restrict from the single-coordinate nonnegative half-line to the whole orthant.
    refine hpow.subset ?_ nonnegative_radius_orthant_convex
    intro r hr
    exact hr i
  -- Scale the convex power term by the nonnegative coefficient `a`.
  simpa [smul_eq_mul] using hpow_restricted.smul ha

/-- The objective is convex because it is a finite sum of convex coordinate power terms. -/
lemma convexOn_minimum_enclosing_balls_objective {k m : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    ConvexOn ℝ {r : Fin m → ℝ | ∀ i : Fin m, 0 ≤ r i}
      (fun r => ∑ i : Fin m, a * (r i) ^ k) := by
  classical
  have hsum :
      ∀ s : Finset (Fin m),
        ConvexOn ℝ {r : Fin m → ℝ | ∀ i : Fin m, 0 ≤ r i}
          (fun r => s.sum fun i => a * (r i) ^ k) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        -- The empty sum is the constant zero function.
        simpa using
          (convexOn_const
            (E := Fin m → ℝ) (𝕜 := ℝ)
            (s := {r : Fin m → ℝ | ∀ i : Fin m, 0 ≤ r i}) (0 : ℝ)
            nonnegative_radius_orthant_convex)
    | @insert i s hi hs =>
        -- Add one more convex coordinate term to the inductive partial sum.
        simpa [Finset.sum_insert, hi] using
          (convexOn_radius_power_term (k := k) (i := i) (a := a) ha).add hs
  -- Specialize the finite-sum statement to the full index set.
  simpa using hsum Finset.univ

/-- Each norm-minus-radius constraint is convex on the ambient product space. -/
lemma convexOn_norm_sub_radius_constraint {k n m : ℕ} (i : Fin m) (j : Fin n) :
    ConvexOn ℝ Set.univ
      (fun z :
        (Fin n → EuclideanSpace ℝ (Fin k)) ×
          (Fin m → EuclideanSpace ℝ (Fin k)) × (Fin m → ℝ) =>
        ‖z.1 j - z.2.1 i‖ - z.2.2 i) := by
  let xProj :
      ((Fin n → EuclideanSpace ℝ (Fin k)) ×
          (Fin m → EuclideanSpace ℝ (Fin k)) × (Fin m → ℝ)) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin k) :=
    (LinearMap.proj j).comp
      (LinearMap.fst ℝ (Fin n → EuclideanSpace ℝ (Fin k))
        ((Fin m → EuclideanSpace ℝ (Fin k)) × (Fin m → ℝ)))
  let cProj :
      ((Fin n → EuclideanSpace ℝ (Fin k)) ×
          (Fin m → EuclideanSpace ℝ (Fin k)) × (Fin m → ℝ)) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin k) :=
    (LinearMap.proj i).comp
      ((LinearMap.fst ℝ (Fin m → EuclideanSpace ℝ (Fin k)) (Fin m → ℝ)).comp
        (LinearMap.snd ℝ (Fin n → EuclideanSpace ℝ (Fin k))
          ((Fin m → EuclideanSpace ℝ (Fin k)) × (Fin m → ℝ))))
  let radiusProj :
      ((Fin n → EuclideanSpace ℝ (Fin k)) ×
          (Fin m → EuclideanSpace ℝ (Fin k)) × (Fin m → ℝ)) →ₗ[ℝ] ℝ :=
    (LinearMap.proj i).comp
      ((LinearMap.snd ℝ (Fin m → EuclideanSpace ℝ (Fin k)) (Fin m → ℝ)).comp
        (LinearMap.snd ℝ (Fin n → EuclideanSpace ℝ (Fin k))
          ((Fin m → EuclideanSpace ℝ (Fin k)) × (Fin m → ℝ))))
  let diffProj :
      ((Fin n → EuclideanSpace ℝ (Fin k)) ×
          (Fin m → EuclideanSpace ℝ (Fin k)) × (Fin m → ℝ)) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin k) :=
    xProj - cProj
  have hnorm :
      ConvexOn ℝ Set.univ
        (fun z :
          (Fin n → EuclideanSpace ℝ (Fin k)) ×
            (Fin m → EuclideanSpace ℝ (Fin k)) × (Fin m → ℝ) => ‖diffProj z‖) := by
    -- The norm is convex on the whole space, so it stays convex after a linear precomposition.
    simpa [diffProj] using convexOn_univ_norm.comp_linearMap diffProj
  have hradius :
      ConcaveOn ℝ Set.univ
        (fun z :
          (Fin n → EuclideanSpace ℝ (Fin k)) ×
            (Fin m → EuclideanSpace ℝ (Fin k)) × (Fin m → ℝ) => radiusProj z) := by
    -- Linear functions are both convex and concave on convex sets.
    simpa [radiusProj] using radiusProj.concaveOn (𝕜 := ℝ) convex_univ
  -- Subtract the linear radius term from the convex norm term.
  simpa [diffProj, xProj, cProj, radiusProj] using hnorm.sub hradius

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
  constructor
  · -- The objective is the finite sum of the convex coordinate power terms.
    exact convexOn_minimum_enclosing_balls_objective (k := k) (m := m) (a := p.α k) hα_pos.le
  · -- Each constraint is a norm of a linear difference minus a linear radius projection.
    intro i j
    exact convexOn_norm_sub_radius_constraint (k := k) (n := n) (m := m) i j
end «problem-102»
