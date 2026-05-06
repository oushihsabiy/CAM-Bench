import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-161»

-- def l2Norm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
--   Real.sqrt (∑ i, (x i) ^ 2)

-- /-
-- Let p(a) = c₀ + c_1a + c_2a^2 + ·s + c_ka^k be a real polynomial of degree at most k, where k∈ N0
-- and
-- c₀, ..., cₖ∈ ℝ. For A∈ ℝ^{n×n}, define p(A) = c_0I + c_1A + c_2A^2 + ·s + c_kA^k, where I is the n×
-- n
-- identity matrix. Let S^n be the set of real symmetric n× n matrices. For A∈ S^n, let σ(A) denote the
-- set of eigenvalues of A. Let ω⊂ ℝ be a nonempty union of intervals with 0notin ω, and define A = {A∈
-- S^n| σ(A)⊆ ω}. Assume Anevarnothing. For A∈ A and b∈ ℝ^n with ‖b‖_2 ≤ 1, define R^{wc} = sup_{A∈ A,
-- ‖b‖_2 ≤ 1}‖Ap(A)b - b‖_2, where ‖·‖_2 is the Euclidean norm. Prove that R^{wc} = sup_{λ∈ ω}|λ p(λ) -
-- 1|.
-- -/
-- open Matrix

-- theorem worst_case_residual_eq_iSup_spectral_scalar
--     (n : ℕ)
--     (k : ℕ)
--     (c : Fin (k + 1) → ℝ)
--     (Ω : Set ℝ)
--     (hΩ_nonempty : Ω.Nonempty)
--     (hΩ_is_union_of_intervals :
--       ∀ x ∈ Ω, ∀ y ∈ Ω, x ≤ y → Set.Icc x y ⊆ Ω)
--     (hΩ_zero : 0 ∉ Ω)
--     (hA_nonempty :
--       ∃ A : Matrix (Fin n) (Fin n) ℝ,
--         A.IsSymm ∧ ∀ μ : ℝ, μ ∈ spectrum ℝ A → μ ∈ Ω) :
--     let 𝒜 : Set (Matrix (Fin n) (Fin n) ℝ) :=
--       {A | A.IsSymm ∧ ∀ μ : ℝ, μ ∈ spectrum ℝ A → μ ∈ Ω}
--     -- p(A) = c₀·I + c₁·A + ··· + cₖ·Aᵏ
--     let pMat : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ :=
--       fun A => ∑ i : Fin (k + 1), c i • (A ^ (i : ℕ))
--     -- p(λ) = c₀ + c₁λ + ··· + cₖλᵏ
--     let pScalar : ℝ → ℝ :=
--       fun lam => ∑ i : Fin (k + 1), c i * lam ^ (i : ℕ)
--     -- R^wc = sup_{A ∈ 𝒜, ‖b‖₂ ≤ 1} ‖A·p(A)·b - b‖₂
--     let Rwc : ℝ :=
--       sSup {r : ℝ | ∃ A ∈ 𝒜, ∃ b : EuclideanSpace ℝ (Fin n),
--         ‖b‖ ≤ 1 ∧ r = ‖(A * pMat A).mulVec b - b‖}
--     Rwc = sSup ((fun lam : ℝ => |lam * pScalar lam - 1|) '' Ω) := by
--   sorry

-- /-
-- Let p(a) = c₀ + c_1a + c_2a^2 + ·s + c_ka^k be a real polynomial of degree at most k, where k∈ N0
-- and
-- c₀, ..., cₖ∈ ℝ. For A∈ ℝ^{n×n}, define p(A) = c_0I + c_1A + c_2A^2 + ·s + c_kA^k, where I is the n×
-- n
-- identity matrix. Let S^n be the set of real symmetric n× n matrices. For A∈ S^n, let σ(A) denote the
-- set of eigenvalues of A. Let ω⊂ ℝ be a nonempty union of intervals with 0notin ω, and define A = {A∈
-- S^n| σ(A)⊆ ω}. Assume Anevarnothing. For A∈ A and b∈ ℝ^n with ‖b‖_2 ≤ 1, define R^{wc} = sup_{A∈ A,
-- ‖b‖_2 ≤ 1}‖Ap(A)b - b‖_2, where ‖·‖_2 is the Euclidean norm. Hence, if p^star(a) = c₀^star + c₁^star
-- a + ·s + cₖ^star a^k is any polynomial of degree at most k that minimizes sup_{λ∈ ω}|λ p(λ) - 1|
-- among
-- all real polynomials p of degree at most k, then the coefficients c₀^star, ..., cₖ^star minimize
-- R^{wc}.
-- -/
-- theorem minimizer_of_scalar_sup_norm_gives_minimizer_of_worst_case_residual
--     {n : Type*} [Fintype n] [DecidableEq n]
--     (k : ℕ)
--     (Ω : Set ℝ)
--     (hΩ_nonempty : Ω.Nonempty)
--     (hΩ_zero : 0 ∉ Ω)
--     (hA_nonempty :
--       ∃ A : Matrix n n ℝ,
--         A.IsSymm ∧ ∀ μ : ℝ, μ ∈ spectrum ℝ A → μ ∈ Ω)
--     (cstar : Fin (k + 1) → ℝ)
--     (hopt :
--       ∀ c : Fin (k + 1) → ℝ,
--         sSup {r : ℝ | ∃ lam : ℝ, lam ∈ Ω ∧ r = |lam * (∑ i : Fin (k + 1), cstar i * lam ^ (i : ℕ)) - 1|}
--           ≤
--         sSup {r : ℝ | ∃ lam : ℝ, lam ∈ Ω ∧ r = |lam * (∑ i : Fin (k + 1), c i * lam ^ (i : ℕ)) - 1|}) :
--     ∀ c : Fin (k + 1) → ℝ,
--       sSup
--         {r : ℝ |
--           ∃ A : Matrix n n ℝ,
--             A.IsSymm ∧
--             (∀ μ : ℝ, μ ∈ spectrum ℝ A → μ ∈ Ω) ∧
--             ∃ b : n → ℝ,
--               l2Norm b ≤ 1 ∧
--               r = l2Norm (A.mulVec (∑ i : Fin (k + 1), (cstar i) • ((A ^ (i : ℕ)).mulVec b)) - b)}
--         ≤
--       sSup
--         {r : ℝ |
--           ∃ A : Matrix n n ℝ,
--             A.IsSymm ∧
--             (∀ μ : ℝ, μ ∈ spectrum ℝ A → μ ∈ Ω) ∧
--             ∃ b : n → ℝ,
--               l2Norm b ≤ 1 ∧
--               r = l2Norm (A.mulVec (∑ i : Fin (k + 1), (c i) • ((A ^ (i : ℕ)).mulVec b)) - b)} := by
--   sorry
namespace «problem-161»

def l2Norm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i) ^ 2)

/-
Let p(a) = c₀ + c_1a + c_2a^2 + ·s + c_ka^k be a real polynomial of degree at most k, where k∈ N0
and
c₀, ..., cₖ∈ ℝ. For A∈ ℝ^{n×n}, define p(A) = c_0I + c_1A + c_2A^2 + ·s + c_kA^k, where I is the n×
n
identity matrix. Let S^n be the set of real symmetric n× n matrices. For A∈ S^n, let σ(A) denote the
set of eigenvalues of A. Let ω⊂ ℝ be a nonempty union of intervals with 0notin ω, and define A = {A∈
S^n| σ(A)⊆ ω}. Assume Anevarnothing. For A∈ A and b∈ ℝ^n with ‖b‖_2 ≤ 1, define R^{wc} = sup_{A∈ A,
‖b‖_2 ≤ 1}‖Ap(A)b - b‖_2, where ‖·‖_2 is the Euclidean norm. Prove that R^{wc} = sup_{λ∈ ω}|λ p(λ) -
1|.
-/
open Matrix

theorem worst_case_residual_eq_iSup_spectral_scalar
    (n : ℕ)
    (hn : 0 < n)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (Ω : Set ℝ)
    (hΩ_nonempty : Ω.Nonempty)
    (hΩ_is_union_of_intervals :
      ∀ x ∈ Ω, ∀ y ∈ Ω, x ≤ y → Set.Icc x y ⊆ Ω)
    (hΩ_zero : 0 ∉ Ω)
    (hA_nonempty :
      ∃ A : Matrix (Fin n) (Fin n) ℝ,
        A.IsSymm ∧ ∀ μ : ℝ, μ ∈ spectrum ℝ A → μ ∈ Ω) :
    let 𝒜 : Set (Matrix (Fin n) (Fin n) ℝ) :=
      {A | A.IsSymm ∧ ∀ μ : ℝ, μ ∈ spectrum ℝ A → μ ∈ Ω}
    -- p(A) = c₀·I + c₁·A + ··· + cₖ·Aᵏ
    let pMat : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ :=
      fun A => ∑ i : Fin (k + 1), c i • (A ^ (i : ℕ))
    -- p(λ) = c₀ + c₁λ + ··· + cₖλᵏ
    let pScalar : ℝ → ℝ :=
      fun lam => ∑ i : Fin (k + 1), c i * lam ^ (i : ℕ)
    -- R^wc = sup_{A ∈ 𝒜, ‖b‖₂ ≤ 1} ‖A·p(A)·b - b‖₂
    let Rwc : ℝ :=
      sSup {r : ℝ | ∃ A ∈ 𝒜, ∃ b : EuclideanSpace ℝ (Fin n),
        ‖b‖ ≤ 1 ∧ r = ‖(A * pMat A).mulVec b - b‖}
    Rwc = sSup ((fun lam : ℝ => |lam * pScalar lam - 1|) '' Ω) := by
  sorry

/-
Let p(a) = c₀ + c_1a + c_2a^2 + ·s + c_ka^k be a real polynomial of degree at most k, where k∈ N0
and
c₀, ..., cₖ∈ ℝ. For A∈ ℝ^{n×n}, define p(A) = c_0I + c_1A + c_2A^2 + ·s + c_kA^k, where I is the n×
n
identity matrix. Let S^n be the set of real symmetric n× n matrices. For A∈ S^n, let σ(A) denote the
set of eigenvalues of A. Let ω⊂ ℝ be a nonempty union of intervals with 0notin ω, and define A = {A∈
S^n| σ(A)⊆ ω}. Assume Anevarnothing. For A∈ A and b∈ ℝ^n with ‖b‖_2 ≤ 1, define R^{wc} = sup_{A∈ A,
‖b‖_2 ≤ 1}‖Ap(A)b - b‖_2, where ‖·‖_2 is the Euclidean norm. Hence, if p^star(a) = c₀^star + c₁^star
a + ·s + cₖ^star a^k is any polynomial of degree at most k that minimizes sup_{λ∈ ω}|λ p(λ) - 1|
among
all real polynomials p of degree at most k, then the coefficients c₀^star, ..., cₖ^star minimize
R^{wc}.
-/
theorem minimizer_of_scalar_sup_norm_gives_minimizer_of_worst_case_residual
    {n : Type*} [Fintype n] [DecidableEq n]
    (k : ℕ)
    (Ω : Set ℝ)
    (hΩ_nonempty : Ω.Nonempty)
    (hΩ_zero : 0 ∉ Ω)
    (hA_nonempty :
      ∃ A : Matrix n n ℝ,
        A.IsSymm ∧ ∀ μ : ℝ, μ ∈ spectrum ℝ A → μ ∈ Ω)
    (cstar : Fin (k + 1) → ℝ)
    (hopt :
      ∀ c : Fin (k + 1) → ℝ,
        sSup {r : ℝ | ∃ lam : ℝ, lam ∈ Ω ∧ r = |lam * (∑ i : Fin (k + 1), cstar i * lam ^ (i : ℕ)) - 1|}
          ≤
        sSup {r : ℝ | ∃ lam : ℝ, lam ∈ Ω ∧ r = |lam * (∑ i : Fin (k + 1), c i * lam ^ (i : ℕ)) - 1|}) :
    ∀ c : Fin (k + 1) → ℝ,
      sSup
        {r : ℝ |
          ∃ A : Matrix n n ℝ,
            A.IsSymm ∧
            (∀ μ : ℝ, μ ∈ spectrum ℝ A → μ ∈ Ω) ∧
            ∃ b : n → ℝ,
              l2Norm b ≤ 1 ∧
              r = l2Norm (A.mulVec (∑ i : Fin (k + 1), (cstar i) • ((A ^ (i : ℕ)).mulVec b)) - b)}
        ≤
      sSup
        {r : ℝ |
          ∃ A : Matrix n n ℝ,
            A.IsSymm ∧
            (∀ μ : ℝ, μ ∈ spectrum ℝ A → μ ∈ Ω) ∧
            ∃ b : n → ℝ,
              l2Norm b ≤ 1 ∧
              r = l2Norm (A.mulVec (∑ i : Fin (k + 1), (c i) • ((A ^ (i : ℕ)).mulVec b)) - b)} := by
  sorry

end «problem-161»

end «problem-161»
