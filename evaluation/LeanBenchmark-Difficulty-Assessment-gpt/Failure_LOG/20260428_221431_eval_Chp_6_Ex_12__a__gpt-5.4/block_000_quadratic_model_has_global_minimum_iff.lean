theorem quadratic_model_has_global_minimum_iff
    {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℝ) (g : n → ℝ)
    (hsymm : B.IsSymm) :
    (∃ d₀ : n → ℝ, IsMinOn
      (fun d : n → ℝ =>
        dotProduct g d + (1 / 2 : ℝ) * dotProduct d (fun i => ∑ j, B i j * d j))
      Set.univ d₀) ↔
      ((∀ x : n → ℝ, 0 ≤ dotProduct x (fun i => ∑ j, B i j * x j)) ∧
        ∃ y : n → ℝ, B.mulVec y = g) := by
  sorry

/- [BLOCK Chp.6 Ex.12-(a) | 36 | thm]
Let B ∈ ℝ^{n imes n} be a real symmetric matrix, and let g ∈ ℝ^n. Define m(d)=gᵀ d+
rac{1}{2}dᵀ B d, d ∈ ℝ^n. Let B succeq 0 denote that B is positive semidefinite, namely, xᵀ B x ≥ 0,
orall x ∈ ℝ^n. Prove that, under the condition B succeq 0, any vector d satisfying Bd=-g is a global
minimizer of m(d).
-/
