theorem standardForm_feasible_to_feasible
    (sf : StandardFormLinearProgram)
    {xPlus xMinus : Fin sf.base.n → ℝ}
    {s : Fin sf.base.m → ℝ}
    (hfeas : (xPlus, xMinus, s) ∈ sf.feasibleSet) :
    let x : Fin sf.base.n → ℝ := fun i => xPlus i - xMinus i
    (x ∈ sf.base.feasibleSet) ∧
      (sf.base.objective x = sf.objective xPlus xMinus) := by
  dsimp
  constructor
  · exact ⟨
      by
        intro i
        have hs0 : 0 ≤ s i := hfeas.2.2.1 i
        have hEq : sf.base.G (fun j => xPlus j - xMinus j) i + s i = sf.base.h i := hfeas.2.2.2.1 i
        linarith
      ,
      hfeas.2.2.2.2⟩
  · rfl

/- [BLOCK Exercise 4.10 | 9 | thm]

Let n, m, p ∈ ℕ, c ∈ ℝⁿ, d ∈ ℝ, G ∈ ℝ^{m×n}, h ∈ ℝᵐ, A ∈ ℝ^{p×n}, and b ∈ ℝᵖ. Consider the linear
program

minimize cᵀx + d

subject to Gx ≤ h,
Ax = b,

with decision variable x ∈ ℝⁿ, and let

𝓕 = {x ∈ ℝⁿ ∣ Gx ≤ h, Ax = b}.

Define the associated standard-form problem with variables x⁺, x⁻ ∈ ℝⁿ and s ∈ ℝᵐ by

minimize cᵀx⁺ - cᵀx⁻ + d

subject to Gx⁺ - Gx⁻ + s = h,
Ax⁺ - Ax⁻ = b,
x⁺ ≥ 0, x⁻ ≥ 0, s ≥ 0,

where all inequalities are componentwise, and let

𝓕_sf = {(x⁺, x⁻, s) ∈ ℝⁿ × ℝⁿ × ℝᵐ ∣ x⁺ ≥ 0, x⁻ ≥ 0, s ≥ 0, Gx⁺ - Gx⁻ + s = h, Ax⁺ - Ax⁻ = b}.

For x ∈ ℝⁿ, define x⁺, x⁻ ∈ ℝⁿ componentwise by

(x⁺)ᵢ = max{xᵢ, 0},   (x⁻)ᵢ = max{-xᵢ, 0}   (i = 1, …, n).

Prove that consequently, the two problems have the same optimal value.
-/