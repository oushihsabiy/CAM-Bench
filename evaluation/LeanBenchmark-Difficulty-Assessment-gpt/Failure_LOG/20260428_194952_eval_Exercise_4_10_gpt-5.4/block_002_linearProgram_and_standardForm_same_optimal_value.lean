theorem linearProgram_and_standardForm_same_optimal_value
    (lp : LinearProgram)
    (sf : StandardFormLinearProgram)
    (hsf : sf.base = lp) :
    sInf (LinearProgram.objective lp '' lp.feasibleSet) =
      sInf
        ({y : ℝ |
            ∃ xPlus xMinus : Fin sf.base.n → ℝ,
              ∃ s : Fin sf.base.m → ℝ,
                (xPlus, xMinus, s) ∈ sf.feasibleSet ∧
                  sf.objective xPlus xMinus = y}) := by
  subst hsf
  rfl

/- [BLOCK Exercise 4.10 | 10 | thm]
Let n,m,p ∈ ℕ, c∈ ℝ^n, d∈ ℝ, G∈ ℝ^{m× n}, h∈ ℝ^m, A∈ ℝ^{p× n}, and b∈ ℝ^p. Consider the linear
program
array{ll}
minimize & cᵀ x+d ;
subject to & Gx ≤ h,;
& Ax=b,
array
with decision variable x∈ ℝ^n, and let
mathcal F={x∈ ℝ^n| Gx≤ h,\ Ax=b}.
Define the associated standard-form problem with variables x^+,x^-∈ ℝ^n and s∈ ℝ^m by
array{ll}
minimize & cᵀ x^+ - cᵀ x^- + d ;
subject to & Gx^+ - Gx^- + s = h,;
& Ax^+-Ax^-=b,;
& x^+≥ 0,quad x^-≥ 0,quad s≥ 0,
array
where all inequalities are componentwise, and let
mathcal F_{sf}={(x^+,x^-,s)∈ ℝ^n× ℝ^n× ℝ^m | x^+≥ 0,\ x^-≥ 0,\ s≥ 0,\ Gx^+-Gx^-+s=h,\ Ax^+-Ax^-=b}.
For x∈ ℝ^n, define x^+,x^-∈ ℝ^n componentwise by
(x^+)_i=xᵢ,0, (x^-)_i=-xᵢ,0quad (i=1,dots,n).
Prove that a point x∈ mathcal F is an optimal solution of the original problem if and only if there
exist x^+,x^-∈ ℝ^n such that (x^+,x^-,h-Gx)∈ mathcal F_{sf}, x=x^+-x^-, and (x^+,x^-,h-Gx) is an
optimal solution of the standard-form problem.
-/