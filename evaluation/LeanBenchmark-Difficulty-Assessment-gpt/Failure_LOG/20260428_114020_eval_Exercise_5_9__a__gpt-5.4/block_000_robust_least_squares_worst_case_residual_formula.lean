theorem robust_least_squares_worst_case_residual_formula
    {m n : ℕ} (p : RobustLeastSquaresSOCP m n) (x : Fin n → ℝ)
    (hR_nonneg : ∀ i : Fin m, ∀ j : Fin n, 0 ≤ p.R i j) :
    sSup
        ((fun A : Matrix (Fin m) (Fin n) ℝ => ‖A.mulVec x - p.b‖) ''
          {A : Matrix (Fin m) (Fin n) ℝ |
            ∀ i : Fin m, ∀ j : Fin n, |A i j - p.Abar i j| ≤ p.R i j}) =
      ‖fun i : Fin m => |p.Abar.mulVec x i - p.b i| + (p.R.mulVec (fun j : Fin n => |x j|)) i‖ := by
  sorry

/- [BLOCK Exercise 5.9-(a) | 12 | thm]
Let m,n ∈ ℕ, bar A ∈ ℝ^{m× n}, R ∈ ℝ^{m× n} with R_{ij} ≥ 0 for all i=1,ldots,m, j=1,ldots,n, and b
∈ ℝ^m. Define
A=≤ft{A∈ℝ^{m× n}| |A_{ij}-bar A_{ij}|≤ R_{ij}\ for all i=1,ldots,m,\ j=1,ldots,n}.
For x∈ℝ^n, let |x|∈ℝ^n denote the vector of componentwise absolute values, and let R|x|∈ℝ^m be the
usual matrix-vector product. Hence prove that the robust least-squares problem
min_{x∈ℝ^n}\ sup_{A∈A} ‖Ax-b‖_2
is equivalent to robust least-squares SOCP.
-/
