theorem lagrangian_and_dual_function_formula
    (P : EqualityConstrainedLeastSquares) :
    ∃ L : (P.n → ℝ) → (P.p → ℝ) → ℝ,
      ∃ g : (P.p → ℝ) → ℝ,
        (∀ x lam, L x lam = P.obj x + 2 * dotProduct lam (P.G.mulVec x - P.h)) ∧
        (∀ lam, g lam = sInf (Set.range fun x : P.n → ℝ => L x lam)) := by
  sorry
