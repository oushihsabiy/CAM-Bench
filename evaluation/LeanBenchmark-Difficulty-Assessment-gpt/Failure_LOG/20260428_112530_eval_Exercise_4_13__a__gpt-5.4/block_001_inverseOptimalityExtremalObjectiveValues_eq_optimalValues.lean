theorem inverseOptimalityExtremalObjectiveValues_eq_optimalValues
    {n m r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin r → (Fin n → ℝ))
    (b : Fin r → (Fin m → ℝ))
    (i : Fin n) :
    optimalValueMax
        (fun P : InverseOptimalityMaximizationLP n m r => ((P.objective P.i : ℝ) : EReal))
        {P | P.A = A ∧ P.x = x ∧ P.b = b ∧ P.i = i ∧ P.is_feasible} =
      sSup (((fun c : Fin n → ℝ => ((c i : ℝ) : EReal)) '' inverseOptimalitySet A x b)) ∧
    optimalValueMin
        (fun P : InverseOptimalityMinimizationLP n m r => ((P.objective : ℝ) : EReal))
        {P | P.A = A ∧ P.x = x ∧ P.b = b ∧ P.objectiveIndex = i ∧ P.is_feasible} =
      sInf (((fun c : Fin n → ℝ => ((c i : ℝ) : EReal)) '' inverseOptimalitySet A x b)) := by
  sorry
