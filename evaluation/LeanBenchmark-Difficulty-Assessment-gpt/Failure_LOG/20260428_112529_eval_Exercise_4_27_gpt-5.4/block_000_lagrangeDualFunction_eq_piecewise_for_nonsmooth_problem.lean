theorem lagrangeDualFunction_eq_piecewise_for_nonsmooth_problem
    {n m : ℕ}
    (P : PrimalNonsmoothOptimizationProblem n m)
    (h_def : P.h = fun u : ℝ => if 1 ≤ u then (u - 1) ^ 2 / 2 else 0) :
    ∀ ν : Fin m → Fin 3 → ℝ,
      let D : DualNonsmoothOptimizationProblem n m :=
        { c := P.c
          A := fun i => fun k j => P.A i (Pi.single j (1 : ℝ)) k
          b := P.b }
      (sInf
        (Set.range
          (fun xy : (Fin n → ℝ) × (Fin m → Fin 3 → ℝ) =>
            show EReal from
              (((∑ i : Fin m,
                    (P.h ‖xy.2 i‖ + (∑ k : Fin 3, ν i k * P.b i k) -
                      (∑ k : Fin 3, ν i k * xy.2 i k))) +
                  ((∑ i : Fin m, ∑ k : Fin 3, ν i k * P.A i xy.1 k) -
                    ∑ j : Fin n, P.c j * xy.1 j)) : ℝ))) =
        if ∀ j : Fin n,
            ∑ i : Fin m, ∑ k : Fin 3, P.A i (Pi.single j (1 : ℝ)) k * ν i k = P.c j then
          ((∑ i : Fin m,
              ((∑ k : Fin 3, P.b i k * ν i k) - ‖ν i‖ - (1 / 2 : ℝ) * ‖ν i‖ ^ 2) : ℝ) : EReal)
        else ⊥) ∧
      (D.feasible ν ↔
        ∀ j : Fin n,
          ∑ i : Fin m, ∑ k : Fin 3, P.A i (Pi.single j (1 : ℝ)) k * ν i k = P.c j) ∧
      (D.objective ν =
        ∑ i : Fin m,
          ((∑ k : Fin 3, P.b i k * ν i k) - ‖ν i‖ - (1 / 2 : ℝ) * ‖ν i‖ ^ 2)) := by
  sorry
