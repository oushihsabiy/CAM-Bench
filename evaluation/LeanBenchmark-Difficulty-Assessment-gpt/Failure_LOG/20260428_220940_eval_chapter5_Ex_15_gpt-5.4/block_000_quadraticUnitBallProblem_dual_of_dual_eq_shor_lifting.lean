theorem quadraticUnitBallProblem_dual_of_dual_eq_shor_lifting
    {n : ℕ} (p : QuadraticUnitBallProblem n) :
    ∃ sdp : ShorLiftingSDP n,
      sdp.A = p.A ∧
      sdp.b = p.b ∧
      sdp.objective =
        (fun q =>
          let X := q.1
          let x := q.2
          Matrix.trace (p.A * X) + 2 * dotProduct p.b x) ∧
      sdp.feasible =
        {q |
          let X := q.1
          let x := q.2
          Matrix.IsSymm X ∧
          Matrix.trace X ≤ 1 ∧
          Matrix.PosSemidef
            (Matrix.fromBlocks X (fun i _ => x i) (fun _ j => x j)
              (![![1]] : Matrix (Fin 1) (Fin 1) ℝ))} := by
  sorry
