theorem graphEmbeddingLeastSquares_optimal_vectors_satisfy_symmetric_linear_systems
    (p : GraphEmbeddingLeastSquaresProblem) :
    ∃ C : Matrix (Fin p.M) (Fin p.M) ℝ,
      Matrix.IsSymm C ∧
      (∀ i j : Fin p.M,
        C i j =
          if i = j then
            (((p.edges.filter (fun e => e.1.1 = i.1 ∨ e.2.1 = i.1)).card : ℕ) : ℝ)
          else
            -((((p.edges.filter (fun e =>
                (e.1.1 = i.1 ∧ e.2.1 = j.1) ∨
                (e.1.1 = j.1 ∧ e.2.1 = i.1))).card : ℕ) : ℝ))) ∧
      ∀ x : Fin p.M → Fin 2 → ℝ,
        optimalVector p.feasibleSet p.objective x →
        let u : Fin p.M → ℝ := fun i => x i 0
        let v : Fin p.M → ℝ := fun i => x i 1
        let d₁ : Fin p.M → ℝ := fun i =>
          ∑ e ∈ p.edges,
            if h1 : e.1.1 = i.1 ∧ p.M ≤ e.2.1 then p.fixedData e.2 h1.2 0
            else if h2 : e.2.1 = i.1 ∧ p.M ≤ e.1.1 then p.fixedData e.1 h2.2 0
            else 0
        let d₂ : Fin p.M → ℝ := fun i =>
          ∑ e ∈ p.edges,
            if h1 : e.1.1 = i.1 ∧ p.M ≤ e.2.1 then p.fixedData e.2 h1.2 1
            else if h2 : e.2.1 = i.1 ∧ p.M ≤ e.1.1 then p.fixedData e.1 h2.2 1
            else 0
        linearSystem C u d₁ ∧ linearSystem C v d₂ := by
  sorry
