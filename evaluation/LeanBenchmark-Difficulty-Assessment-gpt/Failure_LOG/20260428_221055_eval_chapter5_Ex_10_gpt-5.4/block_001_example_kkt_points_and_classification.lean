theorem example_kkt_points_and_classification :
    let f : EuclideanSpace ℝ (Fin 2) → ℝ := fun x => x 0
    let g : Fin 1 → EuclideanSpace ℝ (Fin 2) → ℝ :=
      fun _ x => (x 0 - 4) ^ 2 + (x 1) ^ 2 - 16
    let h : Fin 1 → EuclideanSpace ℝ (Fin 2) → ℝ :=
      fun _ x => (x 0) ^ 2 + (x 1 - 2) ^ 2 - 4
    let x00 : EuclideanSpace ℝ (Fin 2) :=
      EuclideanSpace.single (0 : Fin 2) (0 : ℝ) + EuclideanSpace.single (1 : Fin 2) (0 : ℝ)
    let x85_165 : EuclideanSpace ℝ (Fin 2) :=
      EuclideanSpace.single (0 : Fin 2) (8 / 5 : ℝ) +
        EuclideanSpace.single (1 : Fin 2) (16 / 5 : ℝ)
    let x22 : EuclideanSpace ℝ (Fin 2) :=
      EuclideanSpace.single (0 : Fin 2) (2 : ℝ) +
        EuclideanSpace.single (1 : Fin 2) (2 : ℝ)
    let feasible := fun x : EuclideanSpace ℝ (Fin 2) => g 0 x ≤ 0 ∧ h 0 x = 0
    (∀ x : EuclideanSpace ℝ (Fin 2),
      IsKKTPoint f g h x ↔ x = x00 ∨ x = x85_165 ∨ x = x22) ∧
    f x00 = 0 ∧
    (∀ x : EuclideanSpace ℝ (Fin 2), feasible x → f x00 ≤ f x) ∧
    f x85_165 = 8 / 5 ∧
    (∃ r > 0, ∀ x : EuclideanSpace ℝ (Fin 2),
      feasible x → ‖x - x85_165‖ < r → f x85_165 ≤ f x) ∧
    ¬(∀ x : EuclideanSpace ℝ (Fin 2), feasible x → f x85_165 ≤ f x) ∧
    f x22 = 2 ∧
    (∃ r > 0, ∀ x : EuclideanSpace ℝ (Fin 2),
      feasible x → ‖x - x22‖ < r → f x ≤ f x22) := by
  sorry
