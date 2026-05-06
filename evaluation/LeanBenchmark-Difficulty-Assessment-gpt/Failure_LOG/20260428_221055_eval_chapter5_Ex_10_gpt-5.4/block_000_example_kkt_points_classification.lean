theorem example_kkt_points_classification :
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
    -- KKT 点恰好是 x00, x85_165, x22
    (∀ x : EuclideanSpace ℝ (Fin 2),
      IsKKTPoint f g h x ↔ x = x00 ∨ x = x85_165 ∨ x = x22) ∧
    -- x00 = (0,0) 是全局极小点，目标值 0
    f x00 = 0 ∧
    (∀ x : EuclideanSpace ℝ (Fin 2), feasible x → f x00 ≤ f x) ∧
    -- x85_165 = (8/5, 16/5) 是局部极小点但非全局，目标值 8/5
    f x85_165 = 8 / 5 ∧
    (∃ r > 0, ∀ x : EuclideanSpace ℝ (Fin 2),
      feasible x → ‖x - x85_165‖ < r → f x85_165 ≤ f x) ∧
    ¬(∀ x : EuclideanSpace ℝ (Fin 2), feasible x → f x85_165 ≤ f x) ∧
    -- x22 = (2,2) 是局部极大点，目标值 2
    f x22 = 2 ∧
    (∃ r > 0, ∀ x : EuclideanSpace ℝ (Fin 2),
      feasible x → ‖x - x22‖ < r → f x ≤ f x22) ∧
    ¬(∃ r > 0, ∀ x : EuclideanSpace ℝ (Fin 2),
      feasible x → ‖x - x22‖ < r → f x22 ≤ f x) := by
  sorry

/- [BLOCK chapter5 Ex.10 | 12 | thm]
Consider the two-variable constrained problem. Prove that the KKT points of this problem are (0,0),
≤ft((8)/(5),(16)/(5)), (2,2), and among them, (0,0) is a global minimizer, with objective function
value 0; ≤ft((8)/(5),(16)/(5)) is a local minimizer but not a global minimizer, with objective
function value (8)/(5); (2,2) is a local maximizer, with objective function value 2.
-/
