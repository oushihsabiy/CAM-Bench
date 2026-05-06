theorem slack_variable_kkt_iff_original_kkt
    {n mE mI : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (cE : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin mE))
    (cI : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin mI))
    (f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (AE : EuclideanSpace ℝ (Fin n) → (Fin mE → EuclideanSpace ℝ (Fin n)))
    (AI : EuclideanSpace ℝ (Fin n) → (Fin mI → EuclideanSpace ℝ (Fin n)))
    (hf' : ∀ x v, (fderiv ℝ f x) v = ⟪f' x, v⟫)
    (hAE :
      ∀ x i v, (fderiv ℝ (fun x => cE x i) x) v = ⟪AE x i, v⟫)
    (hAI :
      ∀ x i v, (fderiv ℝ (fun x => cI x i) x) v = ⟪AI x i, v⟫)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∃ s : EuclideanSpace ℝ (Fin mI),
      ∃ y : EuclideanSpace ℝ (Fin mE),
        ∃ z : EuclideanSpace ℝ (Fin mI),
          KKTStationarity f' AE AI x y z ∧
          PrimalFeasibility cE cI x s ∧
          DualFeasibility z ∧
          (fun i : Fin mI => s i * z i) = 0) ↔
      KKTConditions f cE cI f' AE AI x := by
  sorry
