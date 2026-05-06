theorem unconstrainedMinimizer_along_steepestDescentLine
    {n mE mI : ℕ}
    (Ae : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin mE))
    (AI : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin mI))
    (ce : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin mE))
    (cI : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin mI))
    (x : EuclideanSpace ℝ (Fin n))
    (s : EuclideanSpace ℝ (Fin mI))
    (S : EuclideanSpace ℝ (Fin mI) → EuclideanSpace ℝ (Fin mI))
    (ATe :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin mE) → EuclideanSpace ℝ (Fin n))
    (ATI :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin mI) → EuclideanSpace ℝ (Fin n))
    (hS : ∀ v : EuclideanSpace ℝ (Fin mI), ∀ i : Fin mI, (S v) i = s i * v i)
    (hATe :
      ∀ u : EuclideanSpace ℝ (Fin n), ∀ w : EuclideanSpace ℝ (Fin mE),
        ⟪Ae x u, w⟫ = ⟪u, ATe x w⟫)
    (hATI :
      ∀ u : EuclideanSpace ℝ (Fin n), ∀ w : EuclideanSpace ℝ (Fin mI),
        ⟪AI x u, w⟫ = ⟪u, ATI x w⟫)
    (hqgrad :
      let r_x : EuclideanSpace ℝ (Fin n) := ATe x (ce x) + ATI x (cI x - s)
      let r_s : EuclideanSpace ℝ (Fin mI) := -S (cI x - s)
      let r : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin mI) := (r_x, r_s)
      let q : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin mI)) → ℝ :=
        fun v =>
          ‖Ae x v.1 + ce x‖ ^ 2 + ‖AI x v.1 - S v.2 + (cI x - s)‖ ^ 2
      ∀ v : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin mI),
        (fderiv ℝ q 0) v = ⟪(2 : ℝ) • r.1, v.1⟫ + ⟪(2 : ℝ) • r.2, v.2⟫)
    (hdenom :
      let r_x : EuclideanSpace ℝ (Fin n) := ATe x (ce x) + ATI x (cI x - s)
      let r_s : EuclideanSpace ℝ (Fin mI) := -S (cI x - s)
      let r : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin mI) := (r_x, r_s)
      r ≠ 0 →
        (2 : ℝ) * (‖Ae x r_x‖ ^ 2 + ‖AI x r_x - S r_s‖ ^ 2) ≠ 0) :
    let r_x : EuclideanSpace ℝ (Fin n) := ATe x (ce x) + ATI x (cI x - s)
    let r_s : EuclideanSpace ℝ (Fin mI) := -S (cI x - s)
    let r : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin mI) := (r_x, r_s)
    let d : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin mI) := ((-2 : ℝ) • r.1, (-2 : ℝ) • r.2)
    let q : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin mI)) → ℝ :=
      fun v =>
        ‖Ae x v.1 + ce x‖ ^ 2 + ‖AI x v.1 - S v.2 + (cI x - s)‖ ^ 2
    let αStar : ℝ :=
      if hne : r ≠ 0 then
        ‖r‖ ^ 2 /
          ((2 : ℝ) * (‖Ae x r_x‖ ^ 2 + ‖AI x r_x - S r_s‖ ^ 2))
      else 0
    IsUnconstrainedMinimizer (fun α : ℝ => q (α • d)) αStar ∧
      (αStar =
        if hne : r ≠ 0 then
          ‖r‖ ^ 2 /
            ((2 : ℝ) * (‖Ae x r_x‖ ^ 2 + ‖AI x r_x - S r_s‖ ^ 2))
        else 0) ∧
      (αStar • d = ((-2 * αStar) • r.1, (-2 * αStar) • r.2)) := by
  sorry
