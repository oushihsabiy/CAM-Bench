theorem cone_closure_has_nonempty_interior
    (P : ConvexOptimizationProblem)
    (hconvex : ∀ i : Fin P.m, ConvexOn ℝ Set.univ (P.f i))
    (x_tilde : EuclideanSpace ℝ (Fin P.n))
    (hSlater : ∀ i : Fin P.m, P.f i x_tilde < 0) :
    HasNonemptyInterior
      (closure
        {z : EuclideanSpace ℝ (Fin (P.n + 1)) |
          0 < z 0 ∧
          (∀ i : Fin P.m,
            z 0 * P.f i
                (((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin P.n)).symm
                  (fun j : Fin P.n => z j.succ / z 0) : EuclideanSpace ℝ (Fin P.n))) ≤ 0)}) := by
  classical
  by_cases hm : IsEmpty (Fin P.m)
  · refine ⟨?_⟩
    ext z
    simp [hm.false_iff_nonempty.mp ?_]
    exact Classical.choice (not_isEmpty_iff.mp (by
      intro h
      exact hm h))
  · let z : EuclideanSpace ℝ (Fin (P.n + 1)) :=
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (P.n + 1))).symm
        (fun j => if h : j = 0 then (1 : ℝ) else x_tilde j.succAbove 0)
    have hz0 : z 0 = 1 := by
      simp [z]
    have hzsucc : ∀ j : Fin P.n, z j.succ = x_tilde j := by
      intro j
      simp [z]
    have hx :
        (((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin P.n)).symm
          (fun j : Fin P.n => z j.succ / z 0) : EuclideanSpace ℝ (Fin P.n))) = x_tilde := by
      apply (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin P.n)).injective
      ext j
      simp [hzsucc, hz0]
    have hzmem :
        z ∈
          {z : EuclideanSpace ℝ (Fin (P.n + 1)) |
            0 < z 0 ∧
            (∀ i : Fin P.m,
              z 0 * P.f i
                  (((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin P.n)).symm
                    (fun j : Fin P.n => z j.succ / z 0) : EuclideanSpace ℝ (Fin P.n))) ≤ 0)} := by
      refine ⟨by simpa [hz0], ?_⟩
      intro i
      rw [hz0, one_mul, hx]
      exact le_of_lt (hSlater i)
    have hnonempty :
        Set.Nonempty
          (interior
            (closure
              {z : EuclideanSpace ℝ (Fin (P.n + 1)) |
                0 < z 0 ∧
                (∀ i : Fin P.m,
                  z 0 * P.f i
                      (((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin P.n)).symm
                        (fun j : Fin P.n => z j.succ / z 0) : EuclideanSpace ℝ (Fin P.n))) ≤ 0)})) := by
      exact ⟨z, interior_subset (subset_closure hzmem)⟩
    simpa [Set.nonempty_interior] using hnonempty