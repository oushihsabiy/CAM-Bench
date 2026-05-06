theorem convexConcave_iff_hessian_blocks_semidefinite
    {n m : ℕ}
    {f : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → ℝ}
    (hf : ContDiff ℝ 2 f) :
    ((
      ∀ z : EuclideanSpace ℝ (Fin m),
        ConvexOn ℝ Set.univ (fun x : EuclideanSpace ℝ (Fin n) => f (x, z))) ∧
      (∀ x : EuclideanSpace ℝ (Fin n),
        ConcaveOn ℝ Set.univ (fun z : EuclideanSpace ℝ (Fin m) => f (x, z)))
    ) ↔
    (∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m),
      (∀ v : EuclideanSpace ℝ (Fin n),
        0 ≤
          (fderiv ℝ
            (fun x : EuclideanSpace ℝ (Fin n) =>
              (fderiv ℝ (fun x' : EuclideanSpace ℝ (Fin n) => f (x', p.2)) x) v)
            p.1) v) ∧
      (∀ w : EuclideanSpace ℝ (Fin m),
        (fderiv ℝ
          (fun z : EuclideanSpace ℝ (Fin m) =>
            (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin m) => f (p.1, z')) z) w)
          p.2) w ≤ 0)) := by
  sorry
