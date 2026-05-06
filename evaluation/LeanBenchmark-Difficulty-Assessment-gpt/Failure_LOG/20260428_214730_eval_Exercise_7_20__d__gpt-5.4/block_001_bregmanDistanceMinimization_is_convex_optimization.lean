theorem bregmanDistanceMinimization_is_convex_optimization
    (P : BregmanDistanceMinimization)
    (h_strict : StrictConvexOn ℝ (Set.univ : Set (Fin P.n → ℝ)) P.f)
    (hC : Convex ℝ P.C) :
    ConvexOn ℝ P.C P.objective := by
  simpa [BregmanDistanceMinimization.objective] using
    h_strict.convexOn.restrict hC