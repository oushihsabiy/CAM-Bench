theorem piecewiseAffineRegression_equivalent_to_convexSplineRegression
    (P : ConvexSplineRegressionProblem)
    (hN : 1 ≤ P.N)
    (hn : 1 ≤ P.n)
    (hK : 1 ≤ P.K)
    (hlam : 0 < P.lam)
    (hp_strictMono : StrictMono P.p)
    (hfeas : P.isFeasible) :
    (∀ j : Fin P.n,
      Continuous
        (fun t =>
          P.a j + P.b j * t
            + ∑ k : Fin P.K, P.u j k * ConvexSplineRegressionProblem.posPart (t - P.p k))) ∧
    (∀ j : Fin P.n,
      PiecewiseAffine
        (fun t =>
          P.a j + P.b j * t
            + ∑ k : Fin P.K, P.u j k * ConvexSplineRegressionProblem.posPart (t - P.p k))) ∧
    (∀ j : Fin P.n,
      KnotPoints
        (fun t =>
          P.a j + P.b j * t
            + ∑ k : Fin P.K, P.u j k * ConvexSplineRegressionProblem.posPart (t - P.p k))
        (Finset.univ.image P.p)) ∧
    -- The full objective (over all parameter choices α,a,b,u) is convex
    ConvexOn ℝ Set.univ
      (fun params : ℝ × (Fin P.n → ℝ) × (Fin P.n → ℝ) × (Fin P.n → Fin P.K → ℝ) =>
        (1 / (P.N : ℝ)) *
          ∑ i : Fin P.N,
            (P.y i - params.1 -
              ∑ j : Fin P.n,
                (params.2.1 j + params.2.2.1 j * P.x i j +
                  ∑ k : Fin P.K,
                    params.2.2.2 j k *
                      ConvexSplineRegressionProblem.posPart (P.x i j - P.p k))) ^ 2 +
        P.lam * ∑ j : Fin P.n, ∑ k : Fin P.K, |params.2.2.2 j k|) := by
  sorry
