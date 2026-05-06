theorem convex_concave_gradient_zero_implies_minimax
    {n m : ℕ}
    {f : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → ℝ}
    (hdiff : Differentiable ℝ f)
    (hconv :
      ∀ z : EuclideanSpace ℝ (Fin m),
        ConvexOn ℝ Set.univ (fun x : EuclideanSpace ℝ (Fin n) => f (x, z)))
    (hconc :
      ∀ x : EuclideanSpace ℝ (Fin n),
        ConcaveOn ℝ Set.univ (fun z : EuclideanSpace ℝ (Fin m) => f (x, z)))
    (hex :
      ∃ xBar : EuclideanSpace ℝ (Fin n), ∃ zBar : EuclideanSpace ℝ (Fin m),
        fderiv ℝ f (xBar, zBar) = 0) :
    sInf (Set.range fun x : EuclideanSpace ℝ (Fin n) =>
      sSup (Set.range fun z : EuclideanSpace ℝ (Fin m) => f (x, z))) =
    sSup (Set.range fun z : EuclideanSpace ℝ (Fin m) =>
      sInf (Set.range fun x : EuclideanSpace ℝ (Fin n) => f (x, z))) := by
  sorry
