theorem convex_concave_gradient_zero_is_saddle_point
    {n m : ℕ}
    {f : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → ℝ}
    {xBar : EuclideanSpace ℝ (Fin n)}
    {zBar : EuclideanSpace ℝ (Fin m)}
    (hconv :
      ∀ z : EuclideanSpace ℝ (Fin m),
        ConvexOn ℝ Set.univ (fun x : EuclideanSpace ℝ (Fin n) => f (x, z)))
    (hconc :
      ∀ x : EuclideanSpace ℝ (Fin n),
        ConcaveOn ℝ Set.univ (fun z : EuclideanSpace ℝ (Fin m) => f (x, z)))
    (hgrad : fderiv ℝ f (xBar, zBar) = 0) :
    ∀ x : EuclideanSpace ℝ (Fin n), ∀ z : EuclideanSpace ℝ (Fin m),
      f (xBar, z) ≤ f (xBar, zBar) ∧ f (xBar, zBar) ≤ f (x, zBar) := by
  sorry

/- [BLOCK chapter2 Ex.2.8-(b) | 10 | thm]
Let f:ℝ^n imes ℝ^m o ℝ be differentiable, and suppose that for any fixed z ∈ ℝ^m, the mapping x
mapsto f(x,z) is convex on ℝ^n, and for any fixed x ∈ ℝ^n, the mapping z mapsto f(x,z) is concave on
ℝ^m. That is, f is a convex--concave function with respect to (x,z). It is known that there exists
(ar x,ar z) ∈ ℝ^n imes ℝ^m such that
abla f(ar x,ar z)=0, where
abla f(ar x,ar z) denotes the ∇of f with respect to all variables (x,z). Prove that f satisfies
the minimax relation min_{x ∈ ℝ^n}sup_{z ∈ ℝ^m} f(x,z) = sup_{z ∈ ℝ^m}∈f_{x ∈ ℝ^n} f(x,z).
-/
