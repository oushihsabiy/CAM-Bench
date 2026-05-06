theorem exists_taylor_expansion_cos_one_div
    {x p : ℝ}
    (hx : x ≠ 0)
    (hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, x + s * p ≠ 0) :
    ∃ t : ℝ,
      t ∈ Set.Ioo (0 : ℝ) 1 ∧
        Real.cos (1 / (x + p)) =
          Real.cos (1 / x) + (Real.sin (1 / x) / x ^ 2) * p +
            (1 / 2 : ℝ) *
              (-Real.cos (1 / (x + t * p)) / (x + t * p) ^ 4 -
                2 * Real.sin (1 / (x + t * p)) / (x + t * p) ^ 3) *
              p ^ 2 := by
  sorry

/- [BLOCK Exercise 2.4 | 10 | thm]
For every x,p∈ℝ, prove that there exists t∈(0,1) such that
cos(x+p)=cos x-sin xp-(1)/(2)cos xp^2+(1)/(6)sin(x+tp)p^3.
-/
