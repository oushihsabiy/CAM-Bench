theorem exists_taylor_expansion_cos
    (x p : ℝ) :
    ∃ t : ℝ,
      t ∈ Set.Ioo (0 : ℝ) 1 ∧
        Real.cos (x + p) =
          Real.cos x - Real.sin x * p - (1 / 2 : ℝ) * Real.cos x * p ^ 2 +
            (1 / 6 : ℝ) * Real.sin (x + t * p) * p ^ 3 := by
  sorry

/- [BLOCK Exercise 2.4 | 11 | thm]
In particular, at x=1, prove that for every p∈ℝ, there exists t∈(0,1) such that
cos(1+p)=cos 1-sin 1p-(1)/(2)cos 1p^2+(1)/(6)sin(1+tp)p^3.
-/
