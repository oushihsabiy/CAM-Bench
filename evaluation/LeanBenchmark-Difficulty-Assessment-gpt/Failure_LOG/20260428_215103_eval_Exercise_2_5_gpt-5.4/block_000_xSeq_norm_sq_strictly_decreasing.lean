theorem xSeq_norm_sq_strictly_decreasing :
    ∀ k : ℕ,
      let f : (Fin 2 → ℝ) → ℝ := fun x => ‖x‖ ^ 2
      let xSeq : ℕ → Fin 2 → ℝ :=
        fun k =>
          ![
            (1 + (1 : ℝ) / (2 : ℝ) ^ k) * Real.cos k,
            (1 + (1 : ℝ) / (2 : ℝ) ^ k) * Real.sin k
          ]
      f (xSeq (k + 1)) < f (xSeq k) := by
  sorry

/- [BLOCK Exercise 2.5 | 3 | thm]
Let f:ℝ^2 → ℝ be defined by f(x)=‖x‖^2, where ‖x‖ is the Euclidean norm on ℝ^2. Let {xₖ}_{k=0}^∞ ⊂
ℝ^2 be given by xₖ=≤ft(1+(1)/(2^k))[cos k; sin k], k=0,1,2,ldots, with k measured in radians. Show
that every point x ∈ ℝ^2 with ‖x‖^2=1 is a limit point of {xₖ}.
-/

