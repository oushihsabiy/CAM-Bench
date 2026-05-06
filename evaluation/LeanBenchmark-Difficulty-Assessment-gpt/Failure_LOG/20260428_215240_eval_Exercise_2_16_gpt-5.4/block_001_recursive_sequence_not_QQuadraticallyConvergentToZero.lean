theorem recursive_sequence_not_QQuadraticallyConvergentToZero :
    ¬ QQuadraticallyConvergentToZero
      (Nat.rec
        ((1 / 4 : ℝ) ^ (2 ^ 0))
        (fun k xk =>
          if Even (k + 1) then
            (1 / 4 : ℝ) ^ (2 ^ (k + 1))
          else
            xk / (k + 1))) := by
  sorry

/- [BLOCK Exercise 2.16 | 15 | thm]
Let {xₖ}_{k≥ 0}⊂ ℝ be defined by
xₖ=
cases
(14)^{2^k}, & if k is even,;
x_{k-1}/k, & if k is odd.
cases
Using the following definition for a sequence {xₖ}⊂ ℝ converging to 0: {xₖ} is R-quadratically
convergent to 0 if there exist a sequence {yₖ}⊂ [0,∞) and a constant M>0 such that |xₖ|≤ yₖ for all
sufficiently large k, yₖ→ 0, and for all sufficiently large k,
y_{k+1}≤ M yₖ^2,
determine whether {xₖ} converges to 0 R-quadratically.
-/
