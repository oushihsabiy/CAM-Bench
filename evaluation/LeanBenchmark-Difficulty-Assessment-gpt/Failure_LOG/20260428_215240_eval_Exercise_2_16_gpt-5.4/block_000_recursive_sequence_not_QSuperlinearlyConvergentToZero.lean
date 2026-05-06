theorem recursive_sequence_not_QSuperlinearlyConvergentToZero :
    ¬ QSuperlinearlyConvergentToZero
      (fun k : ℕ =>
        if Even k then
          (1 / 4 : ℝ) ^ (2 ^ k)
        else
          (1 / (k : ℝ)) * (1 / 4 : ℝ) ^ (2 ^ (k - 1))) := by
  sorry

/-
Exercise 2.16 | 14 | thm

Let (xₖ)_{k ≥ 0} ⊂ ℝ be defined by

xₖ = {
(1/4)^{2^k}, if k is even,
x_{k-1}/k, if k is odd.
}

Using the following definition for a sequence (xₖ) ⊂ ℝ converging to 0: (xₖ) is Q-quadratically
convergent to 0 if there exists M > 0 such that for all sufficiently large k,

|xₖ₊₁| ≤ M|xₖ|²,

determine whether (xₖ) converges to 0 Q-quadratically.
-/
