def quadraticPenaltyFunction
    {α : Type*} (f c : α → ℝ) (μ : ℝ) (hμ : 0 < μ := by sorry) : α → ℝ :=
  fun x => f x + (μ / 2) * (c x)^2

/- [BLOCK Exercise 17.1-(a) | 2 | defn]
An optimization problem is equality-constrained if its feasible set is of the form
{x∈ℝ^n : hᵢ(x)=0 for i=1,dots,m},
for given constraint functions hᵢ.
-/
