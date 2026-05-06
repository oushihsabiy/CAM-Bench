def penaltyFunction (f P : α → ℝ) (ρ : ℝ) (feasible : α → Prop := fun _ => True)
    (_hρ : 0 < ρ := by sorry) (_hP_nonneg : ∀ x, 0 ≤ P x := by sorry)
    (_hP_feasible : ∀ x, feasible x → P x = 0 := by
      intro x hx
      rfl) :
    α → ℝ :=
  fun x => f x + ρ * P x

/- [BLOCK Exercise 5.4-(c) | 2 | defn]
A penalty function approximation is an unconstrained optimization problem obtained by replacing a
constrained problem with the minimization of a penalty function that includes a term measuring
constraint violation, typically depending on a penalty parameter.
-/
structure PenaltyFunctionApproximation (α : Type*) where
  objective : α → ℝ
  isUnconstrained : Prop := True
  baseObjective : α → ℝ
  penaltyTerm : α → ℝ
  penaltyParameter : ℝ
  feasible : α → Prop
  penaltyParameter_pos : 0 < penaltyParameter
  penaltyTerm_nonneg : ∀ x, 0 ≤ penaltyTerm x
  penaltyTerm_feasible : ∀ x, feasible x → penaltyTerm x = 0
  objective_eq_penaltyFunction :
    objective =
      penaltyFunction baseObjective penaltyTerm penaltyParameter feasible
        penaltyParameter_pos penaltyTerm_nonneg penaltyTerm_feasible

instance : CoeFun (PenaltyFunctionApproximation α) (fun _ => α → ℝ) where
  coe p := p.objective


/- [BLOCK Exercise 5.4-(c) | 3 | opt_prob]
The penalty function approximation problem in part (c) is
min_{x ∈ ℝ^n} sum_{i=1}^r |Ax-b|_{[i]}.
-/
structure TrimmedAbsoluteResidualMinimization where
  n : ℕ
  m : ℕ
  r : ℕ
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  h_r_le_m : r ≤ m
  objective : (Fin n → ℝ) → ℝ
  objective_eq :
    objective =
      fun x =>
        (((List.ofFn fun i : Fin m => |(A.mulVec x) i - b i|).mergeSort (· ≥ ·)).take r).sum