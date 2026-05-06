theorem linearizedConstraint_at_point_0_1_0_02
    (p : Fin 2 → ℝ) :
    linearizedEqualityConstraint
      (fun x : Fin 2 → ℝ => fun _ : Fin 1 => x 0 ^ 2 + x 1 ^ 2 - (1 : ℝ))
      (fun x => circleConstraintLinearMap x)
      (fun i => if i = 0 then (0.1 : ℝ) else (0.02 : ℝ))
      p
    ↔ (0.2 : ℝ) * p 0 + (0.04 : ℝ) * p 1 - 0.9896 = 0 := by
  sorry

/- [BLOCK Exercise 18.5 | 27 | thm]
Let c:ℝ^2 → ℝ be defined by c(x)=x₁^2+x₂^2-1 for x=(x₁,x₂)ᵀ ∈ ℝ^2. For a given point xₖ ∈ ℝ^2,
define cₖ=c(xₖ) and Aₖ=∇ c(xₖ)ᵀ. The linearized equality constraint is Aₖ p + cₖ = 0 for p=(p₁,p₂)ᵀ
∈ ℝ^2. Prove that at xₖ=-(0.1,0.02)ᵀ=(-0.1,-0.02)ᵀ, the linearized constraint is
-0.2p_1-0.04p_2-0.9896=0.
-/
