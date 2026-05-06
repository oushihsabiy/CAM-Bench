theorem linearizedConstraint_at_origin_is_false
    (p : Fin 2 → ℝ) :
    linearizedEqualityConstraint
      (fun x : Fin 2 → ℝ => fun _ : Fin 1 => x 0 ^ 2 + x 1 ^ 2 - 1)
      (0 : (Fin 2 → ℝ) → (Fin 2 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
      0
      p ↔
      (-1 : ℝ) = 0 := by
  sorry

/- [BLOCK Exercise 18.5 | 25 | thm]
Let c:ℝ^2 → ℝ be defined by c(x)=x₁^2+x₂^2-1 for x=(x₁,x₂)ᵀ ∈ ℝ^2. For a given point xₖ ∈ ℝ^2,
define cₖ=c(xₖ) and Aₖ=∇ c(xₖ)ᵀ. The linearized equality constraint is Aₖ p + cₖ = 0 for p=(p₁,p₂)ᵀ
∈ ℝ^2. Prove that at xₖ=(0,1)ᵀ, the linearized constraint is 2p_2=0.
-/
