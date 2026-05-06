theorem gradient_and_hessian_of_lagrangian_combination
    (n m : ℕ)
    (f : (Fin n → ℝ) → ℝ)
    (c : Fin m → ((Fin n → ℝ) → ℝ))
    (lam : Fin m → ℝ)
    (x xk : Fin n → ℝ)
    (hf : TwiceContinuouslyDifferentiable n f)
    (hc : ∀ i, TwiceContinuouslyDifferentiable n (c i)) :
    let Fk : (Fin n → ℝ) → ℝ := fun y => f y - ∑ i, lam i * c i y
    (gradient n Fk x = fun j => gradient n f x j - ∑ i, lam i * gradient n (c i) x j) ∧
    (hessian n Fk x = fun a b => hessian n f x a b - ∑ i, lam i * hessian n (c i) x a b) ∧
    (gradient n Fk xk = fun j => gradient n f xk j - ∑ i, lam i * gradient n (c i) xk j) ∧
    (hessian n Fk xk = fun a b => hessian n f xk a b - ∑ i, lam i * hessian n (c i) xk a b) := by
  sorry

/- [BLOCK Exercise 17.10 | 18 | thm]
Let f:ℝ^n → ℝ and, for each i=1,dots,m, let bar cᵢ^k:ℝ^n→ℝ be twice continuously differentiable. Let
λ_i^k∈ℝ for i=1,dots,m, let μ∈ℝ, and let xₖ∈ℝ^n. Prove also that if
Fₖ(x)=f(x)-sum_{i=1}^m λ_i^kbar cᵢ^k(x)+(μ)/(2)sum_{i=1}^m (bar cᵢ^k(x))^2,
then
∇ Fₖ(x)=∇ f(x)-sum_{i=1}^m λ_i^k∇ bar cᵢ^k(x)+μsum_{i=1}^m bar cᵢ^k(x)∇ bar cᵢ^k(x)
and
∇^2 Fₖ(x)=∇^2 f(x)-sum_{i=1}^m λ_i^k∇^2 bar cᵢ^k(x)+μsum_{i=1}^m ≤ft(∇ bar cᵢ^k(x)∇ bar cᵢ^k(x)ᵀ+bar
cᵢ^k(x)∇^2 bar cᵢ^k(x)).
Moreover,
∇ Fₖ(xₖ)=∇ f(xₖ)-sum_{i=1}^m λ_i^k∇ bar cᵢ^k(xₖ)+μsum_{i=1}^m bar cᵢ^k(xₖ)∇ bar cᵢ^k(xₖ)
and
∇^2 Fₖ(xₖ)=∇^2 f(xₖ)-sum_{i=1}^m λ_i^k∇^2 bar cᵢ^k(xₖ)+μsum_{i=1}^m ≤ft(∇ bar cᵢ^k(xₖ)∇ bar
cᵢ^k(xₖ)ᵀ+bar cᵢ^k(xₖ)∇^2 bar cᵢ^k(xₖ)).
-/
