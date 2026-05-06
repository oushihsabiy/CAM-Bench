def centeredFiniteDifferenceGradient {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε := by sorry) : Fin n → ℝ :=
  fun i =>
    (f (x + fun j => if j = i then ε else 0) - f (x - fun j => if j = i then ε else 0)) / (2 * ε)

/- [BLOCK Exercise UNKNOWN | 43 | thm]
Let f,h : ℝ^n → ℝ, let x ∈ ℝ^n, and let ε > 0. For v=(v₁,dots,vₙ) ∈ ℝ^n, define
‖v‖_{∞} := max_{1 ≤ i ≤ n} |vᵢ|.
Let e₁,dots,eₙ denote the standard basis vectors of ℝ^n. Define the finite-difference ∇approximation
by
∇_{ε} f(x)
:= ≤ft((f(x+ε eᵢ)-f(x-ε eᵢ))/(2ε))_{i=1}^n,
and define the error term
eta(x;ε)
:= max_{1 ≤ i ≤ n} ≤ft| f(x+ε eᵢ)-h(x+ε eᵢ) |
+ max_{1 ≤ i ≤ n} ≤ft| f(x-ε eᵢ)-h(x-ε eᵢ) |.
Assume that h is differentiable on a neighborhood of the box
{ z ∈ ℝ^n | ‖z-x‖_{∞} ≤ ε },
and that ∇ h is Lipschitz continuous there with Lipschitz constant L_h ≥ 0, i.e.
‖∇ h(u)-∇ h(v)‖_{∞} ≤ L_h ‖u-v‖_{∞}
quad for all u,v in that neighborhood.
Then
‖∇_{ε} f(x)-∇ h(x)‖_{∞} ≤ L_h ε^2 + (eta(x;ε))/(ε).
9.5
-/
