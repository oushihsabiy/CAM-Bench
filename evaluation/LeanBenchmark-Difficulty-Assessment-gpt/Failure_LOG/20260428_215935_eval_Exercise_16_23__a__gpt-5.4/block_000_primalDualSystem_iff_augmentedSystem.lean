theorem primalDualSystem_iff_augmentedSystem
    {n m : ℕ}
    (hm : 1 ≤ m)
    (G : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ)
    (b : Fin m → ℝ)
    (x : Fin n → ℝ)
    (y : Fin m → ℝ)
    (lam : Fin m → ℝ)
    (σ : ℝ)
    (hy : ∀ i : Fin m, y i ≠ 0)
    (hlam : ∀ i : Fin m, lam i ≠ 0)
    (Δx : Fin n → ℝ)
    (Δy Δlam : Fin m → ℝ) :
    let Y : Matrix (Fin m) (Fin m) ℝ := Matrix.diagonal y
    let Lambda : Matrix (Fin m) (Fin m) ℝ := Matrix.diagonal lam
    let μ : ℝ := (∑ i : Fin m, y i * lam i) / (m : ℝ)
    let r_d : Fin n → ℝ := fun i => (G.mulVec x) i - (A.transpose.mulVec lam) i + c i
    let r_p : Fin m → ℝ := fun i => (A.mulVec x) i - y i - b i
    ((primalDualSystem G A Lambda Y r_d r_p σ μ).1.mulVec
        (Fin.append (Fin.append Δx Δy) Δlam) =
      (primalDualSystem G A Lambda Y r_d r_p σ μ).2) ↔
    (((augmentedSystem G A Lambda Y r_d r_p y σ μ).1.mulVec (Sum.elim Δx Δlam) =
        (augmentedSystem G A Lambda Y r_d r_p y σ μ).2) ∧
      (Δy = fun i => (A.mulVec Δx) i + r_p i)) := by
  sorry

/- [BLOCK Exercise 16.23-(a) | 29 | thm]
Let G ∈ ℝ^{n×n}, A ∈ ℝ^{m × n}, c ∈ ℝ^n, b ∈ ℝ^m, x ∈ ℝ^n, y ∈ ℝ^m, λ ∈ ℝ^m, and σ ∈ ℝ. Let e ∈ ℝ^m
be the vector of all ones, assume m ≥ 1, and assume every component of y and λ is nonzero. Define
Y=diag(y₁,dots,yₘ), λ=diag(λ_1,dots,λ_m), μ=(yᵀλ)/(m), and r_d=Gx-Aᵀλ+c, r_p=Ax-y-b. Also prove that
if (δ x,δ λ) satisfies [ G & -Aᵀ ; A & λ^{-1}Y ] [ δ x ; δ λ ] = [ -r_d ; -r_{p-y}+σμLambda^{-1}e ],
then δ x satisfies (G+Aᵀ Y^{-1}λ A)δ x = -r_d+Aᵀ Y^{-1}λ(-r_{p-y}+σμLambda^{-1}e), and, conversely,
if δ x satisfies this normal equation, then δ λ and δ y are given by δ λ =
Y^{-1}λ(-r_{p-y}+σμLambda^{-1}e-ADelta x) and δ y=ADelta x+r_p, so that (δ x,δ y,δ λ) satisfies the
primal-dual system.
-/
