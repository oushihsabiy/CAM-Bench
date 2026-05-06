theorem scalar_nonlinear_program_primal_dual_newton_system
    (x s1 s2 z1 z2 μ px ps1 ps2 pz1 pz2 : ℝ)
    (hμ : 0 ≤ μ) :
    primalDualNewtonSystem
      (fun xfun zfun _ =>
        1 - 2 * (xfun ()) * (zfun false) - (zfun true))
      (fun xfun =>
        fun b => cond b (xfun () ^ 2 - s1 - 1) (xfun () - s2 - (1 / 2 : ℝ)))
      (fun _ zfun =>
        fun b => cond b (s1 * zfun false - μ) (s2 * zfun true - μ))
      (fun xfun zfun step =>
        let px' := step.1 ()
        let ps' := step.2.1
        let pz' := step.2.2
        (fun _ => (-2 * zfun false) * px' + (-2 * xfun ()) * pz' false + (-1) * pz' true,
         fun b => cond b (zfun false * ps' false + s1 * pz' false) (zfun true * ps' true + s2 * pz' true),
         fun b => cond b (2 * xfun () * px' - ps' false) (px' - ps' true)))
      (fun _ => x)
      (fun b => cond b z1 z2)
      ((fun _ => px), (fun b => cond b ps1 ps2), (fun b => cond b pz1 pz2)) ↔
    ((-2 * z1) * px + 0 * ps1 + 0 * ps2 + (-2 * x) * pz1 + (-1) * pz2 =
        -(1 - 2 * x * z1 - z2)) ∧
    (0 * px + z1 * ps1 + 0 * ps2 + s1 * pz1 + 0 * pz2 =
        -(s1 * z1 - μ)) ∧
    (0 * px + 0 * ps1 + z2 * ps2 + 0 * pz1 + s2 * pz2 =
        -(s2 * z2 - μ)) ∧
    (2 * x * px + (-1) * ps1 + 0 * ps2 + 0 * pz1 + 0 * pz2 =
        -(x ^ 2 - s1 - 1)) ∧
    (1 * px + 0 * ps1 + (-1) * ps2 + 0 * pz1 + 0 * pz2 =
        -(x - s2 - (1 / 2 : ℝ))) := by
  sorry

/- [BLOCK Exercise 19.11-(a) | 28 | thm]
Consider the scalar nonlinear program
aligned
min quad & f(x)=x ;
subject to quad & x^2-s_{1-1}=0,;
& x-s_{2-frac12}=0,;
& s₁≥ 0,quad s₂≥ 0,
aligned
where x∈ℝ and s=(s₁,s₂)ᵀ∈ ℝ^2. There are no equality constraints. Let
c_I(x)=[x^2-1; x-frac12],
A_I(x)=∇ c_I(x)ᵀ=[2x; 1],
z=[z₁; z₂],
with
S=diag(s₁,s₂),
Z=diag(z₁,z₂),
e=(1,1)ᵀ,
and let μ≥ 0. The Lagrangian is
L(x,z)=x-z₁(x^2-1)-z₂≤ft(x-frac12),
so that
∇ f(x)=1,
∇_{xx}^2L(x,z)=-2z_1.
Prove moreover that for every x∈ℝ, at every iterate with s₁=s₂=0 and arbitrary z₁,z₂, the
coefficient matrix
[
-2z_1 & 0 & 0 & -2x & -1 ;
0 & z₁ & 0 & s₁ & 0 ;
0 & 0 & z₂ & 0 & s₂ ;
2x & -1 & 0 & 0 & 0 ;
1 & 0 & -1 & 0 & 0
]
is singular.
-/
