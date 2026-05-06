import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-193»

/- [BLOCK Exercise 7.2 | 2 | defn]
Given a parametric family of densities or mass functions {p_θ} for observed data y, a parameter
value hatθ is a maximum-likelihood estimate if hatθ ∈ operatorname*{argmax}_{θ} p_θ(y);
equivalently, hatθ maximizes the log-likelihood log p_θ(y) over all feasible θ.
-/
def IsMaximumLikelihoodEstimate {Θ Y : Type _} (p : Θ → Y → ℝ) (feasible : Set Θ) (y : Y)
    (θhat : Θ) : Prop :=
  θhat ∈ feasible ∧ ∀ θ, θ ∈ feasible → p θ y ≤ p θhat y

/- [BLOCK Exercise 7.2 | 3 | thm]
Consider the linear measurement model y = Ax + v, where A is known, x is an unknown vector, y is
observed, and the components of v are independent and identically distributed with density
p(z)=
cases
1{2α}, & |z| ≤ α,;
0, & |z| > α,
cases
where α > 0 is unknown. Let ‖u‖_{∞} = max_i |uᵢ| for a vector u. Show that a pair (hat x, hat α) is
a maximum-likelihood estimate if and only if hat x minimizes ‖Ax-y‖_{∞} and hat α = ‖Ahat x-y‖_{∞}.
-/
open scoped BigOperators

theorem mle_uniform_noise_iff_minimizes_infNorm_residual
    {m n : ℕ} (hm : 0 < m) (A : Matrix (Fin m) (Fin n) ℝ) (y : Fin m → ℝ)
    (hres_pos :
      ∀ x : Fin n → ℝ,
        0 < sSup (Set.range fun i : Fin m => |∑ j : Fin n, A i j * x j - y i|))
    (xalpha_hat : (Fin n → ℝ) × ℝ) :
    IsMaximumLikelihoodEstimate
        (fun xa : (Fin n → ℝ) × ℝ => fun y' : Fin m → ℝ =>
          if hfeas : 0 < xa.2 ∧
              ∀ i : Fin m, |y' i - ∑ j : Fin n, A i j * xa.1 j| ≤ xa.2 then
            if hzero : xa.2 = 0 then
              if (sSup (Set.range fun i : Fin m => |y' i - ∑ j : Fin n, A i j * xa.1 j|)) = 0
              then 1 else 0
            else
              (1 / (2 * xa.2)) ^ m
          else 0)
        {xa : (Fin n → ℝ) × ℝ | 0 < xa.2}
        y
        xalpha_hat
        ↔
        ((∀ x : Fin n → ℝ,
            sSup (Set.range fun i : Fin m => |∑ j : Fin n, A i j * xalpha_hat.1 j - y i|) ≤
              sSup (Set.range fun i : Fin m => |∑ j : Fin n, A i j * x j - y i|)) ∧
          xalpha_hat.2 =
            sSup (Set.range fun i : Fin m => |∑ j : Fin n, A i j * xalpha_hat.1 j - y i|)) := by
  sorry


end «problem-193»
