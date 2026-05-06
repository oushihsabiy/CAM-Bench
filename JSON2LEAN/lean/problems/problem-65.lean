import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-65»
/- [BLOCK Exercise 2.30 | 45 | defn]
For functions f,g: ℝ^n → ℝ+∞, their infimal convolution is the function (fsquare g):ℝ^n→ℝ+∞
defined by
(fsquare g)(x)=∈f_y∈ℝ^n(f(y)+g(x-y))
for all x∈ℝ^n.
-/
def infimalConvolution {n : ℕ} (f g : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun x => sInf {r : EReal | ∃ y : Fin n → ℝ, r = f y + g (x - y)}

/- [BLOCK Exercise 2.30 | 46 | defn]
The Huber penalty is the separable function h:ℝ^n→ℝ given by
h(x)=sum_i=1^n φ(xᵢ),
where
φ(u)=casesu^2{2}, & |u|≤ 1,; |u|-1{2}, & |u|>1.cases
-/
def huberScalar {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, if |x i| ≤ 1 then (x i) ^ 2 / 2 else |x i| - 1 / 2

def huberPenalty {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, if |x i| ≤ 1 then (x i) ^ 2 / 2 else |x i| - 1 / 2

/- [BLOCK Exercise 2.30 | 47 | thm]
Let n ∈ ℕ. For functions f,g:ℝ^n → ℝ, define their infimal convolution by
(f square g)(x)=∈f_{y ∈ ℝ^n}(f(y)+g(x-y)), x ∈ ℝ^n.
For x=(x₁,dots,xₙ) ∈ ℝ^n, let
‖x‖_1=sum_{i=1}^n |xᵢ|, ‖x‖_2=(sum_{i=1}^n xᵢ^2)^{1/2}.
Consider
f(x)=‖x‖_1, g(x)=(1)/(2)‖x‖_2^2,
and define
h(x)=(f square g)(x)=∈f_{y ∈ ℝ^n}(‖y‖_1+(1)/(2)‖x-y‖_2^2).
Show that h is the Huber penalty, that is,
h(x)=sum_{i=1}^n φ(xᵢ),
where φ:ℝ→ℝ is given by
φ(u)=
cases
(u^2)/(2), & |u|≤q 1,;
|u|-(1)/(2), & |u|>1.
cases
-/
theorem infimalConvolution_l1_sqNorm_eq_huberPenalty (n : ℕ) :
    infimalConvolution
        (fun x : Fin n → ℝ => ((∑ i, |x i| : ℝ) : EReal))
        (fun x : Fin n → ℝ => ((1 / 2 : ℝ) * ∑ i, (x i) ^ 2 : ℝ))
      =
      fun x : Fin n → ℝ => (huberPenalty x : EReal) := by
  sorry
end «problem-65»
