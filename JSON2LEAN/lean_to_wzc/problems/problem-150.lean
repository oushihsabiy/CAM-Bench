import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-150»

/- [BLOCK Exercise 17.7 | 5 | defn]
For inequality constraint functions cᵢ, the active set at a feasible point x is A(x)={i : cᵢ(x)=0},
that is, the set of indices of inequality constraints that are satisfied with equality.
-/
def activeSet {ι : Type*} {X : Type*} (c : ι → X → ℝ) (x : X) : Set ι :=
  {i | c i x = 0}

/- [BLOCK Exercise 17.7 | 6 | defn]
An equality constraint is a constraint of the form cᵢ(x)=0.
-/
def IsEqualityConstraint {X : Type*} (c : X → ℝ) : X → Prop :=
  fun x => c x = 0

/- [BLOCK Exercise 17.7 | 7 | defn]
An inequality constraint is a constraint of the form cᵢ(x)≥ 0, or equivalently -cᵢ(x)≤ 0, depending
on the sign convention.
-/
def IsInequalityConstraint {X : Type*} (c : X → ℝ) : X → Prop :=
  fun x => 0 ≤ c x

/- [BLOCK Exercise 17.7 | 8 | defn]
A point x is feasible for a family of constraints if it satisfies all equality constraints and all
inequality constraints.
-/
def IsFeasiblePoint {ι : Type*} {X : Type*} (eqs ineqs : ι → X → ℝ) (x : X) : Prop :=
  (∀ i : ι, eqs i x = 0) ∧ (∀ i : ι, 0 ≤ ineqs i x)

/- [BLOCK Exercise 17.7 | 9 | thm]
Let f:ℝ^n → ℝ and cᵢ:ℝ^n → ℝ for i ∈ EcupI be continuously differentiable, where E and I index the
equality and inequality constraints. For μ ≥ 0, define φ_1(x;μ)=f(x)+μsum_{i∈E} |cᵢ(x)|+μsum_{i∈I}
[cᵢ(x)]^-, where [t]^-=0,-t. Let x∈ℝ^n satisfy cᵢ(x)=0 quad for all i∈E, cᵢ(x)≥ 0 quad for all i∈I,
and define the active set A(x)={i∈I: cᵢ(x)=0}. For p∈ℝ^n, let D(φ_1(x;μ);p)=lim_{α→ 0^+}frac{φ_1(x+α
p;μ)-φ_1(x;μ)}{α}, provided the limit exists. Verify that
D(φ_1(x;μ);p)=
∇ f(x)ᵀ p
+μ sum_{i∈E} ≤ft|∇ cᵢ(x)ᵀ p|
+μ sum_{i∈Icap A(x)} ≤ft[∇ cᵢ(x)ᵀ p]^-.
17.28
-/
open scoped BigOperators

theorem phi1_directionalDerivative_formula
    {n : ℕ} {ιE ιI : Type*}
    [Fintype ιE] [Fintype ιI]
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (cE : ιE → EuclideanSpace ℝ (Fin n) → ℝ)
    (cI : ιI → EuclideanSpace ℝ (Fin n) → ℝ)
    (xhat p : EuclideanSpace ℝ (Fin n))
    [DecidablePred fun i : ιI => i ∈ activeSet cI xhat]
    (μ : ℝ)
    (hfd : DifferentiableAt ℝ f xhat)
    (hcE : ∀ i : ιE, DifferentiableAt ℝ (cE i) xhat)
    (hcI : ∀ i : ιI, DifferentiableAt ℝ (cI i) xhat)
    (hμ : 0 ≤ μ)
    (hEq : ∀ i : ιE, cE i xhat = 0)
    (hIneq : ∀ i : ιI, 0 ≤ cI i xhat) :
    Tendsto
      (fun α : ℝ =>
        ((f (xhat + α • p)
            + μ * (∑ i : ιE, |cE i (xhat + α • p)|)
            + μ * (∑ i : ιI, max 0 (-cI i (xhat + α • p))))
          - (f xhat
            + μ * (∑ i : ιE, |cE i xhat|)
            + μ * (∑ i : ιI, max 0 (-cI i xhat)))) / α)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 ((fderiv ℝ f xhat) p
        + μ * (∑ i : ιE, |(fderiv ℝ (cE i) xhat) p|)
        + μ * (∑ i ∈ Finset.univ.filter (fun i : ιI => i ∈ activeSet cI xhat),
            max 0 (-(fderiv ℝ (cI i) xhat) p)))) := by
  sorry

end «problem-150»