import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-77»

-- Chp_6_Ex_6__a_

/- [BLOCK Chp.6 Ex.6-(a) | 14 | defn]
A point x* ∈ ℝ is called a multiple root of the equation f(x)=0 if there exist an integer m ≥ 2 and
a function g, continuous in a neighborhood of x*, such that g(x*) ≠ 0 and
f(x)=(x-x*)^m g(x)
in a neighborhood of x*; the integer m is called the multiplicity.
-/
def IsMultipleRoot (f : ℝ → ℝ) (xStar : ℝ) : Prop :=
  ∃ m : ℕ, 2 ≤ m ∧
    ∃ g : ℝ → ℝ,
      ContinuousAt g xStar ∧ g xStar ≠ 0 ∧
        ∃ s : Set ℝ,
          s ∈ 𝓝 xStar ∧
            ∀ x ∈ s, f x = (x - xStar) ^ m * g x

def multiplicityAt (f : ℝ → ℝ) (xStar : ℝ) (m : ℕ) : Prop :=
  2 ≤ m ∧
    ∃ g : ℝ → ℝ,
      ContinuousAt g xStar ∧ g xStar ≠ 0 ∧
        ∃ s : Set ℝ,
          s ∈ 𝓝 xStar ∧
            ∀ x ∈ s, f x = (x - xStar) ^ m * g x

/- [BLOCK Chp.6 Ex.6-(a) | 15 | defn]
For a differentiable real-valued function f, the Newton iteration for solving f(x)=0 is
x^{k+1}=x^k-(f(x^k))/(f'(x^k)),
whenever f'(x^k) ≠ 0.
-/
def NewtonIterate (f f' : ℝ → ℝ) (x : ℝ) : ℝ :=
  if _h : f' x ≠ 0 then x - f x / f' x else x

def IsNewtonIteration (f f' : ℝ → ℝ) (xSeq : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, ∀ _h : f' (xSeq k) ≠ 0,
    xSeq (k + 1) = NewtonIterate f f' (xSeq k)

/- [BLOCK Chp.6 Ex.6-(a) | 16 | defn]
A sequence {x^k} converges Q-linearly to x* if there exist a constant q∈(0,1) and an index k₀ such
that
‖x^{k+1}-x*‖≤ q‖x^k-x*‖ quad for all k≥ k₀.
-/
def IsQLinearlyConvergentTo (xSeq : ℕ → ℝ) (xStar : ℝ) : Prop :=
  ∃ q : ℝ, 0 < q ∧ q < 1 ∧
    ∃ k0 : ℕ,
      ∀ k : ℕ, k0 ≤ k →
        |xSeq (k + 1) - xStar| ≤ q * |xSeq k - xStar|

/- [BLOCK Chp.6 Ex.6-(a) | 17 | algo]
Apply the classical Newton iteration to the equation f(x)=0:
x^{k+1}=x^k-(f(x^k))/(f'(x^k)), k=0,1,2,dots,
and assume that the initial point x^0 is sufficiently close to 0 so that the iteration is well
defined and the generated sequence {x^k} converges to 0.
-/
structure ClassicalNewtonIteration where
  f : ℝ → ℝ
  f' : ℝ → ℝ
  xSeq : ℕ → ℝ
  x0_near_zero : ∃ r : ℝ, 0 < r ∧ |xSeq 0| < r
  wellDefined : ∀ k : ℕ, f' (xSeq k) ≠ 0
  isNewtonIteration : IsNewtonIteration f f' xSeq
  convergesToZero : Tendsto xSeq atTop (𝓝 0)

def ClassicalNewtonIteration.step (N : ClassicalNewtonIteration) (x : ℝ) : ℝ :=
  NewtonIterate N.f N.f' x

def ClassicalNewtonIteration.initialPoint (N : ClassicalNewtonIteration) : ℝ :=
  N.xSeq 0

def ClassicalNewtonIteration.satisfies_recursion (N : ClassicalNewtonIteration) (k : ℕ) :
    N.xSeq (k + 1) = NewtonIterate N.f N.f' (N.xSeq k) :=
  N.isNewtonIteration k (N.wellDefined k)

/- [BLOCK Chp.6 Ex.6-(a) | 18 | thm]
Let the function f:ℝ → ℝ be continuously differentiable in a neighborhood of 0, and suppose that 0
is a multiple root of the equation f(x)=0. That is, there exist an integer m ≥ 2 and a function g
continuous in a neighborhood of 0 such that f(x)=x^m g(x), g(0) ≠ 0. Apply the classical Newton
iteration to the equation f(x)=0: x^{k+1}=x^k-(f(x^k))/(f'(x^k)), k=0,1,2,dots, and assume that the
initial value x^0 is sufficiently close to 0 so that the iteration is well defined and the generated
sequence {x^k} converges to 0. Prove that the convergence of {x^k} to 0 is Q-linear.
-/
theorem classicalNewtonIteration_multipleRoot_qLinear
    (N : ClassicalNewtonIteration)
    (hroot : IsMultipleRoot N.f 0)
    (hf'_correct : ∀ x : ℝ, N.f' x = deriv N.f x)
    (hC1 : ∃ s : Set ℝ, s ∈ 𝓝 0 ∧ ContDiffOn ℝ 1 N.f s) :
    IsQLinearlyConvergentTo N.xSeq 0 := by
  sorry

end «problem-77»
