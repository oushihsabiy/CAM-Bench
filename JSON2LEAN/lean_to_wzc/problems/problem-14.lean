import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-14»
open scoped RealInnerProductSpace

def dualCone {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  { z | ∀ ⦃x⦄, x ∈ K → 0 ≤ ⟪z, x⟫ }

def Kpol (k : ℕ) : Set (EuclideanSpace ℝ (Fin (2 * k + 1))) :=
  { x |
    ∀ t : ℝ,
      0 ≤
        (∑ i : Fin (2 * k + 1), (x i) * (t ^ (i.1 : ℕ))) }

def hankelMatrix (k : ℕ) (z : EuclideanSpace ℝ (Fin (2 * k + 1))) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  fun i j => z ⟨i.1 + j.1, by
    have hi : i.1 < k + 1 := i.2
    have hj : j.1 < k + 1 := j.2
    have hsum : i.1 + j.1 ≤ 2 * k := by
      have hi' : i.1 ≤ k := Nat.le_of_lt_succ hi
      have hj' : j.1 ≤ k := Nat.le_of_lt_succ hj
      calc
        i.1 + j.1 ≤ k + k := Nat.add_le_add hi' hj'
        _ = 2 * k := by omega
    exact Nat.lt_of_le_of_lt hsum (Nat.lt_succ_self (2 * k))⟩

def Khan (k : ℕ) : Set (EuclideanSpace ℝ (Fin (2 * k + 1))) :=
  { z | Matrix.PosSemidef (hankelMatrix k z) }

/- - The dual of the nonnegative polynomial cone is the Hankel positive semidefinite cone. -/
theorem dualCone_Kpol_eq_Khan (k: ℕ): dualCone (Kpol k) = Khan k := by
  sorry
end «problem-14»