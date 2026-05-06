theorem optimality_conditions_for_equivalent_geometric_convex_program
    (P : EquivalentGeometricConvexProgram)
    (hApos : ∀ i j : Fin P.n, 0 < P.A i j)
    (hcpos : ∀ i : Fin P.n, 0 < P.c i)
    (hdpos : ∀ j : Fin P.n, 0 < P.d j)
    (hcsum : ∑ i : Fin P.n, P.c i = 1)
    (hdsum : ∑ j : Fin P.n, P.d j = 1)
    (u v : Fin P.n → ℝ)
    (hopt_convex :
      P.convexFeasible (u, v) ∧
      ∀ u' v' : Fin P.n → ℝ,
        P.convexFeasible (u', v') →
          Real.log (∑ i : Fin P.n, ∑ j : Fin P.n, P.A i j * Real.exp (u i + v j)) ≤
            Real.log (∑ i : Fin P.n, ∑ j : Fin P.n, P.A i j * Real.exp (u' i + v' j)))
    (hopt_geometric :
      let x := P.xOfU u
      let y := P.yOfV v
      P.geometricFeasible (x, y) ∧
      ∀ x' y' : Fin P.n → ℝ,
        P.geometricFeasible (x', y') → P.geometricObjective x y ≤ P.geometricObjective x' y') :
    let x := P.xOfU u
    let y := P.yOfV v
    let B : Fin P.n → Fin P.n → ℝ := fun i j => (x i * P.A i j * y j) / P.geometricObjective x y
    (∀ i : Fin P.n,
      x i * (∑ j : Fin P.n, P.A i j * y j) / P.geometricObjective x y = P.c i) ∧
    (∀ j : Fin P.n,
      y j * (∑ i : Fin P.n, P.A i j * x i) / P.geometricObjective x y = P.d j) ∧
    (∀ i : Fin P.n, ∑ j : Fin P.n, B i j = P.c i) ∧
    (∀ j : Fin P.n, ∑ i : Fin P.n, B i j = P.d j) := by
  sorry
