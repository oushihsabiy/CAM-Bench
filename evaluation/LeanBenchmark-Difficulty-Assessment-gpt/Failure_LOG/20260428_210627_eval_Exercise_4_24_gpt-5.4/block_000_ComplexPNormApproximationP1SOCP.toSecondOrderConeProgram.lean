def ComplexPNormApproximationP1SOCP.toSecondOrderConeProgram
    (Q : ComplexPNormApproximationP1SOCP) : SecondOrderConeProgram := by
  exact {
    m := 0
    n := Q.n
    k := 0
    obj := Q.objectiveSource
    affineRows := 0
    affineMat := fun _ _ => 0
    affineVec := fun _ => 0
    coneMat := fun _ _ => 0
    coneVec := fun _ => 0
    coneLin := fun _ => 0
    coneConst := fun _ => 0
  }

instance : Coe ComplexPNormApproximationP1SOCP SecondOrderConeProgram where
  coe Q := Q.toSecondOrderConeProgram