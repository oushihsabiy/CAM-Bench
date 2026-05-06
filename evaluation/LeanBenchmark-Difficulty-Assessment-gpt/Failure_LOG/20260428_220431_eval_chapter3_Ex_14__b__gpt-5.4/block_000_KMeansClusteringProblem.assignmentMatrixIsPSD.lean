theorem KMeansClusteringProblem.assignmentMatrixIsPSD {n m k : ℕ}
    (P : KMeansClusteringProblem n m k) :
    Matrix.PosSemidef P.assignmentMatrix := by
  sorry
