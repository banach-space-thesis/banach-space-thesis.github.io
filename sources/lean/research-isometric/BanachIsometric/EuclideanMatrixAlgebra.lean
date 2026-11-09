import BanachIsometric.BodyComponentTransport

/-!
# The actual Euclidean operator algebra in ordinary matrix coordinates

The coordinate maps already proved continuous linear are inverse star-algebra
equivalences. Their unitary groups are therefore identified with the actual
orthogonal matrix group. Both directions have explicit Lipschitz bounds from
the continuous linear coordinate maps; no equality of the two norms is used.
-/

namespace BanachIsometric

open Set
open scoped Topology NNReal Matrix.Norms.Operator

noncomputable section

variable {m : ℕ}

theorem matrixEuclideanOperator_one (m : ℕ) :
    matrixEuclideanOperator m (1 : Matrix (Fin m) (Fin m) ℝ) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [matrixEuclideanOperator_apply, Matrix.one_mulVec, ContinuousLinearEquiv.symm_apply_apply]
  rfl

theorem matrixEuclideanOperator_mul (M N : Matrix (Fin m) (Fin m) ℝ) :
    matrixEuclideanOperator m (M * N) = matrixEuclideanOperator m M * matrixEuclideanOperator m N := by
  have hinj : Function.Injective (euclideanOperatorMatrix m) := by
    intro T U h
    calc
      T = matrixEuclideanOperator m (euclideanOperatorMatrix m T) :=
        (matrixEuclideanOperator_euclideanOperatorMatrix T).symm
      _ = matrixEuclideanOperator m (euclideanOperatorMatrix m U) := congrArg _ h
      _ = U := matrixEuclideanOperator_euclideanOperatorMatrix U
  apply hinj
  rw [euclideanOperatorMatrix_matrixEuclideanOperator, euclideanOperatorMatrix_mul,
    euclideanOperatorMatrix_matrixEuclideanOperator, euclideanOperatorMatrix_matrixEuclideanOperator]

theorem matrixEuclideanOperator_star (M : Matrix (Fin m) (Fin m) ℝ) :
    matrixEuclideanOperator m (star M) = star (matrixEuclideanOperator m M) := by
  change (Matrix.toEuclideanLin M.conjTranspose).toContinuousLinearMap =
    (Matrix.toEuclideanLin M).toContinuousLinearMap.adjoint
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact LinearMap.adjoint_toContinuousLinearMap _

def euclideanMatrixStarAlgEquiv (m : ℕ) : Matrix (Fin m) (Fin m) ℝ ≃⋆ₐ[ℝ]
    (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) where
  toFun := matrixEuclideanOperator m
  invFun := euclideanOperatorMatrix m
  left_inv := euclideanOperatorMatrix_matrixEuclideanOperator
  right_inv := matrixEuclideanOperator_euclideanOperatorMatrix
  map_mul' := matrixEuclideanOperator_mul
  map_add' := (matrixEuclideanOperator m).map_add
  map_smul' := (matrixEuclideanOperator m).map_smul
  map_star' := matrixEuclideanOperator_star

theorem matrixEuclideanOperator_mem_unitary {M : Matrix (Fin m) (Fin m) ℝ}
    (hM : M ∈ unitary (Matrix (Fin m) (Fin m) ℝ)) :
    matrixEuclideanOperator m M ∈ unitary
      (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) := by
  obtain ⟨hLeft, hRight⟩ := unitary.mem_iff.mp hM
  constructor
  · rw [← matrixEuclideanOperator_star, ← matrixEuclideanOperator_mul,
      hLeft, matrixEuclideanOperator_one]
  · rw [← matrixEuclideanOperator_star, ← matrixEuclideanOperator_mul,
      hRight, matrixEuclideanOperator_one]

theorem euclideanOperatorMatrix_mem_unitary
    {T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hT : T ∈ unitary (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) :
    euclideanOperatorMatrix m T ∈ unitary (Matrix (Fin m) (Fin m) ℝ) := by
  let e := euclideanMatrixStarAlgEquiv m
  obtain ⟨hLeft, hRight⟩ := unitary.mem_iff.mp hT
  change e.symm T ∈ unitary (Matrix (Fin m) (Fin m) ℝ)
  constructor
  · rw [← map_star, ← map_mul, hLeft, map_one]
  · rw [← map_star, ← map_mul, hRight, map_one]

def euclideanMatrixUnitaryMulEquiv (m : ℕ) :
    Matrix.orthogonalGroup (Fin m) ℝ ≃*
      unitary (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) where
  toFun Q := ⟨matrixEuclideanOperator m Q.val, matrixEuclideanOperator_mem_unitary Q.property⟩
  invFun T := ⟨euclideanOperatorMatrix m T.val, euclideanOperatorMatrix_mem_unitary T.property⟩
  left_inv Q := Subtype.ext (euclideanOperatorMatrix_matrixEuclideanOperator Q.val)
  right_inv T := Subtype.ext (matrixEuclideanOperator_euclideanOperatorMatrix T.val)
  map_mul' Q R := Subtype.ext (matrixEuclideanOperator_mul Q.val R.val)

theorem lipschitz_euclideanMatrixUnitaryMulEquiv (m : ℕ) :
    LipschitzWith ‖matrixEuclideanOperator m‖₊ (euclideanMatrixUnitaryMulEquiv m) := by
  apply LipschitzWith.of_dist_le_mul
  intro Q R
  exact (matrixEuclideanOperator m).lipschitz.dist_le_mul Q.val R.val

theorem lipschitz_euclideanMatrixUnitaryMulEquiv_symm (m : ℕ) :
    LipschitzWith ‖euclideanOperatorMatrix m‖₊ (euclideanMatrixUnitaryMulEquiv m).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro T U
  exact (euclideanOperatorMatrix m).lipschitz.dist_le_mul T.val U.val

end
end BanachIsometric
