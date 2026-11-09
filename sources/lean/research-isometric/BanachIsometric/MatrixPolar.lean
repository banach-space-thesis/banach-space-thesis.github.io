import BanachIsometric.EquivariantPolar
import BanachIsometric.EuclideanMatrixAlgebra

/-!
# Ambient polar correction in the actual tensor matrix coordinates

The Euclidean operator correction is transported through the proved continuous
linear star-algebra equivalence. The source and target matrix norms remain the
ordinary `L∞` operator norms used by the tensor representation. All changes of
norm contribute their explicit continuous-linear-map Lipschitz constants.
-/

namespace BanachIsometric

open Set
open scoped Topology NNReal Matrix.Norms.Operator

noncomputable section

theorem exists_lipschitz_equivariant_matrix_polar (m : ℕ) :
    ∃ U : Set (Matrix (Fin m) (Fin m) ℝ),
      ∃ P : Matrix (Fin m) (Fin m) ℝ → Matrix (Fin m) (Fin m) ℝ, ∃ L : ℝ≥0,
      IsOpen U ∧ (unitary (Matrix (Fin m) (Fin m) ℝ) : Set _) ⊆ U ∧
      LipschitzOnWith L P U ∧
      (∀ T ∈ U, P T ∈ unitary (Matrix (Fin m) (Fin m) ℝ)) ∧
      (∀ h ∈ unitary (Matrix (Fin m) (Fin m) ℝ), P h = h) ∧
      (∀ h ∈ unitary (Matrix (Fin m) (Fin m) ℝ), ∀ T, P (h * T) = h * P T) ∧
      (∀ h ∈ unitary (Matrix (Fin m) (Fin m) ℝ), ∀ T ∈ U, h * T ∈ U) := by
  obtain ⟨V, Q, LQ, hV, hUnitV, hQLip, hQUnit, hQFix, hQEquiv, hQInvariant⟩ :=
    exists_lipschitz_equivariant_polar_correction (E := EuclideanSpace ℝ (Fin m))
  let U : Set (Matrix (Fin m) (Fin m) ℝ) := matrixEuclideanOperator m ⁻¹' V
  let P : Matrix (Fin m) (Fin m) ℝ → Matrix (Fin m) (Fin m) ℝ := fun T =>
    euclideanOperatorMatrix m (Q (matrixEuclideanOperator m T))
  have hCompose : LipschitzOnWith (LQ * ‖matrixEuclideanOperator m‖₊)
      (fun T => Q (matrixEuclideanOperator m T)) U :=
    hQLip.comp (matrixEuclideanOperator m).lipschitz.lipschitzOnWith (fun _ h => h)
  have hPLip : LipschitzOnWith
      (‖euclideanOperatorMatrix m‖₊ * (LQ * ‖matrixEuclideanOperator m‖₊)) P U :=
    (euclideanOperatorMatrix m).lipschitz.lipschitzOnWith.comp hCompose (fun _ _ => mem_univ _)
  refine ⟨U, P, ‖euclideanOperatorMatrix m‖₊ * (LQ * ‖matrixEuclideanOperator m‖₊),
    hV.preimage (matrixEuclideanOperator m).continuous, ?_, hPLip, ?_, ?_, ?_, ?_⟩
  · intro h hh
    exact hUnitV (matrixEuclideanOperator_mem_unitary hh)
  · intro T hT
    exact euclideanOperatorMatrix_mem_unitary (hQUnit _ hT)
  · intro h hh
    change euclideanOperatorMatrix m (Q (matrixEuclideanOperator m h)) = h
    rw [hQFix _ (matrixEuclideanOperator_mem_unitary hh),
      euclideanOperatorMatrix_matrixEuclideanOperator]
  · intro h hh T
    change euclideanOperatorMatrix m (Q (matrixEuclideanOperator m (h * T))) = _
    rw [matrixEuclideanOperator_mul, hQEquiv _ (matrixEuclideanOperator_mem_unitary hh),
      euclideanOperatorMatrix_mul, euclideanOperatorMatrix_matrixEuclideanOperator]
  · intro h hh T hT
    change matrixEuclideanOperator m (h * T) ∈ V
    rw [matrixEuclideanOperator_mul]
    exact hQInvariant _ (matrixEuclideanOperator_mem_unitary hh) _ hT

end
end BanachIsometric
