import JFA.ScalarExtraction

/-! The bounded operator U in Theorem 1.1, constructed from the original
few-operator hypothesis. Its scalar slice coordinates and norm bound are proved.
Proving separability of the full tensor remainder is a separate remaining step. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace
open scoped TensorProduct
namespace JFA
universe u
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F X A : Type u}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] [SeparableSpace F]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup A] [NormedSpace 𝕜 A]

def extractedOperator (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (p : ReasonableCrossnorm 𝕜 E X) (ι : E ⊗[𝕜] X →ₗ[𝕜] A)
    (hι : IsTensorCompletion 𝕜 E X A p ι)
    (T : A →L[𝕜] InjectiveTensor 𝕜 F X) : E →L[𝕜] F :=
  LinearMap.mkContinuous {
    toFun := fun e => scalarExtraction hX hfew (T.comp (completionPureMap p ι hι e))
    map_add' := by
      intro e f
      rw [completionPureMap_add, ContinuousLinearMap.comp_add, scalarExtraction_add]
    map_smul' := by
      intro a e
      rw [completionPureMap_smul, ContinuousLinearMap.comp_smul, scalarExtraction_smul]
      rfl }
    ‖T‖ (fun e =>
      (norm_scalarExtraction_le hX hfew _).trans
        ((T.opNorm_comp_le _).trans
          (mul_le_mul_of_nonneg_left (norm_completionPureMap_le p ι hι e) (norm_nonneg T))))

theorem extractedOperator_spec (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (p : ReasonableCrossnorm 𝕜 E X) (ι : E ⊗[𝕜] X →ₗ[𝕜] A)
    (hι : IsTensorCompletion 𝕜 E X A p ι)
    (T : A →L[𝕜] InjectiveTensor 𝕜 F X) (e : E) (φ : F →L[𝕜] 𝕜) :
    φ (extractedOperator hX hfew p ι hι T e) =
      scalarCoefficient hX hfew (sliceOperator (T.comp (completionPureMap p ι hι e)) φ) :=
  scalarExtraction_spec hX hfew _ φ

theorem norm_extractedOperator_le (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (p : ReasonableCrossnorm 𝕜 E X) (ι : E ⊗[𝕜] X →ₗ[𝕜] A)
    (hι : IsTensorCompletion 𝕜 E X A p ι)
    (T : A →L[𝕜] InjectiveTensor 𝕜 F X) : ‖extractedOperator hX hfew p ι hι T‖ ≤ ‖T‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg T) _

theorem extractedOperator_slice_remainder_separable
    (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (p : ReasonableCrossnorm 𝕜 E X) (ι : E ⊗[𝕜] X →ₗ[𝕜] A)
    (hι : IsTensorCompletion 𝕜 E X A p ι)
    (T : A →L[𝕜] InjectiveTensor 𝕜 F X) (e : E) (φ : F →L[𝕜] 𝕜) :
    HasSeparableRange 𝕜 X X
      (sliceOperator (T.comp (completionPureMap p ι hι e)) φ -
        φ (extractedOperator hX hfew p ι hι T e) • ContinuousLinearMap.id 𝕜 X) := by
  rw [extractedOperator_spec]
  have heq : sliceOperator (T.comp (completionPureMap p ι hι e)) φ -
      scalarCoefficient hX hfew (sliceOperator (T.comp (completionPureMap p ι hι e)) φ) •
        ContinuousLinearMap.id 𝕜 X =
      scalarRemainder hX hfew (sliceOperator (T.comp (completionPureMap p ι hι e)) φ) := by
    exact sub_eq_iff_eq_add.mpr
      ((scalar_decomposition hX hfew (sliceOperator (T.comp (completionPureMap p ι hι e)) φ)).trans
        (add_comm _ _))
  rw [heq]
  exact scalarRemainder_separable hX hfew _

end JFA
