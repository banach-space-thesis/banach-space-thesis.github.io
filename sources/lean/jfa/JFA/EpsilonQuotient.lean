import JFA.TensorCancellation

/-! The bounded scalar quotient on epsilon-tensor operators: linearity,
contractivity, surjectivity and the exact separable-range kernel. Its already
proved composition law is the algebraic step used in the ideal classification. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace
open scoped TensorProduct
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F X : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] [SeparableSpace F]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem epsilonScalarOperator_add (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (T Q : InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X) :
    epsilonScalarOperator hX hfew (T + Q) =
      epsilonScalarOperator hX hfew T + epsilonScalarOperator hX hfew Q := by
  apply ContinuousLinearMap.ext
  intro e
  change scalarExtraction hX hfew ((T + Q).comp (injectivePureMap e)) =
    scalarExtraction hX hfew (T.comp (injectivePureMap e)) +
      scalarExtraction hX hfew (Q.comp (injectivePureMap e))
  rw [ContinuousLinearMap.add_comp, scalarExtraction_add]

theorem epsilonScalarOperator_smul (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (a : 𝕜) (T : InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X) :
    epsilonScalarOperator hX hfew (a • T) = a • epsilonScalarOperator hX hfew T := by
  apply ContinuousLinearMap.ext
  intro e
  change scalarExtraction hX hfew ((a • T).comp (injectivePureMap e)) =
    a • scalarExtraction hX hfew (T.comp (injectivePureMap e))
  rw [ContinuousLinearMap.smul_comp, scalarExtraction_smul]

theorem norm_epsilonScalarOperator_le (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (T : InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X) :
    ‖epsilonScalarOperator hX hfew T‖ ≤ ‖T‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg T) _

def epsilonScalarQuotient (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X) :
    (InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X) →L[𝕜] (E →L[𝕜] F) :=
  LinearMap.mkContinuous
    (E := InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X) (F := E →L[𝕜] F) {
    toFun := epsilonScalarOperator (E := E) (F := F) hX hfew
    map_add' := epsilonScalarOperator_add hX hfew
    map_smul' := fun a T => by simpa only [RingHom.id_apply] using epsilonScalarOperator_smul hX hfew a T }
    1 (fun T => by
      change ‖epsilonScalarOperator hX hfew T‖ ≤ 1 * ‖T‖
      simpa only [one_mul] using norm_epsilonScalarOperator_le hX hfew T)

theorem epsilonScalarOperator_tensorMap (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (U : E →L[𝕜] F) : epsilonScalarOperator hX hfew (injectiveTensorMap U) = U := by
  apply epsilonScalarOperator_of_decomposition hX hfew _ U 0 hasSeparableRange_zero
  intro e x
  simp only [injectiveTensorMap_pure, ContinuousLinearMap.zero_apply, add_zero]

theorem epsilonScalarQuotient_surjective (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X) :
    Function.Surjective (epsilonScalarQuotient (E := E) (F := F) hX hfew) := by
  intro U
  exact ⟨injectiveTensorMap U, epsilonScalarOperator_tensorMap hX hfew U⟩

theorem epsilonScalarOperator_eq_zero_iff [SeparableSpace E]
    (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (T : InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X) :
    epsilonScalarOperator hX hfew T = 0 ↔
      HasSeparableRange 𝕜 (InjectiveTensor 𝕜 E X) (InjectiveTensor 𝕜 F X) T := by
  have hzero (x : X) : injectivePure 𝕜 F X 0 x = 0 := by
    change injectiveInclusion 𝕜 F X (0 ⊗ₜ[𝕜] x) = 0
    rw [TensorProduct.zero_tmul, map_zero]
  constructor
  · intro hT
    have hmap : injectiveTensorMap (X := X) (0 : E →L[𝕜] F) = 0 := by
      apply injectiveTensor_ext
      intro e x
      simp only [injectiveTensorMap_pure, ContinuousLinearMap.zero_apply, hzero]
    have hr : epsilonRemainder hX hfew T = T := by
      rw [epsilonRemainder, hT, hmap]
      apply ContinuousLinearMap.ext
      intro z
      change T z - 0 = T z
      exact sub_zero _
    exact hr ▸ epsilonRemainder_separable hX hfew T
  · intro hT
    apply epsilonScalarOperator_of_decomposition hX hfew T 0 T hT
    intro e x
    simp only [ContinuousLinearMap.zero_apply, hzero, zero_add]

end JFA
