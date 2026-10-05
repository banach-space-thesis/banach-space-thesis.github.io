import Posets.ProductQuotientCoordinates
import JFA.EpsilonQuotient

/-! Strongly split operator quotients on injective tensor products. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open ThesisCommon TopologicalSpace
namespace Posets

variable {𝕜 E X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem productTensorLift_norm_le (U : E →L[𝕜] E) :
    ‖JFA.injectiveTensorMap (X := X) U‖ ≤ ‖U‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg U)
  intro z
  change ‖JFA.tensorAmbientMap U z.val‖ ≤ ‖U‖ * ‖z‖
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg U) (norm_nonneg z))
  intro φ
  change ‖z.val (φ.comp U)‖ ≤ ‖U‖ * ‖z‖ * ‖φ‖
  calc
    _ ≤ ‖z.val‖ * ‖φ.comp U‖ := z.val.le_opNorm _
    _ ≤ ‖z‖ * (‖φ‖ * ‖U‖) :=
      mul_le_mul_of_nonneg_left (φ.opNorm_comp_le U) (norm_nonneg z)
    _ = _ := by ring

def productTensorLiftLinearMap : (E →L[𝕜] E) →ₗ[𝕜]
    (JFA.InjectiveTensor 𝕜 E X →L[𝕜] JFA.InjectiveTensor 𝕜 E X) where
  toFun := JFA.injectiveTensorMap
  map_add' := by
    intro U V
    apply JFA.injectiveTensor_ext
    intro e x
    simp only [ContinuousLinearMap.add_apply, JFA.injectiveTensorMap_pure]
    exact map_add (JFA.injectiveLeftPureMap x) (U e) (V e)
  map_smul' := by
    intro a U
    apply JFA.injectiveTensor_ext
    intro e x
    simp only [ContinuousLinearMap.smul_apply, JFA.injectiveTensorMap_pure, RingHom.id_apply]
    exact map_smul (JFA.injectiveLeftPureMap x) a (U e)

def productTensorLiftMap : (E →L[𝕜] E) →L[𝕜]
    (JFA.InjectiveTensor 𝕜 E X →L[𝕜] JFA.InjectiveTensor 𝕜 E X) := by
  refine LinearMap.mkContinuous (productTensorLiftLinearMap (𝕜 := 𝕜) (E := E) (X := X)) 1 ?_
  intro U
  change ‖JFA.injectiveTensorMap (X := X) U‖ ≤ 1 * ‖U‖
  simpa only [one_mul] using productTensorLift_norm_le (X := X) U

def productTensorSection : BoundedHom 𝕜 (E →L[𝕜] E)
    (JFA.InjectiveTensor 𝕜 E X →L[𝕜] JFA.InjectiveTensor 𝕜 E X) where
  toContinuousLinearMap := productTensorLiftMap
  map_mul' U V := JFA.injectiveTensorMap_comp V U

variable [CompleteSpace E] [SeparableSpace E] [CompleteSpace X]
  (hX : ¬ SeparableSpace X) (hfew : JFA.HasFewOperators 𝕜 X)

def productTensorQuotient : BoundedHom 𝕜
    (JFA.InjectiveTensor 𝕜 E X →L[𝕜] JFA.InjectiveTensor 𝕜 E X) (E →L[𝕜] E) where
  toContinuousLinearMap := JFA.epsilonScalarQuotient hX hfew
  map_mul' S T := JFA.epsilonScalarOperator_comp hX hfew T S

theorem productTensorQuotient_norm_le :
    ‖(productTensorQuotient (E := E) hX hfew).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  change ‖JFA.epsilonScalarOperator hX hfew T‖ ≤ 1 * ‖T‖
  simpa only [one_mul] using JFA.norm_epsilonScalarOperator_le hX hfew T

theorem productTensor_strongSplit :
    StrongSplit 𝕜 (JFA.InjectiveTensor 𝕜 E X) (E →L[𝕜] E)
      (productTensorQuotient hX hfew) productTensorSection :=
  ⟨JFA.epsilonScalarQuotient_surjective hX hfew,
    JFA.epsilonScalarOperator_eq_zero_iff hX hfew,
    JFA.epsilonScalarOperator_tensorMap hX hfew⟩

include hX hfew in
theorem productTensorSection_norm (U : E →L[𝕜] E) :
    ‖productTensorSection (𝕜 := 𝕜) (E := E) (X := X) U‖ = ‖U‖ := by
  apply le_antisymm (productTensorLift_norm_le (X := X) U)
  have hb := JFA.norm_epsilonScalarOperator_le hX hfew (JFA.injectiveTensorMap (X := X) U)
  rwa [JFA.epsilonScalarOperator_tensorMap hX hfew] at hb

include hX hfew in
theorem productTensorSection_isometry :
    Isometry (productTensorSection (𝕜 := 𝕜) (E := E) (X := X)) :=
  AddMonoidHomClass.isometry_of_norm
    (productTensorSection (𝕜 := 𝕜) (E := E) (X := X)).toContinuousLinearMap
    (productTensorSection_norm (E := E) hX hfew)

end Posets
