import JFA.TensorSlices
import JFA.ScalarExtraction

/-! Functoriality of the concrete injective completion, obtained by continuous
precomposition on dual operators and restriction to the tensor closures. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open scoped TensorProduct
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F G X : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def dualPrecompose (U : E →L[𝕜] F) : (F →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜 :=
  (ContinuousLinearMap.compL 𝕜 E F 𝕜).flip U

def tensorAmbientMap (U : E →L[𝕜] F) : DualOperators 𝕜 E X →L[𝕜] DualOperators 𝕜 F X :=
  (ContinuousLinearMap.compL 𝕜 (F →L[𝕜] 𝕜) (E →L[𝕜] 𝕜) X).flip (dualPrecompose U)

theorem tensorAmbientMap_pairing (U : E →L[𝕜] F) (z : E ⊗[𝕜] X) :
    tensorAmbientMap U (tensorPairing 𝕜 E X z) =
      tensorPairing 𝕜 F X (TensorProduct.map U.toLinearMap (LinearMap.id : X →ₗ[𝕜] X) z) := by
  ext φ
  change tensorPairing 𝕜 E X z (φ.comp U) =
    tensorPairing 𝕜 F X (TensorProduct.map U.toLinearMap (LinearMap.id : X →ₗ[𝕜] X) z) φ
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, ContinuousLinearMap.zero_apply]
  | tmul e x => rfl
  | add z w hz hw => simp only [map_add, ContinuousLinearMap.add_apply, hz, hw]

theorem tensorAmbientMap_mem (U : E →L[𝕜] F) (z : InjectiveTensor 𝕜 E X) :
    tensorAmbientMap U z.val ∈ InjectiveTensor 𝕜 F X := by
  refine (injectiveInclusion_dense (𝕜 := 𝕜) (E := E) (X := X)).induction_on z
    ((Submodule.isClosed_topologicalClosure _).preimage
      ((tensorAmbientMap (X := X) U).comp (InjectiveTensor 𝕜 E X).subtypeL).continuous) ?_
  intro w
  change tensorAmbientMap U (tensorPairing 𝕜 E X w) ∈ _
  rw [tensorAmbientMap_pairing]
  exact Submodule.le_topologicalClosure _ ⟨_, rfl⟩

def injectiveTensorMap (U : E →L[𝕜] F) : InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X :=
  ((tensorAmbientMap (X := X) U).comp (InjectiveTensor 𝕜 E X).subtypeL).codRestrict
    (InjectiveTensor 𝕜 F X) (tensorAmbientMap_mem U)

@[simp] theorem injectiveTensorMap_pure (U : E →L[𝕜] F) (e : E) (x : X) :
    injectiveTensorMap U (injectivePure 𝕜 E X e x) = injectivePure 𝕜 F X (U e) x := rfl

theorem injectiveTensor_ext {B : Type*} [NormedAddCommGroup B] [NormedSpace 𝕜 B]
    {T Q : InjectiveTensor 𝕜 E X →L[𝕜] B}
    (hpure : ∀ e x, T (injectivePure 𝕜 E X e x) = Q (injectivePure 𝕜 E X e x)) : T = Q := by
  apply ContinuousLinearMap.ext
  intro z
  refine injectiveInclusion_dense.induction_on z (isClosed_eq T.continuous Q.continuous) ?_
  intro w
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul e x => exact hpure e x
  | add z w hz hw => simp only [map_add, hz, hw]

theorem injectiveTensorMap_comp (U : E →L[𝕜] F) (V : F →L[𝕜] G) :
    injectiveTensorMap (X := X) (V.comp U) = (injectiveTensorMap V).comp (injectiveTensorMap U) := by
  apply injectiveTensor_ext
  intro e x
  change injectiveTensorMap (V.comp U) (injectivePure 𝕜 E X e x) =
    injectiveTensorMap V (injectiveTensorMap U (injectivePure 𝕜 E X e x))
  simp only [ContinuousLinearMap.comp_apply, injectiveTensorMap_pure]

@[simp] theorem injectiveTensorMap_id :
    injectiveTensorMap (X := X) (ContinuousLinearMap.id 𝕜 E) =
      ContinuousLinearMap.id 𝕜 (InjectiveTensor 𝕜 E X) := by
  apply injectiveTensor_ext
  intro e x
  change injectiveTensorMap (ContinuousLinearMap.id 𝕜 E) (injectivePure 𝕜 E X e x) =
    injectivePure 𝕜 E X e x
  simp only [ContinuousLinearMap.id_apply, injectiveTensorMap_pure]

end JFA
