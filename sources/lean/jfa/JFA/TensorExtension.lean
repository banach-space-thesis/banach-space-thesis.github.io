import JFA.CrossnormCompletion
import JFA.RightSlice
import Mathlib.Tactic.Ring

/-! Extension of U ⊗ I from every reasonable-crossnorm completion to the
injective completion, with the expected operator norm bound. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open scoped TensorProduct
namespace JFA
universe u
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F X A : Type u}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup A] [NormedSpace 𝕜 A]

def mappedTensor (U : E →L[𝕜] F) : E ⊗[𝕜] X →ₗ[𝕜] InjectiveTensor 𝕜 F X :=
  (injectiveInclusion 𝕜 F X).comp (TensorProduct.map U.toLinearMap (LinearMap.id : X →ₗ[𝕜] X))

@[simp] theorem mappedTensor_pure (U : E →L[𝕜] F) (e : E) (x : X) :
    mappedTensor U (e ⊗ₜ[𝕜] x) = injectivePure 𝕜 F X (U e) x := rfl

theorem mappedTensor_pairing (U : E →L[𝕜] F) (z : E ⊗[𝕜] X) (φ : F →L[𝕜] 𝕜) :
    (mappedTensor U z).val φ = tensorPairing 𝕜 E X z (φ.comp U) := by
  induction z using TensorProduct.induction_on with
  | zero => simp [mappedTensor]
  | tmul e x => rfl
  | add z w hz hw => simpa only [map_add, ContinuousLinearMap.add_apply] using congrArg₂ (· + ·) hz hw

theorem norm_mappedTensor_le (p : ReasonableCrossnorm 𝕜 E X) (U : E →L[𝕜] F)
    (z : E ⊗[𝕜] X) : ‖mappedTensor U z‖ ≤ ‖U‖ * p.seminorm z := by
  change ‖(mappedTensor U z).val‖ ≤ _
  apply (dualOperator_norm_le_iff _ _ (mul_nonneg (norm_nonneg U) (apply_nonneg p.seminorm z))).mpr
  intro φ ψ
  rw [mappedTensor_pairing]
  calc
    ‖ψ (tensorPairing 𝕜 E X z (φ.comp U))‖ ≤
        (‖φ.comp U‖ * ‖ψ‖) * p.seminorm z := p.dual_le z (φ.comp U) ψ
    _ ≤ ((‖φ‖ * ‖U‖) * ‖ψ‖) * p.seminorm z :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (φ.opNorm_comp_le U) (norm_nonneg ψ))
        (apply_nonneg p.seminorm z)
    _ = ((‖U‖ * p.seminorm z) * ‖φ‖) * ‖ψ‖ := by ring

def tensorMapOnAlgebraic (p : ReasonableCrossnorm 𝕜 E X) (U : E →L[𝕜] F) :
    p.Algebraic →L[𝕜] InjectiveTensor 𝕜 F X :=
  LinearMap.mkContinuous (E := p.Algebraic) (F := InjectiveTensor 𝕜 F X)
    (mappedTensor (X := X) U : p.Algebraic →ₗ[𝕜] InjectiveTensor 𝕜 F X)
    ‖U‖ (fun z => norm_mappedTensor_le p U z)

@[simp] theorem tensorMapOnAlgebraic_apply (p : ReasonableCrossnorm 𝕜 E X)
    (U : E →L[𝕜] F) (z : p.Algebraic) : tensorMapOnAlgebraic p U z = mappedTensor U z := rfl

def crossnormEmbedding (p : ReasonableCrossnorm 𝕜 E X) (ι : E ⊗[𝕜] X →ₗ[𝕜] A)
    (hι : IsTensorCompletion 𝕜 E X A p ι) : p.Algebraic →ₗᵢ[𝕜] A where
  toLinearMap := ι
  norm_map' := hι.2.2

def tensorExtension [CompleteSpace X] (p : ReasonableCrossnorm 𝕜 E X)
    (ι : E ⊗[𝕜] X →ₗ[𝕜] A) (hι : IsTensorCompletion 𝕜 E X A p ι)
    (U : E →L[𝕜] F) : A →L[𝕜] InjectiveTensor 𝕜 F X :=
  (tensorMapOnAlgebraic p U).extend (crossnormEmbedding p ι hι).toContinuousLinearMap
    hι.2.1 (crossnormEmbedding p ι hι).isometry.isUniformInducing

@[simp] theorem tensorExtension_inclusion [CompleteSpace X]
    (p : ReasonableCrossnorm 𝕜 E X) (ι : E ⊗[𝕜] X →ₗ[𝕜] A)
    (hι : IsTensorCompletion 𝕜 E X A p ι) (U : E →L[𝕜] F) (z : E ⊗[𝕜] X) :
    tensorExtension p ι hι U (ι z) = mappedTensor U z := by
  have h := ContinuousLinearMap.extend_eq (E := p.Algebraic)
    (F := InjectiveTensor 𝕜 F X) (Fₗ := A) (tensorMapOnAlgebraic p U)
    (crossnormEmbedding p ι hι).toContinuousLinearMap hι.2.1
    (crossnormEmbedding p ι hι).isometry.isUniformInducing (show p.Algebraic from z)
  rw [tensorMapOnAlgebraic_apply] at h
  exact h

@[simp] theorem tensorExtension_pure [CompleteSpace X]
    (p : ReasonableCrossnorm 𝕜 E X) (ι : E ⊗[𝕜] X →ₗ[𝕜] A)
    (hι : IsTensorCompletion 𝕜 E X A p ι) (U : E →L[𝕜] F) (e : E) (x : X) :
    tensorExtension p ι hι U (ι (e ⊗ₜ[𝕜] x)) = injectivePure 𝕜 F X (U e) x :=
  (tensorExtension_inclusion p ι hι U _).trans (mappedTensor_pure U e x)

theorem norm_tensorExtension_le [CompleteSpace X]
    (p : ReasonableCrossnorm 𝕜 E X) (ι : E ⊗[𝕜] X →ₗ[𝕜] A)
    (hι : IsTensorCompletion 𝕜 E X A p ι) (U : E →L[𝕜] F) : ‖tensorExtension p ι hι U‖ ≤ ‖U‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg U)
  intro a
  refine hι.2.1.induction_on a
    (isClosed_le (tensorExtension p ι hι U).continuous.norm (continuous_const.mul continuous_norm)) ?_
  intro z
  rw [tensorExtension_inclusion, hι.2.2]
  exact norm_mappedTensor_le p U z

end JFA
