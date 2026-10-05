import JFA.TensorRemainder
import JFA.TensorFunction

/-! Range separability from a common separable subspace of all dual slices.
The embedding is into the actual normed continuous-function space. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {F X A : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] [SeparableSpace F]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup A] [NormedSpace 𝕜 A]

def rangeTensorFunction (R : A →L[𝕜] InjectiveTensor 𝕜 F X) (Y : Submodule 𝕜 X)
    (hY : ∀ a (φ : F →L[𝕜] 𝕜), leftSlice φ (R a) ∈ Y)
    (z : LinearMap.range R.toLinearMap) : C(DualBall 𝕜 F, Y) := by
  have hval : ∀ φ : DualBall 𝕜 F, tensorFunction z.val φ ∈ Y := by
    intro φ
    rcases z.property with ⟨a, ha⟩
    rw [← ha, tensorFunction_apply]
    exact hY a (WeakDual.toStrongDual φ.val)
  exact ⟨fun φ => ⟨tensorFunction z.val φ, hval φ⟩,
    (tensorFunction z.val).continuous.subtype_mk hval⟩

theorem norm_rangeTensorFunction (R : A →L[𝕜] InjectiveTensor 𝕜 F X) (Y : Submodule 𝕜 X)
    (hY : ∀ a (φ : F →L[𝕜] 𝕜), leftSlice φ (R a) ∈ Y)
    (z : LinearMap.range R.toLinearMap) : ‖rangeTensorFunction R Y hY z‖ = ‖z‖ := by
  have hnorm : ‖rangeTensorFunction R Y hY z‖ = ‖tensorFunction z.val‖ := by
    apply le_antisymm
    · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
      intro φ
      exact (tensorFunction z.val).norm_coe_le_norm φ
    · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
      intro φ
      exact (rangeTensorFunction R Y hY z).norm_coe_le_norm φ
  exact hnorm.trans (norm_tensorFunction z.val)

def rangeTensorFunctionIsometry (R : A →L[𝕜] InjectiveTensor 𝕜 F X) (Y : Submodule 𝕜 X)
    (hY : ∀ a (φ : F →L[𝕜] 𝕜), leftSlice φ (R a) ∈ Y) :
    LinearMap.range R.toLinearMap →ₗᵢ[𝕜] C(DualBall 𝕜 F, Y) where
  toLinearMap := {
    toFun := rangeTensorFunction R Y hY
    map_add' := by
      intro z w; ext φ
      change tensorFunction (z.val + w.val) φ = tensorFunction z.val φ + tensorFunction w.val φ
      rw [map_add, ContinuousMap.add_apply]
    map_smul' := by
      intro a z; ext φ
      change tensorFunction (a • z.val) φ = a • tensorFunction z.val φ
      rw [map_smul, ContinuousMap.smul_apply] }
  norm_map' := norm_rangeTensorFunction R Y hY

theorem hasSeparableRange_of_slices_in_separable_subspace
    (R : A →L[𝕜] InjectiveTensor 𝕜 F X) (Y : Submodule 𝕜 X)
    (hsep : IsSeparable (Y : Set X))
    (hY : ∀ a (φ : F →L[𝕜] 𝕜), leftSlice φ (R a) ∈ Y) :
    HasSeparableRange 𝕜 A (InjectiveTensor 𝕜 F X) R := by
  letI : SeparableSpace Y := hsep.separableSpace
  letI : SecondCountableTopology (LinearMap.range R.toLinearMap) :=
    (rangeTensorFunctionIsometry R Y hY).isometry.isEmbedding.secondCountableTopology
  change IsSeparable (LinearMap.range R.toLinearMap : Set (InjectiveTensor 𝕜 F X))
  exact IsSeparable.of_subtype _

end JFA
