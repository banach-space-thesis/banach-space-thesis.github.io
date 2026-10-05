import JFA.TensorSlices
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Analysis.Normed.Operator.Completeness

/-! Right slice maps on the concrete injective tensor product. We first factor
the algebraic contraction through the tensor image using a proved kernel bound,
then extend continuously to its closure. No injectivity assumption is needed. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open scoped TensorProduct
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def rightContraction (ψ : X →L[𝕜] 𝕜) : E ⊗[𝕜] X →ₗ[𝕜] E :=
  TensorProduct.lift {
    toFun := fun e => (ψ.smulRight e).toLinearMap
    map_add' := by intro e f; ext x; exact smul_add (ψ x) e f
    map_smul' := by intro a e; ext x; exact smul_comm (ψ x) a e }

@[simp] theorem rightContraction_pure (ψ : X →L[𝕜] 𝕜) (e : E) (x : X) :
    rightContraction ψ (e ⊗ₜ[𝕜] x) = ψ x • e := rfl

theorem rightContraction_pairing (ψ : X →L[𝕜] 𝕜) (φ : E →L[𝕜] 𝕜)
    (z : E ⊗[𝕜] X) : φ (rightContraction ψ z) = ψ (tensorPairing 𝕜 E X z φ) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e x => simp [mul_comm]
  | add z w hz hw => simp only [map_add, ContinuousLinearMap.add_apply, hz, hw]

theorem norm_rightContraction_le (ψ : X →L[𝕜] 𝕜) (z : E ⊗[𝕜] X) :
    ‖rightContraction ψ z‖ ≤ ‖ψ‖ * ‖tensorPairing 𝕜 E X z‖ := by
  apply NormedSpace.norm_le_dual_bound 𝕜 _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro φ
  rw [rightContraction_pairing]
  calc
    ‖ψ (tensorPairing 𝕜 E X z φ)‖ ≤ ‖ψ‖ * ‖tensorPairing 𝕜 E X z φ‖ := ψ.le_opNorm _
    _ ≤ ‖ψ‖ * (‖tensorPairing 𝕜 E X z‖ * ‖φ‖) :=
      mul_le_mul_of_nonneg_left ((tensorPairing 𝕜 E X z).le_opNorm φ) (norm_nonneg ψ)
    _ = (‖ψ‖ * ‖tensorPairing 𝕜 E X z‖) * ‖φ‖ := (mul_assoc _ _ _).symm

theorem tensorPairing_ker_le_rightContraction_ker (ψ : X →L[𝕜] 𝕜) :
    LinearMap.ker (tensorPairing 𝕜 E X) ≤ LinearMap.ker (rightContraction ψ) := by
  intro z hz
  apply norm_le_zero_iff.mp
  simpa only [LinearMap.mem_ker.mp hz, norm_zero, mul_zero] using norm_rightContraction_le ψ z

def rightSliceOnRangeLinear (ψ : X →L[𝕜] 𝕜) :
    LinearMap.range (tensorPairing 𝕜 E X) →ₗ[𝕜] E :=
  ((LinearMap.ker (tensorPairing 𝕜 E X)).liftQ (rightContraction ψ)
    (tensorPairing_ker_le_rightContraction_ker ψ)).comp
    (tensorPairing 𝕜 E X).quotKerEquivRange.symm.toLinearMap

@[simp] theorem rightSliceOnRangeLinear_image (ψ : X →L[𝕜] 𝕜) (z : E ⊗[𝕜] X) :
    rightSliceOnRangeLinear ψ ⟨tensorPairing 𝕜 E X z, ⟨z, rfl⟩⟩ = rightContraction ψ z := by
  simp [rightSliceOnRangeLinear]

theorem norm_rightSliceOnRangeLinear_le (ψ : X →L[𝕜] 𝕜)
    (z : LinearMap.range (tensorPairing 𝕜 E X)) :
    ‖rightSliceOnRangeLinear ψ z‖ ≤ ‖ψ‖ * ‖z‖ := by
  rcases z with ⟨_, w, rfl⟩
  simpa only [rightSliceOnRangeLinear_image, Submodule.coe_norm] using norm_rightContraction_le ψ w

def rightSliceOnRange (ψ : X →L[𝕜] 𝕜) :
    LinearMap.range (tensorPairing 𝕜 E X) →L[𝕜] E :=
  (rightSliceOnRangeLinear (E := E) ψ).mkContinuous ‖ψ‖
    (norm_rightSliceOnRangeLinear_le (E := E) ψ)

def tensorRangeEmbedding : LinearMap.range (tensorPairing 𝕜 E X) →ₗᵢ[𝕜] InjectiveTensor 𝕜 E X where
  toLinearMap := Submodule.inclusion (Submodule.le_topologicalClosure _)
  norm_map' := fun _ => rfl

theorem tensorRangeEmbedding_dense : DenseRange (tensorRangeEmbedding (𝕜 := 𝕜) (E := E) (X := X)) := by
  apply injectiveInclusion_dense.mono
  rintro _ ⟨z, rfl⟩
  exact ⟨⟨tensorPairing 𝕜 E X z, ⟨z, rfl⟩⟩, rfl⟩

def rightSlice [CompleteSpace E] (ψ : X →L[𝕜] 𝕜) : InjectiveTensor 𝕜 E X →L[𝕜] E :=
  (rightSliceOnRange (E := E) ψ).extend
    (tensorRangeEmbedding (𝕜 := 𝕜) (E := E) (X := X)).toContinuousLinearMap
    tensorRangeEmbedding_dense
    (tensorRangeEmbedding (𝕜 := 𝕜) (E := E) (X := X)).isometry.isUniformInducing

@[simp] theorem rightSlice_inclusion [CompleteSpace E] (ψ : X →L[𝕜] 𝕜) (z : E ⊗[𝕜] X) :
    rightSlice ψ (injectiveInclusion 𝕜 E X z) = rightContraction ψ z := by
  change rightSlice ψ
    (tensorRangeEmbedding (𝕜 := 𝕜) (E := E) (X := X)
      ⟨tensorPairing 𝕜 E X z, ⟨z, rfl⟩⟩) = _
  exact (ContinuousLinearMap.extend_eq (rightSliceOnRange (E := E) ψ)
    (tensorRangeEmbedding (𝕜 := 𝕜) (E := E) (X := X)).toContinuousLinearMap
    tensorRangeEmbedding_dense
    (tensorRangeEmbedding (𝕜 := 𝕜) (E := E) (X := X)).isometry.isUniformInducing
    ⟨tensorPairing 𝕜 E X z, ⟨z, rfl⟩⟩).trans (rightSliceOnRangeLinear_image ψ z)

@[simp] theorem rightSlice_pure [CompleteSpace E] (ψ : X →L[𝕜] 𝕜) (e : E) (x : X) :
    rightSlice ψ (injectivePure 𝕜 E X e x) = ψ x • e :=
  (rightSlice_inclusion ψ (e ⊗ₜ[𝕜] x)).trans (rightContraction_pure ψ e x)

theorem rightSlice_pairing [CompleteSpace E] (ψ : X →L[𝕜] 𝕜) (φ : E →L[𝕜] 𝕜)
    (z : InjectiveTensor 𝕜 E X) : φ (rightSlice ψ z) = ψ (leftSlice φ z) := by
  refine injectiveInclusion_dense.induction_on z
    (isClosed_eq (φ.continuous.comp (rightSlice ψ).continuous)
      (ψ.continuous.comp (leftSlice φ).continuous)) ?_
  intro w
  rw [rightSlice_inclusion]
  exact rightContraction_pairing ψ φ w

theorem norm_rightSlice_le [CompleteSpace E] (ψ : X →L[𝕜] 𝕜) :
    ‖rightSlice (E := E) ψ‖ ≤ ‖ψ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg ψ)
  intro z
  refine injectiveInclusion_dense.induction_on z
    (isClosed_le (rightSlice ψ).continuous.norm (continuous_const.mul continuous_norm)) ?_
  intro w
  rw [rightSlice_inclusion]
  exact norm_rightContraction_le ψ w

end JFA
