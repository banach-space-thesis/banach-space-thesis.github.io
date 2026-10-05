import JFA.DualBall
import JFA.TensorNorming
import Mathlib.Topology.ContinuousMap.Compact

/-! An isometric representation of the concrete injective tensor product as
continuous vector-valued functions on the weak-star dual unit ball. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace
open scoped TensorProduct
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {F X : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem norm_dualBall_le (φ : DualBall 𝕜 F) : ‖WeakDual.toStrongDual φ.val‖ ≤ 1 := by
  simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using φ.property

def algebraicTensorFunction : F ⊗[𝕜] X →ₗ[𝕜] C(DualBall 𝕜 F, X) :=
  TensorProduct.lift {
    toFun := fun f => {
      toFun := fun x => ⟨fun φ => φ.val f • x,
        ((WeakDual.eval_continuous f).comp continuous_subtype_val).smul continuous_const⟩
      map_add' := by intro x y; ext φ; exact smul_add (φ.val f) x y
      map_smul' := by intro a x; ext φ; exact smul_comm (φ.val f) a x }
    map_add' := by
      intro f g; ext x φ
      change φ.val (f + g) • x = φ.val f • x + φ.val g • x
      rw [map_add, add_smul]
    map_smul' := by
      intro a f; ext x φ
      change φ.val (a • f) • x = a • (φ.val f • x)
      rw [map_smul, smul_eq_mul, mul_smul] }

@[simp] theorem algebraicTensorFunction_pure (f : F) (x : X) (φ : DualBall 𝕜 F) :
    algebraicTensorFunction (f ⊗ₜ[𝕜] x) φ = φ.val f • x := rfl

theorem algebraicTensorFunction_apply (z : F ⊗[𝕜] X) (φ : DualBall 𝕜 F) :
    algebraicTensorFunction z φ = tensorPairing 𝕜 F X z (WeakDual.toStrongDual φ.val) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f x => rfl
  | add z w hz hw => simpa only [map_add, ContinuousMap.add_apply,
      ContinuousLinearMap.add_apply] using congrArg₂ (· + ·) hz hw

theorem norm_algebraicTensorFunction_le (z : F ⊗[𝕜] X) :
    ‖algebraicTensorFunction z‖ ≤ ‖tensorPairing 𝕜 F X z‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro φ
  rw [algebraicTensorFunction_apply]
  exact ((tensorPairing 𝕜 F X z).le_opNorm _).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (norm_dualBall_le φ) (norm_nonneg _))

theorem tensorPairing_ker_le_function_ker : LinearMap.ker (tensorPairing 𝕜 F X) ≤
    LinearMap.ker (algebraicTensorFunction (𝕜 := 𝕜) (F := F) (X := X)) := by
  intro z hz
  apply norm_le_zero_iff.mp
  simpa only [LinearMap.mem_ker.mp hz, norm_zero] using norm_algebraicTensorFunction_le z

def tensorFunctionOnRangeLinear : LinearMap.range (tensorPairing 𝕜 F X) →ₗ[𝕜] C(DualBall 𝕜 F, X) :=
  ((LinearMap.ker (tensorPairing 𝕜 F X)).liftQ
    (algebraicTensorFunction (𝕜 := 𝕜) (F := F) (X := X)) tensorPairing_ker_le_function_ker).comp
    (tensorPairing 𝕜 F X).quotKerEquivRange.symm.toLinearMap

@[simp] theorem tensorFunctionOnRangeLinear_image (z : F ⊗[𝕜] X) :
    tensorFunctionOnRangeLinear ⟨tensorPairing 𝕜 F X z, ⟨z, rfl⟩⟩ = algebraicTensorFunction z := by
  simp [tensorFunctionOnRangeLinear]

theorem norm_tensorFunctionOnRangeLinear_le (z : LinearMap.range (tensorPairing 𝕜 F X)) :
    ‖tensorFunctionOnRangeLinear z‖ ≤ ‖z‖ := by
  rcases z with ⟨_, w, rfl⟩
  simpa only [tensorFunctionOnRangeLinear_image, Submodule.coe_norm] using norm_algebraicTensorFunction_le w

def tensorFunctionOnRange : LinearMap.range (tensorPairing 𝕜 F X) →L[𝕜] C(DualBall 𝕜 F, X) :=
  LinearMap.mkContinuous (E := LinearMap.range (tensorPairing 𝕜 F X))
    (F := C(DualBall 𝕜 F, X)) tensorFunctionOnRangeLinear 1
    (fun z => by simpa only [one_mul] using norm_tensorFunctionOnRangeLinear_le z)

def tensorFunction [CompleteSpace X] : InjectiveTensor 𝕜 F X →L[𝕜] C(DualBall 𝕜 F, X) :=
  (tensorFunctionOnRange (𝕜 := 𝕜) (F := F) (X := X)).extend
    (tensorRangeEmbedding (𝕜 := 𝕜) (E := F) (X := X)).toContinuousLinearMap
    tensorRangeEmbedding_dense
    (tensorRangeEmbedding (𝕜 := 𝕜) (E := F) (X := X)).isometry.isUniformInducing

@[simp] theorem tensorFunction_inclusion [CompleteSpace X] (z : F ⊗[𝕜] X) :
    tensorFunction (injectiveInclusion 𝕜 F X z) = algebraicTensorFunction z := by
  have h := ContinuousLinearMap.extend_eq
    (E := LinearMap.range (tensorPairing 𝕜 F X)) (F := C(DualBall 𝕜 F, X))
    (Fₗ := InjectiveTensor 𝕜 F X) (tensorFunctionOnRange (𝕜 := 𝕜) (F := F) (X := X))
    (tensorRangeEmbedding (𝕜 := 𝕜) (E := F) (X := X)).toContinuousLinearMap
    tensorRangeEmbedding_dense
    (tensorRangeEmbedding (𝕜 := 𝕜) (E := F) (X := X)).isometry.isUniformInducing
    ⟨tensorPairing 𝕜 F X z, ⟨z, rfl⟩⟩
  exact h.trans (tensorFunctionOnRangeLinear_image z)

theorem tensorFunction_apply [CompleteSpace X] (z : InjectiveTensor 𝕜 F X) (φ : DualBall 𝕜 F) :
    tensorFunction z φ = leftSlice (WeakDual.toStrongDual φ.val) z := by
  refine injectiveInclusion_dense.induction_on z
    (isClosed_eq ((ContinuousMap.evalCLM 𝕜 φ).continuous.comp tensorFunction.continuous)
      (leftSlice (WeakDual.toStrongDual φ.val)).continuous) ?_
  intro w
  rw [tensorFunction_inclusion]
  exact algebraicTensorFunction_apply w φ

theorem norm_tensorFunction_le [CompleteSpace X] (z : InjectiveTensor 𝕜 F X) :
    ‖tensorFunction (𝕜 := 𝕜) (F := F) (X := X) z‖ ≤ ‖z‖ := by
  refine (injectiveInclusion_dense (𝕜 := 𝕜) (E := F) (X := X)).induction_on z
    (isClosed_le (tensorFunction (𝕜 := 𝕜) (F := F) (X := X)).continuous.norm continuous_norm) ?_
  intro w
  rw [tensorFunction_inclusion]
  exact norm_algebraicTensorFunction_le w

variable [CompleteSpace F] [SeparableSpace F]

def normingDualBall (n : ℕ) : DualBall 𝕜 F :=
  ⟨StrongDual.toWeakDual (normingSequence (𝕜 := 𝕜) (E := F) n), by
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using
      (norm_normingSequence_le (𝕜 := 𝕜) (E := F) n)⟩

theorem norm_tensorFunction [CompleteSpace X] (z : InjectiveTensor 𝕜 F X) : ‖tensorFunction z‖ = ‖z‖ := by
  apply le_antisymm (norm_tensorFunction_le z)
  apply norm_le_of_norming_slices_le z (norm_nonneg _)
  intro n
  have h := (tensorFunction z).norm_coe_le_norm (normingDualBall (𝕜 := 𝕜) (F := F) n)
  rw [tensorFunction_apply] at h
  exact h

def tensorFunctionIsometry [CompleteSpace X] :
    InjectiveTensor 𝕜 F X →ₗᵢ[𝕜] C(DualBall 𝕜 F, X) where
  toLinearMap := tensorFunction.toLinearMap
  norm_map' := norm_tensorFunction

end JFA
