import JFA.TensorFunction

/-! The concrete injective tensor of C(M) and X maps isometrically to C(M,X).
Point evaluations define the map. Dual contractions prove the reverse norm
bound without assuming an integral representation of the dual of C(M). -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace Topology
open scoped TensorProduct
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {M : Type*} [TopologicalSpace M] [CompactSpace M]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem norm_compactEvaluation_le (m : M) :
    ‖(ContinuousMap.evalCLM 𝕜 m : C(M, 𝕜) →L[𝕜] 𝕜)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using f.norm_coe_le_norm m

def compactDualEvaluation (m : M) : DualBall 𝕜 C(M, 𝕜) :=
  ⟨StrongDual.toWeakDual (ContinuousMap.evalCLM 𝕜 m), by
    change dist (ContinuousMap.evalCLM 𝕜 m : C(M, 𝕜) →L[𝕜] 𝕜) 0 ≤ 1
    rw [(inferInstance : NormedAddCommGroup (C(M, 𝕜) →L[𝕜] 𝕜)).dist_eq, sub_zero]
    exact norm_compactEvaluation_le m⟩

theorem continuous_compactDualEvaluation :
    Continuous (compactDualEvaluation (𝕜 := 𝕜) (M := M)) := by
  apply Continuous.subtype_mk
  apply WeakDual.continuous_of_continuous_eval
  intro f
  exact f.continuous

def compactEvaluationPullback : C(DualBall 𝕜 C(M, 𝕜), X) →L[𝕜] C(M, X) :=
  LinearMap.mkContinuous (E := C(DualBall 𝕜 C(M, 𝕜), X)) (F := C(M, X)) {
    toFun := fun f => f.comp ⟨compactDualEvaluation, continuous_compactDualEvaluation⟩
    map_add' := by intro f g; ext m; rfl
    map_smul' := by intro a f; ext m; rfl }
    1 (fun f => by
      rw [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg f)).mpr fun m =>
        f.norm_coe_le_norm (compactDualEvaluation (𝕜 := 𝕜) m))

def tensorContinuousFunction : InjectiveTensor 𝕜 C(M, 𝕜) X →L[𝕜] C(M, X) :=
  compactEvaluationPullback.comp tensorFunction

theorem tensorContinuousFunction_apply (z : InjectiveTensor 𝕜 C(M, 𝕜) X) (m : M) :
    tensorContinuousFunction z m = leftSlice (ContinuousMap.evalCLM 𝕜 m) z :=
  tensorFunction_apply z (compactDualEvaluation m)

@[simp] theorem tensorContinuousFunction_pure (f : C(M, 𝕜)) (x : X) (m : M) :
    tensorContinuousFunction (injectivePure 𝕜 C(M, 𝕜) X f x) m = f m • x := by
  rw [tensorContinuousFunction_apply, leftSlice_pure]
  rfl

theorem norm_tensorContinuousFunction_le (z : InjectiveTensor 𝕜 C(M, 𝕜) X) :
    ‖tensorContinuousFunction z‖ ≤ ‖z‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg z)).mpr
  intro m
  change ‖tensorFunction z (compactDualEvaluation m)‖ ≤ ‖z‖
  exact ((tensorFunction z).norm_coe_le_norm _).trans (norm_tensorFunction_le z)

theorem norm_rightSlice_continuous_le (z : InjectiveTensor 𝕜 C(M, 𝕜) X)
    (ψ : X →L[𝕜] 𝕜) : ‖rightSlice ψ z‖ ≤ ‖ψ‖ * ‖tensorContinuousFunction z‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro m
  have hpair := rightSlice_pairing ψ (ContinuousMap.evalCLM 𝕜 m) z
  change rightSlice ψ z m = ψ (leftSlice (ContinuousMap.evalCLM 𝕜 m) z) at hpair
  rw [hpair, ← tensorContinuousFunction_apply]
  exact (ψ.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    ((tensorContinuousFunction z).norm_coe_le_norm m) (norm_nonneg ψ))

theorem norm_tensorContinuousFunction (z : InjectiveTensor 𝕜 C(M, 𝕜) X) :
    ‖tensorContinuousFunction z‖ = ‖z‖ := by
  apply le_antisymm (norm_tensorContinuousFunction_le z)
  change ‖z.val‖ ≤ ‖tensorContinuousFunction z‖
  apply (dualOperator_norm_le_iff z.val _ (norm_nonneg _)).mpr
  intro φ ψ
  have hpair := rightSlice_pairing ψ φ z
  change φ (rightSlice ψ z) = ψ (z.val φ) at hpair
  rw [← hpair]
  calc
    ‖φ (rightSlice ψ z)‖ ≤ ‖φ‖ * ‖rightSlice ψ z‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ * (‖ψ‖ * ‖tensorContinuousFunction z‖) :=
      mul_le_mul_of_nonneg_left (norm_rightSlice_continuous_le z ψ) (norm_nonneg φ)
    _ = (‖tensorContinuousFunction z‖ * ‖φ‖) * ‖ψ‖ := by ring

def tensorContinuousIsometry : InjectiveTensor 𝕜 C(M, 𝕜) X →ₗᵢ[𝕜] C(M, X) where
  toLinearMap := tensorContinuousFunction.toLinearMap
  norm_map' := norm_tensorContinuousFunction

end JFA
