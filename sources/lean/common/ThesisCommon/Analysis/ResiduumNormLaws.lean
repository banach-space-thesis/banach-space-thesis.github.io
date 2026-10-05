import ThesisCommon.Analysis.ResiduumProperties
import ThesisCommon.Analysis.WeakCompactClosed
import ThesisCommon.Analysis.SeminormedOperatorZero

/-! The residuum norm is a seminorm whose kernel is precisely the weakly
compact ideal for a complete range space. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
namespace ThesisCommon
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

local instance : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := StrongDual 𝕜 E) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)

local instance : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ContinuousLinearMap.toNormedSpace (𝕜' := 𝕜) (E := StrongDual 𝕜 E) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)

theorem residuumNorm_add_le (S T : E →L[𝕜] F) :
    residuumNorm (S + T) ≤ residuumNorm S + residuumNorm T := by
  rw [residuumNorm_eq_norm, residuumOperator_add, residuumNorm_eq_norm, residuumNorm_eq_norm]
  exact norm_add_le _ _

theorem residuumNorm_smul (a : 𝕜) (T : E →L[𝕜] F) :
    residuumNorm (a • T) = ‖a‖ * residuumNorm T := by
  letI : NormSMulClass 𝕜 (ResiduumSpace 𝕜 E →L[𝕜] ResiduumSpace 𝕜 F) :=
    NormedSpace.toNormSMulClass (𝕜 := 𝕜) (E := ResiduumSpace 𝕜 E →L[𝕜] ResiduumSpace 𝕜 F)
  rw [residuumNorm_eq_norm, residuumOperator_smul, residuumNorm_eq_norm]
  exact norm_smul a (residuumOperator T)

theorem residuumNorm_eq_zero_iff [CompleteSpace F] (T : E →L[𝕜] F) :
    residuumNorm T = 0 ↔ IsWeaklyCompactOperator T := by
  letI : IsClosed (bidualImage 𝕜 F : Set (StrongDual 𝕜 (StrongDual 𝕜 F))) :=
    isClosed_bidualImage (𝕜 := 𝕜) (F := F)
  rw [residuumNorm_eq_norm]
  exact (opNorm_eq_zero_iff_of_seminormed_domain (𝕜 := 𝕜)
    (A := ResiduumSpace 𝕜 E) (B := ResiduumSpace 𝕜 F) (residuumOperator T)).trans
    (gantmacher_iff_residuum_eq_zero T).symm

end ThesisCommon
