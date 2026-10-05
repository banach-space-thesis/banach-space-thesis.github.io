import ThesisCommon.Analysis.AdjointWeakEssentialNorm
import ThesisCommon.Analysis.WeakEssentialNormProperties

/-! Pulling an adjoint approximant back through an actual contractive bidual
retraction preserves its error. This proves equality of primal and dual weak
essential norms and transports an attained dual distance. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
namespace ThesisCommon
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

local instance bidualRetractionNormedAddCommGroup : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := StrongDual 𝕜 E) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)
local instance bidualRetractionNormedSpace : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ContinuousLinearMap.toNormedSpace (𝕜' := 𝕜) (E := StrongDual 𝕜 E) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)

def adjointApproximationPullback
    (P : StrongDual 𝕜 (StrongDual 𝕜 F) →L[𝕜] F)
    (S : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) : E →L[𝕜] F :=
  P.comp ((banachAdjoint S).comp (NormedSpace.inclusionInDoubleDual 𝕜 E))

theorem weaklyCompact_adjointApproximationPullback
    (P : StrongDual 𝕜 (StrongDual 𝕜 F) →L[𝕜] F)
    {S : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E} (hS : IsWeaklyCompactOperator S) :
    IsWeaklyCompactOperator (adjointApproximationPullback P S) :=
  (hS.banachAdjoint.comp_right _).comp_left P

theorem norm_sub_adjointApproximationPullback_le
    (P : StrongDual 𝕜 (StrongDual 𝕜 F) →L[𝕜] F)
    (hP : ‖P‖ ≤ 1) (hPJ : ∀ y, P (NormedSpace.inclusionInDoubleDual 𝕜 F y) = y)
    (T : E →L[𝕜] F) (S : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) :
    ‖T - adjointApproximationPullback P S‖ ≤ ‖banachAdjoint T - S‖ := by
  have heq : T - adjointApproximationPullback P S =
      P.comp ((banachAdjoint (banachAdjoint T - S)).comp
        (NormedSpace.inclusionInDoubleDual 𝕜 E)) := by
    ext x
    rw [banachAdjoint_sub]
    change T x - P (banachAdjoint S (NormedSpace.inclusionInDoubleDual 𝕜 E x)) =
      P (NormedSpace.inclusionInDoubleDual 𝕜 F (T x) -
        banachAdjoint S (NormedSpace.inclusionInDoubleDual 𝕜 E x))
    rw [map_sub, hPJ]
  rw [heq]
  calc
    _ ≤ ‖P‖ * ‖(banachAdjoint (banachAdjoint T - S)).comp
        (NormedSpace.inclusionInDoubleDual 𝕜 E)‖ := P.opNorm_comp_le _
    _ ≤ ‖(banachAdjoint (banachAdjoint T - S)).comp
        (NormedSpace.inclusionInDoubleDual 𝕜 E)‖ := mul_le_of_le_one_left (norm_nonneg _) hP
    _ ≤ ‖banachAdjoint (banachAdjoint T - S)‖ *
        ‖NormedSpace.inclusionInDoubleDual 𝕜 E‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖banachAdjoint (banachAdjoint T - S)‖ :=
      mul_le_of_le_one_right (norm_nonneg _) (NormedSpace.inclusionInDoubleDual_norm_le 𝕜 E)
    _ = _ := norm_banachAdjoint _

theorem weakEssentialNorm_banachAdjoint_eq_of_bidual_retraction
    (P : StrongDual 𝕜 (StrongDual 𝕜 F) →L[𝕜] F)
    (hP : ‖P‖ ≤ 1) (hPJ : ∀ y, P (NormedSpace.inclusionInDoubleDual 𝕜 F y) = y)
    (T : E →L[𝕜] F) : weakEssentialNorm (banachAdjoint T) = weakEssentialNorm T := by
  apply le_antisymm (weakEssentialNorm_banachAdjoint_le T)
  apply le_csInf
  · exact ⟨_, 0, weaklyCompact_zero, rfl⟩
  · rintro r ⟨S, hS, rfl⟩
    exact (weakEssentialNorm_le T (weaklyCompact_adjointApproximationPullback P hS)).trans
      (norm_sub_adjointApproximationPullback_le P hP hPJ T S)

theorem exists_best_weaklyCompact_of_adjoint_attainment
    (P : StrongDual 𝕜 (StrongDual 𝕜 F) →L[𝕜] F)
    (hP : ‖P‖ ≤ 1) (hPJ : ∀ y, P (NormedSpace.inclusionInDoubleDual 𝕜 F y) = y)
    (T : E →L[𝕜] F)
    (hatt : ∃ S : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E,
      IsWeaklyCompactOperator S ∧ ‖banachAdjoint T - S‖ = weakEssentialNorm (banachAdjoint T)) :
    ∃ W : E →L[𝕜] F, IsWeaklyCompactOperator W ∧ ‖T - W‖ = weakEssentialNorm T := by
  obtain ⟨S, hS, he⟩ := hatt
  have hW := weaklyCompact_adjointApproximationPullback P hS
  refine ⟨adjointApproximationPullback P S, hW, le_antisymm ?_ (weakEssentialNorm_le T hW)⟩
  exact (norm_sub_adjointApproximationPullback_le P hP hPJ T S).trans_eq
    (he.trans (weakEssentialNorm_banachAdjoint_eq_of_bidual_retraction P hP hPJ T))

end ThesisCommon
