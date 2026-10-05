import ThesisCommon.Analysis.AdjointWeakCompact
import ThesisCommon.Analysis.BanachAdjointAlgebra

noncomputable section
set_option synthInstance.maxSize 1024
namespace ThesisCommon
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem weakEssentialNorm_banachAdjoint_le (T : E →L[𝕜] F) :
    weakEssentialNorm (banachAdjoint T) ≤ weakEssentialNorm T := by
  apply le_csInf
  · exact ⟨‖T - 0‖, 0, weaklyCompact_zero, rfl⟩
  · rintro r ⟨W, hW, rfl⟩
    calc
      weakEssentialNorm (banachAdjoint T) ≤ ‖banachAdjoint T - banachAdjoint W‖ :=
        weakEssentialNorm_le _ hW.banachAdjoint
      _ = ‖banachAdjoint (T - W)‖ := by rw [banachAdjoint_sub]
      _ = ‖T - W‖ := norm_banachAdjoint _

end ThesisCommon
