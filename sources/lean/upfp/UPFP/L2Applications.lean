import UPFP.PreservationTheorem
import ThesisCommon.Analysis.IntervalL2HaarHilbert
import ThesisCommon.Analysis.IntervalLpFunctionSelfSimilarity

/-! The p=2 part of the original finite-exponent application, using the
actual normalized Haar Hilbert representation and actual L2 self-similarity. -/
noncomputable section
namespace UPFP
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem corollary_1_3_L2 :
    HasUPFP 𝕜 (EllInfinitySum (IntervalLp 𝕜 ⟨2, by norm_num⟩)) ∧
      IsPrimary 𝕜 (EllInfinitySum (IntervalLp 𝕜 ⟨2, by norm_num⟩)) := by
  have h := theorem_1_2_finiteLpSelfSimilar (intervalL2_hasUPFP 𝕜)
    (intervalLpFunction_isFiniteLpSelfSimilar 𝕜 ⟨2, by norm_num⟩ (by simp))
  exact ⟨h.1.2, h.2.2⟩

end UPFP
