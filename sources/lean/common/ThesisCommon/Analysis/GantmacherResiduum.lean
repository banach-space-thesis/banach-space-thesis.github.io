import ThesisCommon.Analysis.Gantmacher
import ThesisCommon.Analysis.ResiduumZero

noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem gantmacher_iff_residuum_eq_zero (T : E →L[𝕜] F) :
    IsWeaklyCompactOperator T ↔ residuumOperator T = 0 :=
  (gantmacher_iff_bidual_mem_image T).trans (residuumOperator_eq_zero_iff T).symm

end ThesisCommon
