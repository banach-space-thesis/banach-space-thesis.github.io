import ThesisCommon.Analysis.ExtremallyDisconnectedCKRetraction
import ThesisCommon.Analysis.BidualRetractionApproximation

/-! Adjoint weak-essential norm equality for actual operators into C(K),
for extremally disconnected compact Hausdorff K. The contractive bidual
retraction is constructed, not supplied as an additional hypothesis. -/
noncomputable section
set_option synthInstance.maxSize 1024
namespace ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
variable [ExtremallyDisconnected K]

theorem weakEssentialNorm_banachAdjoint_eq_continuousMap (T : E →L[𝕜] C(K, 𝕜)) :
    weakEssentialNorm (banachAdjoint T) = weakEssentialNorm T := by
  obtain ⟨P, hP, hPJ⟩ := exists_continuousMap_bidual_retraction (𝕜 := 𝕜) (K := K)
  exact weakEssentialNorm_banachAdjoint_eq_of_bidual_retraction P hP hPJ T

theorem exists_continuousMap_bestApproximation_of_adjoint_attainment
    (T : E →L[𝕜] C(K, 𝕜))
    (hatt : ∃ S : StrongDual 𝕜 C(K, 𝕜) →L[𝕜] StrongDual 𝕜 E,
      IsWeaklyCompactOperator (𝕜 := 𝕜) (E := StrongDual 𝕜 C(K, 𝕜))
        (F := StrongDual 𝕜 E) S ∧
        ‖banachAdjoint T - S‖ = weakEssentialNorm (banachAdjoint T)) :
    ∃ W : E →L[𝕜] C(K, 𝕜), IsWeaklyCompactOperator W ∧ ‖T - W‖ = weakEssentialNorm T := by
  obtain ⟨P, hP, hPJ⟩ := exists_continuousMap_bidual_retraction (𝕜 := 𝕜) (K := K)
  exact exists_best_weaklyCompact_of_adjoint_attainment P hP hPJ T hatt

end ThesisCommon
