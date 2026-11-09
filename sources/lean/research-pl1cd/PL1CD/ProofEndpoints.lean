import PL1CD.StageSeparation
import PL1CD.StageRangeGeometry

noncomputable section

namespace PL1CD

variable (𝕜 : Type) [RCLike 𝕜]

theorem theoremsCDStrong_of_stageAnalyticSeparation (h : StageAnalyticSeparation 𝕜) :
    TheoremsCDStrongStatement 𝕜 :=
  ⟨stageProjectionFamily 𝕜, generatedIdeal 𝕜 (stageProjectionFamily 𝕜),
    h.theoremCSpec, stageProjectionFamily_additionalStrongSpec 𝕜,
    h.idealSeparationData.orderSpec (stageProjectionFamily_range_schur 𝕜),
    stageProjectionFamily_idealAdditionalSpec 𝕜, h.idealSeparationData.cardinality⟩

theorem theoremCReal_of_stageAnalyticSeparation (h : StageAnalyticSeparation ℝ) :
    TheoremCRealStatement := h.theoremC

theorem theoremCComplex_of_stageAnalyticSeparation (h : StageAnalyticSeparation ℂ) :
    TheoremCComplexStatement := h.theoremC

theorem theoremDReal_of_stageAnalyticSeparation (h : StageAnalyticSeparation ℝ) :
    TheoremDRealStatement := h.theoremD

theorem theoremDComplex_of_stageAnalyticSeparation (h : StageAnalyticSeparation ℂ) :
    TheoremDComplexStatement := h.theoremD

end PL1CD
