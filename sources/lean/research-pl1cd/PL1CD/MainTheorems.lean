import PL1CD.RangeVanishing
import PL1CD.StageGrowth
import PL1CD.ProofEndpoints

noncomputable section

namespace PL1CD
variable (K : Type) [RCLike K]

theorem stageAnalyticSeparation : StageAnalyticSeparation K := by
  constructor
  intro a b hab T
  exact Variation.interval_range_vanishing K
    (StageParameters.rates (AlmostDisjoint.family b))
    StageParameters.filtration StageParameters.levels
    (AlmostDisjoint.family a) (AlmostDisjoint.family_infinite a)
    (stage_growthCriterion _ _ (AlmostDisjoint.family_inter_finite hab)) T

theorem theoremC : TheoremCStatement K := (stageAnalyticSeparation K).theoremC

theorem theoremD : TheoremDStatement K := (stageAnalyticSeparation K).theoremD

theorem theoremsCDStrong : TheoremsCDStrongStatement K :=
  theoremsCDStrong_of_stageAnalyticSeparation K (stageAnalyticSeparation K)

theorem theoremCReal : TheoremCRealStatement := theoremC ℝ
theorem theoremCComplex : TheoremCComplexStatement := theoremC ℂ
theorem theoremDReal : TheoremDRealStatement := theoremD ℝ
theorem theoremDComplex : TheoremDComplexStatement := theoremD ℂ
theorem theoremsCDRealStrong : TheoremsCDRealStrongStatement := theoremsCDStrong ℝ
theorem theoremsCDComplexStrong : TheoremsCDComplexStrongStatement := theoremsCDStrong ℂ

end PL1CD
