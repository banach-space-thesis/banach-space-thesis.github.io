import SurveyStatements.P4Gantmacher
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Lemmas

/-! Finite-dimensional normed spaces have the required continuous-dual reflexivity. -/

noncomputable section
set_option autoImplicit false

open Set Metric

namespace SurveyStatements.P4

universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem finiteDimensional_reflexive [FiniteDimensional 𝕜 E] :
    IsReflexiveNormedSpace 𝕜 E := by
  letI : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
  apply reflexive_iff_weaklyCompact_id.mpr
  apply (weaklyCompact_iff_compact_cover (ContinuousLinearMap.id 𝕜 E)).mpr
  refine ⟨(toWeakSpace 𝕜 E) '' closedBall (0 : E) 1,
    (isCompact_closedBall (0 : E) 1).image (toWeakSpaceCLM 𝕜 E).continuous, ?_⟩
  intro x hx
  exact ⟨x, mem_closedBall_zero_iff.mpr hx, rfl⟩

end SurveyStatements.P4
