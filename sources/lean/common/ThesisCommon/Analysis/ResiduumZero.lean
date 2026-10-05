import ThesisCommon.Residuum
import ThesisCommon.Analysis.QuotientOperatorZero

noncomputable section
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 800000
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

local instance : HasQuotient (StrongDual 𝕜 (StrongDual 𝕜 E))
    (Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E))) :=
  @Submodule.hasQuotient 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E))
    inferInstance inferInstance inferInstance

theorem residuumOperator_eq_zero_iff (T : E →L[𝕜] F) :
    residuumOperator T = 0 ↔ ∀ ξ, bidualMap T ξ ∈ bidualImage 𝕜 F := by
  have hq := submodule_mapQ_eq_zero_iff (R := 𝕜)
    (M := StrongDual 𝕜 (StrongDual 𝕜 E)) (N := StrongDual 𝕜 (StrongDual 𝕜 F))
    (bidualImage 𝕜 E) (bidualImage 𝕜 F) (bidualMap T).toLinearMap
    (bidual_preserves_image T)
  constructor
  · intro h
    exact hq.mp (congrArg ContinuousLinearMap.toLinearMap h)
  · intro h
    exact ContinuousLinearMap.coe_injective (hq.mpr h)

end ThesisCommon
