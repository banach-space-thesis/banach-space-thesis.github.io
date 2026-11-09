import SurveyStatements.P4Gantmacher

/-! Necessity of weak compactness for the stated reflexive factorization,
using surjectivity of the actual normed bidual embedding. -/

noncomputable section
set_option autoImplicit false

namespace SurveyStatements.P4

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- A bounded operator factoring through a reflexive Banach space with a
Schauder basis is weakly compact. No approximation hypotheses are required. -/
theorem FactorsThroughReflexiveBasisSpace.weaklyCompact
    {T : X →L[𝕜] Y} (h : FactorsThroughReflexiveBasisSpace 𝕜 T) :
    IsWeaklyCompactOperator 𝕜 T := by
  obtain ⟨V, A, B, hT⟩ := h
  have hid : IsWeaklyCompactOperator 𝕜 (ContinuousLinearMap.id 𝕜 V.Carrier) :=
    reflexive_iff_weaklyCompact_id.mp V.reflexive
  have hA : IsWeaklyCompactOperator 𝕜 A := by
    simpa only [ContinuousLinearMap.id_comp] using hid.comp_right A
  simpa only [hT] using hA.comp_left B

end SurveyStatements.P4
