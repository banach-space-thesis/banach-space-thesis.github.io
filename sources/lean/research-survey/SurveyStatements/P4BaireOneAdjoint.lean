import SurveyStatements.P4BaireAdjointImage
import SurveyStatements.P4CompactInterpolation
import SurveyStatements.P4TailConvexRadial

/-! Genuine norm Baire class one of a weakly compact adjoint. The continuous
approximants come from compact finite interpolation followed by the inverse
isometry's continuous extension. -/

noncomputable section
set_option autoImplicit false

open Set Filter Topology TopologicalSpace

namespace SurveyStatements.P4

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [SeparableSpace Y]

/-- The adjoint on the entire weak-star dual is an actual pointwise norm
limit of norm-continuous maps. -/
theorem weaklyCompact_adjoint_isNormBaireOne (T : X →L[𝕜] Y)
    (hT : IsWeaklyCompactOperator 𝕜 T) :
    IsNormBaireOne (fun φ : WeakDual 𝕜 Y =>
      banachAdjoint T (WeakDual.toStrongDual φ)) := by
  let W := weakClosureImage T
  letI : CompactSpace W := isCompact_iff_compactSpace.mp hT
  letI : MetrizableSpace W := weakCompact_metrizable hT
  letI : MetricSpace W := metrizableSpaceMetric W
  let F : WeakDual 𝕜 Y → C(W, 𝕜) := fun φ =>
    weakClosureRestriction T (WeakDual.toStrongDual φ)
  have hF : ∀ w, Continuous (fun φ => F φ w) := fun w =>
    WeakDual.eval_continuous ((toWeakSpace 𝕜 Y).symm w.val)
  obtain ⟨u, hu⟩ := exists_continuous_pointwise_norm_approximants F hF
  obtain ⟨G, hG⟩ := weaklyCompact_adjoint_inverse_extension T hT
  refine ⟨fun n => G.comp (u n), ?_⟩
  intro φ
  have h := (G.continuous.tendsto (F φ)).comp (hu φ)
  simpa only [ContinuousMap.comp_apply, F, hG] using h

/-- Restriction to any weak-star parameter subset preserves the actual
pointwise continuous norm approximation. -/
theorem weaklyCompact_adjoint_isNormBaireOne_on (T : X →L[𝕜] Y)
    (hT : IsWeaklyCompactOperator 𝕜 T) (K : Set (WeakDual 𝕜 Y)) :
    IsNormBaireOne (fun φ : K => banachAdjoint T (WeakDual.toStrongDual φ.val)) := by
  obtain ⟨u, hu⟩ := weaklyCompact_adjoint_isNormBaireOne T hT
  refine ⟨fun n => ⟨fun φ => u n φ.val, (u n).continuous.comp continuous_subtype_val⟩, ?_⟩
  intro φ
  exact hu φ.val

end SurveyStatements.P4
