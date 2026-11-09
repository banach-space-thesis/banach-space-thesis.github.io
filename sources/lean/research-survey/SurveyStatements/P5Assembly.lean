import SurveyStatements.P5CancellativeCopy
import SurveyStatements.P5BoundedAssembly
import SurveyStatements.P5Primary

/-! Final assembly on the actual mixed Bochner space. A proved bounded
cancellative copy gives a sufficient uniform bound 48. The source's sharper
bound 12 follows from its sharper norm-one copy; the main statement only
requires some common bound. The scalar-compression premise is still a separate
proof obligation on the actual two-kernel space. -/

noncomputable section
set_option autoImplicit false
open scoped ENNReal

namespace SurveyStatements.P5
attribute [local irreducible] vectorLpBlockEquiv vectorLpAffine

variable (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

theorem mixedNorm_uniformPrimaryFactorization_of_scalarCompression (hp : p ≠ ∞)
    (h : HasScalarCompression 𝕜 (DoublyZeroMean 𝕜 p)) :
    HasUniformPrimaryFactorization 𝕜 (MixedNorm 𝕜 p) := by
  exact uniformPrimaryFactorization_of_bounded_cancellative_compression h
    (cancellativeProjection 𝕜 p) (DoublyZeroMean 𝕜 p).subtypeL
    (cancellativeProjection_retraction 𝕜 p)
    (cancellativeCopyInjection 𝕜 p hp) (cancellativeCopyRetraction 𝕜 p hp)
    (cancellativeCopy_retraction 𝕜 p hp)
    (norm_cancellativeProjection_le 𝕜 p) (norm_cancellativeInclusion_le 𝕜 p)
    (norm_cancellativeCopyInjection_le 𝕜 p hp) (norm_cancellativeCopyRetraction_le 𝕜 p hp)

end SurveyStatements.P5
