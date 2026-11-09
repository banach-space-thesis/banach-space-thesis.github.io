import CKEUPFP.MixedUPFP
import CKEUPFP.ContinuousMapPrimary

/-!
# The mixed scalar-space corollary

The scalar UPFP inputs are genuine proved results about mathlib's lp and Lp
spaces, imported with their audited source closure. Their operator equations,
norm bounds, and quantifier order agree with the paper's definitions through
the definitional equivalences in VendorDefinitions. No-c₀ and separability
are proved independently for the actual spaces. Primariness uses the proved
c₀ self-similarity and Pełczyński decomposition, rather than an unrestricted
implication from UPFP to primariness.
-/

noncomputable section

open scoped ENNReal

namespace CKEUPFP

/-- Corollary 1.2, with the complete printed exponent range. -/
theorem mixedSpacePrimariness (𝕜 : Type*) [RCLike 𝕜] : MixedSpacePrimariness 𝕜 := by
  intro p
  letI : Uncountable UnitInterval := unitInterval_uncountable
  exact ⟨continuousMap_isPrimary_of_hasUPFP UnitInterval (ScalarEllp 𝕜 p)
      (mixedSpaceUPFP 𝕜 p).1,
    continuousMap_isPrimary_of_hasUPFP UnitInterval (IntervalLp 𝕜 p)
      (mixedSpaceUPFP 𝕜 p).2⟩

end CKEUPFP
