import CKEUPFP.Transfer
import CKEUPFP.ScalarUniformFactorization
import CKEUPFP.ScalarSpaceSeparable

/-! Applying the fully proved main transfer theorem to the actual scalar
ℓp and Lebesgue Lp[0,1] spaces for every finite Banach exponent. -/

noncomputable section

namespace CKEUPFP

/-- Both mixed continuous-function spaces have UPFP for all 1 ≤ p < ∞. -/
theorem mixedSpaceUPFP (𝕜 : Type*) [RCLike 𝕜] : MixedSpaceUPFP 𝕜 := by
  intro p
  letI : Uncountable UnitInterval := unitInterval_uncountable
  constructor
  · letI := scalarEllp_separableSpace (𝕜 := 𝕜) p
    exact transferTheorem 𝕜 UnitInterval (ScalarEllp 𝕜 p)
      (scalarEllp_containsNoCZero p) (scalarEllp_hasUPFP p)
  · letI := intervalLp_separableSpace (𝕜 := 𝕜) p
    exact transferTheorem 𝕜 UnitInterval (IntervalLp 𝕜 p)
      (intervalLp_containsNoCZero p) (intervalLp_hasUPFP p)

end CKEUPFP
