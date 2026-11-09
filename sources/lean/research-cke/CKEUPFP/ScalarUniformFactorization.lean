import CKEUPFP.ScalarEllpNoCZero
import CKEUPFP.VendorDefinitions
import ThesisCommon.Analysis.ScalarLpPrimary
import ThesisCommon.Analysis.IntervalLpUniformFactorization

/-! Scalar uniform factorisation inputs, with their complete proved source
closure and exact definition translation. The p = 1 endpoint is included. -/

noncomputable section

open scoped ENNReal

namespace CKEUPFP

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Away from p = 1, the scalar lp reduction supplies the explicit constant 8. -/
theorem scalarEllp_hasCPFP_eight (p : FiniteBanachExponent)
    (hp1 : 1 < p.val.toReal) : HasCPFP 𝕜 (ScalarEllp 𝕜 p) 8 :=
  (hasCPFP_iff_vendor 8).mpr
    ⟨by norm_num, ThesisCommon.scalar_lp_finite_hasCPFP p.property.2.ne hp1⟩

/-- Scalar ℓp has UPFP for every exponent in the corollary, including p = 1. -/
theorem scalarEllp_hasUPFP (p : FiniteBanachExponent) :
    HasUPFP 𝕜 (ScalarEllp 𝕜 p) :=
  hasUPFP_iff_vendor.mpr (ThesisCommon.scalar_lp_hasUPFP p.val)

/-- Actual Lebesgue Lp[0,1] has UPFP for every finite Banach exponent. -/
theorem intervalLp_hasUPFP (p : FiniteBanachExponent) :
    HasUPFP 𝕜 (IntervalLp 𝕜 p) := by
  let q : ThesisCommon.BanachExponent := ⟨p.val, p.property.1⟩
  exact hasUPFP_iff_vendor.mpr (ThesisCommon.intervalLp_hasUPFP 𝕜 q p.property.2.ne)

theorem intervalLp_containsNoCZero (p : FiniteBanachExponent) :
    ContainsNoCZero 𝕜 (IntervalLp 𝕜 p) := scalarLp_containsNoCZero p.property.2.ne

end CKEUPFP
