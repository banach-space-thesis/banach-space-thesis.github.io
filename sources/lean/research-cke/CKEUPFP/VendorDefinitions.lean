import CKEUPFP.Definitions
import ThesisCommon.Analysis.Primary

/-! Exact translation of the audited shared factorisation vocabulary.
The shared CPFP predicate places the requirement C ≥ 1 in UPFP, whereas
the paper's CPFP predicate here includes it directly. All operator equations
and norm products agree definitionally. -/

noncomputable section

namespace CKEUPFP

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem vendor_factorsIdentity_iff (T : X →L[𝕜] Y) :
    ThesisCommon.FactorsIdentity T Z ↔
      FactorsThrough (ContinuousLinearMap.id 𝕜 Z) T := Iff.rfl

theorem vendor_factorsIdentityWith_iff (T : X →L[𝕜] Y) (C : ℝ) :
    ThesisCommon.FactorsIdentityWith T Z C ↔
      FactorsThroughWith (ContinuousLinearMap.id 𝕜 Z) T C := Iff.rfl

theorem hasPFP_iff_vendor : HasPFP 𝕜 X ↔ ThesisCommon.HasPFP 𝕜 X := Iff.rfl

theorem hasCPFP_iff_vendor (C : ℝ) :
    HasCPFP 𝕜 X C ↔ 1 ≤ C ∧ ThesisCommon.HasCPFP 𝕜 X C := Iff.rfl

theorem hasUPFP_iff_vendor : HasUPFP 𝕜 X ↔ ThesisCommon.HasUPFP 𝕜 X := Iff.rfl

theorem isPrimary_iff_vendor : IsPrimary 𝕜 X ↔ ThesisCommon.IsPrimary 𝕜 X := Iff.rfl

end CKEUPFP
