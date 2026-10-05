import Posets.OrdinalIdealTransportRegularQuantitative
import Posets.OrdinalClosedCopyInitialPowers

/-! The initial-rank branch uses the proved regular-initial operator theorem
and the actual ordinal fixed-point identity. -/

noncomputable section
namespace Posets
open ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace

theorem ordinalPrincipalInitialRank_hasUPFP (γ : Ordinal.{0})
    (hc : Cardinal.aleph0 < γ.cof) (hγ : γ = γ.cof.ord) :
    HasUPFP 𝕜 (JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ)) := by
  have hregular : γ.cof.IsRegular :=
    Cardinal.isRegular_cof (Ordinal.aleph0_le_cof.mp hc.le)
  have he : Ordinal.omega0 ^ γ = γ.cof.ord := calc
    Ordinal.omega0 ^ γ = Ordinal.omega0 ^ γ.cof.ord := congrArg (Ordinal.omega0 ^ ·) hγ
    _ = γ.cof.ord := ordinal_uncountable_initial_omega_power hc
  exact (initialOrdinal_hasUPFP (𝕜 := 𝕜) hregular hc).of_equiv
    (JLMS.ordinalSpaceCongrIsometry (𝕜 := 𝕜) he).symm.toContinuousLinearEquiv

end Posets

