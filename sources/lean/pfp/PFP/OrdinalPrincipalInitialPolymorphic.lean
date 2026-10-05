import PFP.OrdinalRegularInitialQuantitative
import Posets.OrdinalClosedCopyInitialPowers
import ThesisCommon.Analysis.PrimaryIsomorphism

/-! The initial-rank principal branch in arbitrary ordinal and scalar universes.
The regular initial-ordinal factorisation is proved by the actual row selection;
the power identity is ordinal arithmetic, with no classification premise. -/
noncomputable section
namespace Posets
open ThesisCommon
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

theorem ordinalPrincipalInitialRank_hasUPFP_poly (γ : Ordinal.{u})
    (hc : Cardinal.aleph0 < γ.cof) (hγ : γ = γ.cof.ord) :
    HasUPFP 𝕜 (JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ)) := by
  have hregular : γ.cof.IsRegular :=
    Cardinal.isRegular_cof (Ordinal.aleph0_le_cof.mp hc.le)
  have he : Ordinal.omega0 ^ γ = γ.cof.ord := calc
    Ordinal.omega0 ^ γ = Ordinal.omega0 ^ γ.cof.ord := congrArg (Ordinal.omega0 ^ ·) hγ
    _ = γ.cof.ord := ordinal_uncountable_initial_omega_power hc
  exact (initialOrdinal_hasUPFP_poly (𝕜 := 𝕜) hregular hc).of_equiv
    (JLMS.ordinalSpaceCongrIsometry (𝕜 := 𝕜) he).symm.toContinuousLinearEquiv

end Posets
