import PFP.UncountableCofinalOrdinalCoefficientProofs
import PFP.OrdinalRegularInitialQuantitative
import Posets.OrdinalClosedCopyInitialPowers

/-! The complete principal-rank coefficient theorem. The regular initial
rank is transported along the actual ordinal fixed-point identity; all
other ranks use the checked countable or transfinite selection theorem.
Scalar and ordinal universes are independent. -/
noncomputable section
namespace PFP
open ThesisCommon
universe u
variable (𝕜 : Type*) [RCLike 𝕜]

theorem ordinalContinuous_hasUPFP_of_principal_initial_rank
    (γ : Ordinal.{u}) (hc : Cardinal.aleph0 < γ.cof) (hγ : γ = γ.cof.ord) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 (Ordinal.omega0 ^ γ)) := by
  have hregular : γ.cof.IsRegular :=
    Cardinal.isRegular_cof (Ordinal.aleph0_le_cof.mp hc.le)
  have he : Ordinal.omega0 ^ γ = γ.cof.ord := calc
    Ordinal.omega0 ^ γ = Ordinal.omega0 ^ γ.cof.ord := congrArg (Ordinal.omega0 ^ ·) hγ
    _ = γ.cof.ord := Posets.ordinal_uncountable_initial_omega_power hc
  exact (Posets.initialOrdinal_hasUPFP_poly (𝕜 := 𝕜) hregular hc).of_equiv
    (JLMS.ordinalSpaceCongrIsometry (𝕜 := 𝕜) he).symm.toContinuousLinearEquiv

theorem ordinalContinuous_hasUPFP_of_principal_rank
    (γ : Ordinal.{u}) (hP : Ordinal.Principal (· + ·) γ)
    (hω : Ordinal.omega0 < γ) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 (Ordinal.omega0 ^ γ)) := by
  by_cases hi : γ = γ.cof.ord
  · apply ordinalContinuous_hasUPFP_of_principal_initial_rank 𝕜 γ ?_ hi
    exact Cardinal.ord_lt_ord.mp (by simpa only [Cardinal.ord_aleph0, ← hi] using hω)
  · exact ordinalContinuous_hasUPFP_of_principal_noninitial_rank 𝕜 γ hP hω hi

end PFP
