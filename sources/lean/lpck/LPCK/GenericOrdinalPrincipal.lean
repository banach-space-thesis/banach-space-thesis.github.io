import LPCK.GenericOrdinalQuantitative
import Posets.PFPOrdinalUncountableCofinalPreservation
import Posets.OrdinalVariableUnitPreservation
import Posets.OrdinalClosedCopyInitialPowers

/-! Additive-principal ordinal base UPFP in arbitrary ordinal universes.
The countable and uncountable cofinal constructions are actual operators. -/
noncomputable section
universe u
namespace LPCK.GenericOrdinal
open ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000

theorem principalRank_hasUPFP (γ : Ordinal.{u})
    (hP : Ordinal.Principal (· + ·) γ) (hω : Ordinal.omega0 < γ) :
    HasUPFP 𝕜 (JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ)) := by
  by_cases hcf : γ.cof = Cardinal.aleph0
  · exact Posets.ordinalVariableUnit_hasUPFP γ hP hω hcf
  have hlim := Ordinal.isSuccLimit_of_principal_add (Ordinal.one_lt_omega0.trans hω) hP
  have hc : Cardinal.aleph0 < γ.cof :=
    lt_of_le_of_ne (Ordinal.aleph0_le_cof.mpr hlim) (Ne.symm hcf)
  by_cases hγ : γ = γ.cof.ord
  · have hregular : γ.cof.IsRegular := Cardinal.isRegular_cof hlim
    have he : Ordinal.omega0 ^ γ = γ.cof.ord := calc
      _ = Ordinal.omega0 ^ γ.cof.ord := congrArg (Ordinal.omega0 ^ ·) hγ
      _ = _ := Posets.ordinal_uncountable_initial_omega_power hc
    exact (initialOrdinal_hasUPFP (𝕜 := 𝕜) hregular hc).of_equiv
      (JLMS.ordinalSpaceCongrIsometry (𝕜 := 𝕜) he).symm.toContinuousLinearEquiv
  · exact Posets.pfpOrdinalUncountableCofinal_hasUPFP γ hP hc
      (lt_of_le_of_ne (Ordinal.ord_cof_le γ) (Ne.symm hγ))

end LPCK.GenericOrdinal
