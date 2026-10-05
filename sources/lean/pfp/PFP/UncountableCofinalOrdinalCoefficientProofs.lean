import PFP.HigherCofinalOrdinalCoefficientProofs
import Posets.PFPOrdinalUncountableCofinalPreservation

/-! Higher uncountably cofinal coefficient cases, retaining independent
scalar and ordinal universes. Together with the countably cofinal proof,
this covers every noninitial principal rank above omega. -/
noncomputable section
namespace PFP
open ThesisCommon
universe u
variable (𝕜 : Type*) [RCLike 𝕜]

theorem ordinalContinuous_hasUPFP_of_principal_uncountable_cofinal_rank
    (γ : Ordinal.{u}) (hP : Ordinal.Principal (· + ·) γ)
    (hc : Cardinal.aleph0 < γ.cof) (hgap : γ.cof.ord < γ) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 (Ordinal.omega0 ^ γ)) :=
  ordinalContinuous_hasUPFP_of_real_complex 𝕜 _
    (Posets.pfpOrdinalUncountableCofinal_hasUPFP γ hP hc hgap)
    (Posets.pfpOrdinalUncountableCofinal_hasUPFP γ hP hc hgap)

theorem ordinalContinuous_hasUPFP_of_principal_noninitial_rank
    (γ : Ordinal.{u}) (hP : Ordinal.Principal (· + ·) γ)
    (hω : Ordinal.omega0 < γ) (hni : γ ≠ γ.cof.ord) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 (Ordinal.omega0 ^ γ)) := by
  have hγ : Order.IsSuccLimit γ := Ordinal.isSuccLimit_of_principal_add
    (Ordinal.one_lt_omega0.trans hω) hP
  by_cases hcf : γ.cof ≤ Cardinal.aleph0
  · exact ordinalContinuous_hasUPFP_of_principal_countable_cofinal_rank 𝕜 γ hP hω
      (le_antisymm hcf (Ordinal.aleph0_le_cof.mpr hγ))
  · exact ordinalContinuous_hasUPFP_of_principal_uncountable_cofinal_rank 𝕜 γ hP
      (lt_of_not_ge hcf) (lt_of_le_of_ne (Ordinal.ord_cof_le γ) (Ne.symm hni))

end PFP
