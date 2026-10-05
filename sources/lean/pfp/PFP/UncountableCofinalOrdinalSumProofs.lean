import PFP.UncountableCofinalOrdinalCoefficientProofs
import PFP.OrdinalLpSeparableRange

/-! Exact Corollary 4.10(i) instances for the higher uncountably cofinal
branch, and for every noninitial principal coefficient rank. The original
large-index premise, finite-p range, and primariness conclusion are retained.
The unrestricted coefficient normalization is not asserted here. -/
noncomputable section
namespace PFP
universe u v
variable (𝕜 : Type*) [RCLike 𝕜] (Γ : Type u)

theorem corollary_4_10_i_of_principal_uncountable_cofinal_rank
    (γ : Ordinal.{v}) (hP : Ordinal.Principal (· + ·) γ)
    (hc : Cardinal.aleph0 < γ.cof) (hgap : γ.cof.ord < γ) :
    Corollary_4_10_i 𝕜 Γ (Ordinal.omega0 ^ γ) :=
  corollary_4_10_i_of_coefficient_hasUPFP 𝕜 Γ _
    (ordinalContinuous_hasUPFP_of_principal_uncountable_cofinal_rank 𝕜 γ hP hc hgap)

theorem corollary_4_10_i_of_principal_noninitial_rank
    (γ : Ordinal.{v}) (hP : Ordinal.Principal (· + ·) γ)
    (hω : Ordinal.omega0 < γ) (hni : γ ≠ γ.cof.ord) :
    Corollary_4_10_i 𝕜 Γ (Ordinal.omega0 ^ γ) :=
  corollary_4_10_i_of_coefficient_hasUPFP 𝕜 Γ _
    (ordinalContinuous_hasUPFP_of_principal_noninitial_rank 𝕜 γ hP hω hni)

end PFP
