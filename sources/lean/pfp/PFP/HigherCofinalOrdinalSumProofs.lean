import PFP.HigherCofinalOrdinalCoefficientProofs
import PFP.OrdinalLpSeparableRange

/-! Exact instances of Corollary 4.10(i) on the higher countably cofinal
rank branch. The original p range, primariness conclusion, and independent
scalar/index/ordinal universes are retained. This does not claim the
unrestricted corollary for ordinals outside the displayed branches. -/
noncomputable section
namespace PFP
open ThesisCommon
universe u v
variable (𝕜 : Type*) [RCLike 𝕜] (Γ : Type u)

theorem corollary_4_10_i_of_principal_countable_cofinal_rank
    (γ : Ordinal.{v}) (hP : Ordinal.Principal (· + ·) γ)
    (hω : Ordinal.omega0 < γ) (hcf : γ.cof = Cardinal.aleph0) :
    Corollary_4_10_i 𝕜 Γ (Ordinal.omega0 ^ γ) :=
  corollary_4_10_i_of_coefficient_hasUPFP 𝕜 Γ _
    (ordinalContinuous_hasUPFP_of_principal_countable_cofinal_rank 𝕜 γ hP hω hcf)

theorem corollary_4_10_i_of_initial_higher_limit
    (c : Cardinal.{v}) (hc : Cardinal.aleph0 < c)
    (η : Ordinal.{v}) (hη : η ≠ 0)
    (hcf : (c.ord * Ordinal.omega0 ^ η).cof = Cardinal.aleph0) :
    Corollary_4_10_i 𝕜 Γ (c.ord ^ (Ordinal.omega0 ^ η)) :=
  corollary_4_10_i_of_coefficient_hasUPFP 𝕜 Γ _
    (ordinalContinuous_hasUPFP_of_initial_higher_limit 𝕜 c hc η hη hcf)

theorem corollary_4_10_i_of_initial_higher_successor_limit
    (c : Cardinal.{v}) (hc : Cardinal.aleph0 < c) (η : Ordinal.{v}) :
    Corollary_4_10_i 𝕜 Γ (c.ord ^ (Ordinal.omega0 ^ Order.succ η)) :=
  corollary_4_10_i_of_coefficient_hasUPFP 𝕜 Γ _
    (ordinalContinuous_hasUPFP_of_initial_higher_successor_limit 𝕜 c hc η)

theorem corollary_4_10_i_of_initial_higher_countable_cofinal_limit
    (c : Cardinal.{v}) (hc : Cardinal.aleph0 < c)
    (η : Ordinal.{v}) (hη : Order.IsSuccLimit η) (hcf : η.cof = Cardinal.aleph0) :
    Corollary_4_10_i 𝕜 Γ (c.ord ^ (Ordinal.omega0 ^ η)) :=
  corollary_4_10_i_of_coefficient_hasUPFP 𝕜 Γ _
    (ordinalContinuous_hasUPFP_of_initial_higher_countable_cofinal_limit 𝕜 c hc η hη hcf)

end PFP
