import PFP.OrdinalCoefficientScalarTransport
import Posets.OrdinalHigherLimitCofinalPreservation

/-! Unconditional coefficient UPFP on the higher countably cofinal rank
branch, with arbitrary scalar and ordinal universes. All analytic and
geometric inputs are proved in the imported varying-rank construction. -/
noncomputable section
namespace PFP
open ThesisCommon
universe u
variable (𝕜 : Type*) [RCLike 𝕜]

theorem ordinalContinuous_hasUPFP_of_principal_countable_cofinal_rank
    (γ : Ordinal.{u}) (hP : Ordinal.Principal (· + ·) γ)
    (hω : Ordinal.omega0 < γ) (hcf : γ.cof = Cardinal.aleph0) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 (Ordinal.omega0 ^ γ)) :=
  ordinalContinuous_hasUPFP_of_real_complex 𝕜 _
    (Posets.ordinalVariableUnit_hasUPFP γ hP hω hcf)
    (Posets.ordinalVariableUnit_hasUPFP γ hP hω hcf)

theorem ordinalContinuous_hasUPFP_of_initial_higher_limit
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 < c)
    (η : Ordinal.{u}) (hη : η ≠ 0)
    (hcf : (c.ord * Ordinal.omega0 ^ η).cof = Cardinal.aleph0) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 (c.ord ^ (Ordinal.omega0 ^ η))) :=
  ordinalContinuous_hasUPFP_of_real_complex 𝕜 _
    (Posets.ordinalInitialHigherLimit_hasUPFP c hc η hη hcf)
    (Posets.ordinalInitialHigherLimit_hasUPFP c hc η hη hcf)

theorem ordinalContinuous_hasUPFP_of_initial_higher_successor_limit
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 < c) (η : Ordinal.{u}) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 (c.ord ^ (Ordinal.omega0 ^ Order.succ η))) :=
  ordinalContinuous_hasUPFP_of_real_complex 𝕜 _
    (Posets.ordinalInitialHigherSuccessorLimit_hasUPFP c hc η)
    (Posets.ordinalInitialHigherSuccessorLimit_hasUPFP c hc η)

theorem ordinalContinuous_hasUPFP_of_initial_higher_countable_cofinal_limit
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 < c)
    (η : Ordinal.{u}) (hη : Order.IsSuccLimit η) (hcf : η.cof = Cardinal.aleph0) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 (c.ord ^ (Ordinal.omega0 ^ η))) :=
  ordinalContinuous_hasUPFP_of_real_complex 𝕜 _
    (Posets.ordinalInitialHigherCountableCofinalLimit_hasUPFP c hc η hη hcf)
    (Posets.ordinalInitialHigherCountableCofinalLimit_hasUPFP c hc η hη hcf)

end PFP
