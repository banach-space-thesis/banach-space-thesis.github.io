import Posets.OrdinalVariableUnitPreservation

/-! Higher initial-base limit powers covered by the genuine varying-rank
construction. The arbitrary ordinal exponent is retained; its displayed
cofinality premise is essential to this countable-block proof. -/
noncomputable section
namespace Posets
open ThesisCommon
universe u
variable {𝕜 : Type} [RCLike 𝕜]

theorem ordinalInitialHigherLimit_hasUPFP
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 < c)
    (η : Ordinal.{u}) (hη : η ≠ 0)
    (hcf : (c.ord * Ordinal.omega0 ^ η).cof = Cardinal.aleph0) :
    HasUPFP 𝕜 (JLMS.OrdinalC 𝕜 (c.ord ^ (Ordinal.omega0 ^ η))) := by
  have hωκ : Ordinal.omega0 < c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_lt_ord.mpr hc
  have h := ordinalVariableUnit_hasUPFP (𝕜 := 𝕜) (c.ord * Ordinal.omega0 ^ η)
    (ordinal_higher_limit_rank_principal c.ord hη)
    (hωκ.trans_le (Ordinal.le_mul_left _ (Ordinal.opow_pos _ Ordinal.omega0_pos))) hcf
  have he : Ordinal.omega0 ^ (c.ord * Ordinal.omega0 ^ η) =
      c.ord ^ (Ordinal.omega0 ^ η) := by
    rw [Ordinal.opow_mul, ordinal_uncountable_initial_omega_power hc]
  exact h.of_equiv (JLMS.ordinalSpaceCongrIsometry (𝕜 := 𝕜) he).toContinuousLinearEquiv

theorem ordinalInitialHigherSuccessorLimit_hasUPFP
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 < c) (η : Ordinal.{u}) :
    HasUPFP 𝕜 (JLMS.OrdinalC 𝕜 (c.ord ^ (Ordinal.omega0 ^ Order.succ η))) :=
  ordinalInitialHigherLimit_hasUPFP c hc (Order.succ η) (Order.succ_ne_bot η)
    (ordinal_higher_limit_rank_cof_succ
      (Ordinal.omega0_pos.trans_le (Cardinal.omega0_le_ord.mpr hc.le)) η)

theorem ordinalInitialHigherCountableCofinalLimit_hasUPFP
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 < c)
    (η : Ordinal.{u}) (hη : Order.IsSuccLimit η) (hcf : η.cof = Cardinal.aleph0) :
    HasUPFP 𝕜 (JLMS.OrdinalC 𝕜 (c.ord ^ (Ordinal.omega0 ^ η))) :=
  ordinalInitialHigherLimit_hasUPFP c hc η hη.ne_bot
    (ordinal_higher_limit_rank_cof_limit
      (Ordinal.omega0_pos.trans_le (Cardinal.omega0_le_ord.mpr hc.le)) hη hcf)

end Posets
