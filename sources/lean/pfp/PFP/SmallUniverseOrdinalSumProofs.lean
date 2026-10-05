import PFP.PrincipalOrdinalCoefficientProofs
import PFP.InitialOrdinalSumProofs
import PFP.CountableOrdinalSumProofs
import Posets.OrdinalFinalClassificationReduction

/-! Corollary 4.10(i) for every ordinal in universe zero, with an arbitrary
outer index universe. This is an explicitly limited endpoint: the original
arbitrary-universe target is unchanged. The lower-range coefficient and
normalization results imported here currently require small scalar and
ordinal universes. No principal-preservation hypothesis remains. -/
noncomputable section
namespace PFP
open ThesisCommon
variable (𝕜 : Type) [RCLike 𝕜] (Γ : Type*)

theorem ordinalContinuous_hasUPFP_above_initial_square_small
    (c : Cardinal.{0}) (hc : Cardinal.aleph0 < c) (α : Ordinal.{0})
    (hcard : α.card ≤ c) (hsq : c.ord ^ (2 : Ordinal) ≤ α) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 α) :=
  Posets.ordinalAboveSquare_hasUPFP_of_principal_preservation
    (ordinalContinuous_hasUPFP_of_principal_rank 𝕜) c hc α hcard hsq

theorem corollary_4_10_i_small_universe (α : Ordinal.{0}) :
    Corollary_4_10_i 𝕜 Γ α := by
  by_cases hcount : α.card ≤ Cardinal.aleph0
  · exact corollary_4_10_i_of_countable 𝕜 Γ α
      (Cardinal.lt_ord.mpr (hcount.trans_lt Cardinal.aleph0_lt_aleph_one))
  · have hc : Cardinal.aleph0 < α.card := lt_of_not_ge hcount
    have hlo : α.card.ord ≤ α := Cardinal.ord_card_le α
    by_cases hsq : α < α.card.ord ^ (2 : Ordinal)
    · apply corollary_4_10_i_below_initial_omega_power 𝕜 Γ hc α hlo
      exact hsq.trans ((Ordinal.opow_lt_opow_iff_right
        (Ordinal.one_lt_omega0.trans_le (Cardinal.omega0_le_ord.mpr hc.le))).mpr
          (Ordinal.nat_lt_omega0 2))
    · exact corollary_4_10_i_of_coefficient_hasUPFP 𝕜 Γ α
        (ordinalContinuous_hasUPFP_above_initial_square_small 𝕜 α.card hc α
          le_rfl (le_of_not_gt hsq))

end PFP
