import PFP.OrdinalFullCoefficientReductions
import PFP.InitialOrdinalFiniteQuotientPolymorphic
import PFP.CountableOrdinalSumProofs

/-! Full Corollary 4.10(i), with arbitrary independent scalar, index and ordinal
universes. The countable, finite-quotient, infinite-quotient and canonical-power
cases use actual spaces and previously proved factorisation theorems. -/
noncomputable section
namespace PFP
open ThesisCommon
universe u v
variable (𝕜 : Type*) [RCLike 𝕜] (Γ : Type u)

theorem corollary_4_10_i (α : Ordinal.{v}) :
    Corollary_4_10_i 𝕜 Γ α := by
  by_cases hcount : α.card ≤ Cardinal.aleph0
  · exact corollary_4_10_i_of_countable 𝕜 Γ α
      (Cardinal.lt_ord.mpr (hcount.trans_lt Cardinal.aleph0_lt_aleph_one))
  · have hc : Cardinal.aleph0 < α.card := lt_of_not_ge hcount
    have hlo : α.card.ord ≤ α := Cardinal.ord_card_le α
    by_cases hfinite : α < α.card.ord * Ordinal.omega0
    · exact corollary_4_10_i_initial_finite_quotient_poly 𝕜 Γ hc.le α hlo hfinite
    · apply corollary_4_10_i_of_coefficient_hasUPFP 𝕜 Γ α
      by_cases hsq : α < α.card.ord * α.card.ord
      · by_cases hr : α.card.IsRegular
        · exact ordinalContinuous_hasUPFP_of_regular_infinite_quotient 𝕜 hr hc
            (le_of_not_gt hfinite) hsq
        · exact ordinalContinuous_hasUPFP_of_singular_below_square 𝕜 hc.le hr hlo hsq.le
      · apply ordinalContinuous_hasUPFP_above_initial_square 𝕜 α.card hc α le_rfl
        simpa only [← Ordinal.succ_one, Ordinal.opow_succ, Ordinal.opow_one] using
          (le_of_not_gt hsq)

/-- Both clauses of the printed corollary, retaining their respective cardinal
and exponent hypotheses inside the original statement definitions. -/
theorem corollary_4_10 [TopologicalSpace Γ] [DiscreteTopology Γ] (α : Ordinal.{v}) :
    Corollary_4_10_i 𝕜 Γ α ∧ Corollary_4_10_ii 𝕜 Γ α :=
  ⟨corollary_4_10_i 𝕜 Γ α, corollary_4_10_ii 𝕜 Γ α⟩

end PFP
