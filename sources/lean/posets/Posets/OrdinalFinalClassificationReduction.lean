import Posets.OrdinalCountableExponentPreservation
import Posets.CountableOrdinalIdealResults

/-! An explicitly conditional final classification reduction. The remaining
principal-rank preservation theorem is a displayed argument; this file does
not assert that theorem or unconditional all-ordinal Proposition 3.1. -/

noncomputable section
namespace Posets
open JLMS ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000

theorem ordinalInitialCanonicalPower_hasUPFP_of_principal_preservation
    (hprincipal : ∀ γ : Ordinal.{0}, Ordinal.Principal (· + ·) γ →
      Ordinal.omega0 < γ → HasUPFP 𝕜 (OrdinalSpace 𝕜 (Ordinal.omega0 ^ γ)))
    (c : Cardinal.{0}) (hc : Cardinal.aleph0 < c)
    (g : Ordinal.{0})
    (hgc : g = 2 ∨ (Ordinal.omega0 ≤ g ∧ Ordinal.Principal (· + ·) g)) :
    HasUPFP 𝕜 (OrdinalSpace 𝕜 (c.ord ^ g)) := by
  have hκ : 1 < c.ord := Ordinal.one_lt_omega0.trans_le (Cardinal.omega0_le_ord.mpr hc.le)
  rcases hgc with rfl | ⟨hgω, hgP⟩
  · have he : c.ord ^ (2 : Ordinal.{0}) = c.ord * c.ord := by
      rw [← Ordinal.succ_one, Ordinal.opow_succ, Ordinal.opow_one]
    apply initialHigherBelowOmega_hasUPFP hc
    · exact he.ge
    · exact (Ordinal.opow_lt_opow_iff_right hκ).mpr (Ordinal.nat_lt_omega0 2)
  · have hωκ : Ordinal.omega0 < c.ord := by
      simpa only [Cardinal.ord_aleph0] using Cardinal.ord_lt_ord.mpr hc
    have hg1 : 1 < g := Ordinal.one_lt_omega0.trans_le hgω
    have hrP : Ordinal.Principal (· + ·) (c.ord * g) :=
      Ordinal.principal_add_mul_of_principal_add c.ord hg1.ne' hgP
    have hrω : Ordinal.omega0 < c.ord * g :=
      hωκ.trans_le (Ordinal.le_mul_left _ (zero_lt_one.trans hg1))
    exact (hprincipal _ hrP hrω).of_equiv
      (ordinalSpaceCongrIsometry (𝕜 := 𝕜)
        (ordinal_uncountable_initial_power_rank hc g)).toContinuousLinearEquiv

theorem ordinalAboveSquare_hasUPFP_of_principal_preservation
    (hprincipal : ∀ γ : Ordinal.{0}, Ordinal.Principal (· + ·) γ →
      Ordinal.omega0 < γ → HasUPFP 𝕜 (OrdinalSpace 𝕜 (Ordinal.omega0 ^ γ)))
    (c : Cardinal.{0}) (hc : Cardinal.aleph0 < c)
    (α : Ordinal.{0}) (hcard : α.card ≤ c) (hα : c.ord ^ (2 : Ordinal.{0}) ≤ α) :
    HasUPFP 𝕜 (OrdinalSpace 𝕜 α) := by
  obtain ⟨g, _, _, hgc, ⟨e⟩⟩ :=
    exists_ordinalSpace_canonical_power_normalForm (𝕜 := 𝕜) c hc.le α hcard hα
  exact (ordinalInitialCanonicalPower_hasUPFP_of_principal_preservation hprincipal c hc g hgc).of_equiv e.symm

theorem proposition_3_1_of_principal_preservation
    (hprincipal : ∀ γ : Ordinal.{0}, Ordinal.Principal (· + ·) γ →
      Ordinal.omega0 < γ → HasUPFP 𝕜 (OrdinalSpace 𝕜 (Ordinal.omega0 ^ γ)))
    (α : Ordinal.{0}) : Proposition_3_1 𝕜 α := by
  by_cases hcount : α.card ≤ Cardinal.aleph0
  · exact proposition_3_1_countable α hcount
  · have hc : Cardinal.aleph0 < α.card := lt_of_not_ge hcount
    have hlo : α.card.ord ≤ α := Cardinal.ord_card_le α
    by_cases hsq : α < α.card.ord ^ (2 : Ordinal.{0})
    · apply proposition_3_1_uncountable_belowOmegaPower hc hlo
      exact hsq.trans ((Ordinal.opow_lt_opow_iff_right
        (Ordinal.one_lt_omega0.trans_le (Cardinal.omega0_le_ord.mpr hc.le))).mpr
          (Ordinal.nat_lt_omega0 2))
    · exact proposition_3_1_of_ordinal_hasPFP α
        (ordinalAboveSquare_hasUPFP_of_principal_preservation hprincipal α.card hc α
          le_rfl (le_of_not_gt hsq)).hasPFP

end Posets

