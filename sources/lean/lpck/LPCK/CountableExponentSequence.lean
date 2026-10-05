import LPCK.InitialPowerSequence
import Posets.OrdinalCountableExponentPreservation

/-! All sequence exponents on the actual uncountable ordinal intervals
between the square and the first uncountable exponent of an initial ordinal.
This is a proved subrange of the unrestricted original Theorem 1.1. -/
noncomputable section
namespace LPCK
open ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000

theorem theorem_1_1_initial_countable_canonical (c : Cardinal.{0})
    (hc : Cardinal.aleph0 < c) (g : Ordinal.{0}) (hg : 2 ≤ g)
    (hgcard : g.card ≤ Cardinal.aleph0)
    (hgc : g = 2 ∨ (Ordinal.omega0 ≤ g ∧ Ordinal.Principal (· + ·) g))
    (p : BanachExponent) : Theorem_1_1 𝕜 (c.ord ^ g) p := by
  apply initialCanonical_sequence_of_base c hc g hg (hgcard.trans hc.le) _ p
  rcases hgc with rfl | ⟨hgω, hgP⟩
  · have he : c.ord ^ (2 : Ordinal.{0}) = c.ord * c.ord := by
      rw [← Ordinal.succ_one, Ordinal.opow_succ, Ordinal.opow_one]
    apply Posets.initialHigherBelowOmega_hasUPFP hc
    · exact he.ge
    · exact (Ordinal.opow_lt_opow_iff_right
        (Ordinal.one_lt_omega0.trans_le (Cardinal.omega0_le_ord.mpr hc.le))).mpr
        (Ordinal.nat_lt_omega0 2)
  · exact Posets.ordinalCountablePrincipalExponent_hasUPFP c hc g hgω hgP hgcard

theorem theorem_1_1_initial_below_countable_exponent (c : Cardinal.{0})
    (hc : Cardinal.aleph0 < c) (α : Ordinal.{0})
    (hlo : c.ord ^ (2 : Ordinal.{0}) ≤ α)
    (hhi : α < c.ord ^ (Cardinal.aleph 1).ord) (p : BanachExponent) :
    Theorem_1_1 𝕜 α p := by
  have hκ : 1 < c.ord := Ordinal.one_lt_omega0.trans_le (Cardinal.omega0_le_ord.mpr hc.le)
  have hα0 : α ≠ 0 := ((Ordinal.opow_pos _ (zero_lt_one.trans hκ)).trans_le hlo).ne'
  let β := Ordinal.log c.ord α
  have hβ : 2 ≤ β := Ordinal.le_log_of_opow_le hκ hlo
  have hβhi : β < (Cardinal.aleph 1).ord := (Ordinal.lt_opow_iff_log_lt hκ hα0).mp hhi
  have hβcard : β.card ≤ Cardinal.aleph0 := by
    have hlt : β.card < Cardinal.aleph 1 := Cardinal.lt_ord.mp hβhi
    rw [← Cardinal.succ_aleph0] at hlt
    exact Order.lt_succ_iff.mp hlt
  obtain ⟨g, hg, hgcard, hgc, hgb, hbg⟩ :=
    Posets.exists_ordinalFixedExponentCanonical Cardinal.aleph0 le_rfl β hβ hβcard
  let e := Posets.ordinalFixedExponentMiddleEquiv (𝕜 := 𝕜) c hc.le g hg
    (hgcard.trans hc.le) α
    ((Ordinal.opow_le_opow_right (zero_lt_one.trans hκ) hgb).trans
      (Ordinal.opow_log_le_self c.ord hα0))
    ((Ordinal.lt_opow_iff_log_lt hκ hα0).mpr hbg)
  have h := (theorem_1_1_initial_countable_canonical (𝕜 := 𝕜) c hc g hg hgcard hgc p).1
  have ht := h.of_equiv (lpMapEquiv p.val e.symm)
  exact ⟨ht, ht.lp_isPrimary⟩

end LPCK
