import Posets.OrdinalFixedExponentMiddle
import Posets.OrdinalVariableUnitPreservation

/-! Actual operator preservation for all countable canonical exponents.
The ambient initial cardinal may be regular or singular. -/

noncomputable section
namespace Posets
open JLMS ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000

theorem ordinalCountablePrincipalExponent_hasUPFP (c : Cardinal.{0})
    (hc : Cardinal.aleph0 < c) (g : Ordinal.{0})
    (hgω : Ordinal.omega0 ≤ g) (hgP : Ordinal.Principal (· + ·) g)
    (hgcard : g.card ≤ Cardinal.aleph0) :
    HasUPFP 𝕜 (OrdinalSpace 𝕜 (c.ord ^ g)) := by
  have hκ : 0 < c.ord := Ordinal.omega0_pos.trans_le (Cardinal.omega0_le_ord.mpr hc.le)
  have hωκ : Ordinal.omega0 < c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_lt_ord.mpr hc
  have hg1 : 1 < g := Ordinal.one_lt_omega0.trans_le hgω
  have hglim : Order.IsSuccLimit g := Ordinal.isSuccLimit_of_principal_add hg1 hgP
  have hgcf : g.cof = Cardinal.aleph0 :=
    le_antisymm ((Ordinal.cof_le_card g).trans hgcard) (Ordinal.aleph0_le_cof.mpr hglim)
  have hrP : Ordinal.Principal (· + ·) (c.ord * g) :=
    Ordinal.principal_add_mul_of_principal_add c.ord hg1.ne' hgP
  have hrω : Ordinal.omega0 < c.ord * g :=
    hωκ.trans_le (Ordinal.le_mul_left _ (zero_lt_one.trans hg1))
  have hrcf : (c.ord * g).cof = Cardinal.aleph0 :=
    ((Ordinal.isNormal_mul_right hκ).cof_eq hglim).trans hgcf
  have h := ordinalVariableUnit_hasUPFP (𝕜 := 𝕜) (c.ord * g) hrP hrω hrcf
  exact h.of_equiv (ordinalSpaceCongrIsometry (𝕜 := 𝕜)
    (ordinal_uncountable_initial_power_rank hc g)).toContinuousLinearEquiv

theorem ordinalCountableExponentAboveSquare_hasUPFP (c : Cardinal.{0})
    (hc : Cardinal.aleph0 < c) (α : Ordinal.{0})
    (hlo : c.ord ^ (2 : Ordinal.{0}) ≤ α)
    (hhi : α < c.ord ^ (Cardinal.aleph 1).ord) :
    HasUPFP 𝕜 (OrdinalSpace 𝕜 α) := by
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
    exists_ordinalFixedExponentCanonical Cardinal.aleph0 le_rfl β hβ hβcard
  have hbase : HasUPFP 𝕜 (OrdinalSpace 𝕜 (c.ord ^ g)) := by
    rcases hgc with rfl | ⟨hgω, hgP⟩
    · have he : c.ord ^ (2 : Ordinal.{0}) = c.ord * c.ord := by
        rw [← Ordinal.succ_one, Ordinal.opow_succ, Ordinal.opow_one]
      apply initialHigherBelowOmega_hasUPFP hc
      · exact he.ge
      · exact (Ordinal.opow_lt_opow_iff_right hκ).mpr (Ordinal.nat_lt_omega0 2)
    · exact ordinalCountablePrincipalExponent_hasUPFP c hc g hgω hgP hgcard
  apply ordinalFixedExponentMiddle_hasUPFP_of_base c hc.le g hg (hgcard.trans hc.le) hbase α
  · exact (Ordinal.opow_le_opow_right (zero_lt_one.trans hκ) hgb).trans
      (Ordinal.opow_log_le_self c.ord hα0)
  · exact (Ordinal.lt_opow_iff_log_lt hκ hα0).mpr hbg

theorem proposition_3_1_initial_belowCountableExponent (c : Cardinal.{0})
    (hc : Cardinal.aleph0 < c) (α : Ordinal.{0})
    (hlo : c.ord ≤ α) (hhi : α < c.ord ^ (Cardinal.aleph 1).ord) :
    Proposition_3_1 𝕜 α := by
  by_cases hsq : α < c.ord ^ (2 : Ordinal.{0})
  · apply proposition_3_1_uncountable_belowOmegaPower hc hlo
    exact hsq.trans ((Ordinal.opow_lt_opow_iff_right
      (Ordinal.one_lt_omega0.trans_le (Cardinal.omega0_le_ord.mpr hc.le))).mpr
        (Ordinal.nat_lt_omega0 2))
  · intro _
    letI : Nonempty (Set.Icc (0 : Ordinal.{0}) α) := ⟨⟨0, le_rfl, Ordinal.zero_le _⟩⟩
    have h := uniqueMaximal_of_hasPFP
      (ordinalCountableExponentAboveSquare_hasUPFP (𝕜 := 𝕜) c hc α
        (le_of_not_gt hsq) hhi).hasPFP
    exact ⟨h.2, fun _ => h.1⟩

end Posets
