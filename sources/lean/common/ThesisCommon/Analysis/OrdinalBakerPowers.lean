import ThesisCommon.Analysis.OrdinalBakerMultiples
import ThesisCommon.Analysis.OrdinalBakerLocality

/-! The exact transfinite derived-set calculation for arbitrary ordinal
powers. At positive rank α, the derived ordinals are the positive multiples
of ω^α. No countability hypothesis is imposed. -/
noncomputable section
open Set Order Topology
universe u
namespace ThesisCommon

theorem ordinalDerived_univ (α : Ordinal.{u}) :
    ordinalDerived (univ : Set Ordinal.{u}) α =
      if α = 0 then univ else ordinalPositiveMultiples (Ordinal.omega0 ^ α) := by
  induction α using Ordinal.limitRecOn with
  | zero => simp
  | succ α ih =>
      rw [ordinalDerived_succ, if_neg (Ordinal.succ_ne_zero α)]
      by_cases hα : α = 0
      · subst α
        simpa only [ordinalDerived_zero, Ordinal.succ_zero, Ordinal.opow_one,
          ordinalPositiveMultiples] using ordinal_derivedSet_univ
      · rw [ih, if_neg hα, ordinal_derivedSet_positiveMultiples
          (Ordinal.opow_pos α Ordinal.omega0_pos), Ordinal.opow_succ]
  | limit α hα ih =>
      rw [ordinalDerived_limit _ hα, if_neg (show α ≠ 0 from hα.ne_bot)]
      ext x
      constructor
      · intro hx
        have hone : (1 : Ordinal.{u}) < α := by
          simpa only [Ordinal.succ_zero] using
            hα.succ_lt (show (0 : Ordinal.{u}) < α from hα.bot_lt)
        have h1 := mem_iInter₂.mp hx 1 hone
        rw [ih 1 hone, if_neg Ordinal.one_ne_zero] at h1
        refine ⟨h1.1, ordinal_opow_dvd_limit_iff hα |>.mpr ?_⟩
        intro β hβ
        by_cases hb : β = 0
        · simp [hb]
        · have hxb := mem_iInter₂.mp hx β hβ
          rw [ih β hβ, if_neg hb] at hxb
          exact hxb.2
      · rintro ⟨hx, hd⟩
        apply mem_iInter₂.mpr
        intro β hβ
        rw [ih β hβ]
        by_cases hb : β = 0
        · simp [hb]
        · rw [if_neg hb]
          exact ⟨hx, (Ordinal.opow_dvd_opow _ hβ.le).trans hd⟩

theorem ordinalDerived_Iic_power_self {α : Ordinal.{u}} (hα : α ≠ 0) :
    ordinalDerived (Iic (Ordinal.omega0 ^ α)) α = {Ordinal.omega0 ^ α} := by
  rw [ordinalDerived_Iic, ordinalDerived_univ, if_neg hα]
  ext x
  change ((x ≠ 0 ∧ Ordinal.omega0 ^ α ∣ x) ∧ x ≤ Ordinal.omega0 ^ α) ↔
    x = Ordinal.omega0 ^ α
  constructor
  · intro hx
    exact le_antisymm hx.2 (Ordinal.le_of_dvd hx.1.1 hx.1.2)
  · rintro rfl
    exact ⟨⟨Ordinal.opow_ne_zero α Ordinal.omega0_ne_zero, dvd_refl _⟩, le_rfl⟩

theorem ordinal_power_le_of_nonempty_derivative {α β : Ordinal.{u}} (hα : α ≠ 0)
    (hne : (ordinalDerived (Iic β) α).Nonempty) : Ordinal.omega0 ^ α ≤ β := by
  rw [ordinalDerived_Iic, ordinalDerived_univ, if_neg hα] at hne
  obtain ⟨x, ⟨hx0, hxd⟩, hxβ⟩ := hne
  exact (Ordinal.le_of_dvd hx0 hxd).trans hxβ

end ThesisCommon
