import ThesisCommon.Analysis.OrdinalIntervalSum

/-! A compact ordinal power absorbs every shorter compact ordinal tail.
The homeomorphism is built by interchanging two clopen ordinal blocks. -/

noncomputable section
open Set Order Topology
universe u
namespace ThesisCommon

def ordinalIntervalCongr {α β : Ordinal.{u}} (h : α = β) :
    OrdinalInterval α ≃ₜ OrdinalInterval β := by
  cases h
  exact Homeomorph.refl _

/-- A shorter compact ordinal interval can be added as a clopen component
to any positive ordinal power without changing its homeomorphism type. -/
def ordinalPowerSumAbsorb {η γ : Ordinal.{u}} (hη : η ≠ 0)
    (hγ : γ < Ordinal.omega0 ^ η) :
    (OrdinalInterval γ ⊕ OrdinalInterval (Ordinal.omega0 ^ η)) ≃ₜ
      OrdinalInterval (Ordinal.omega0 ^ η) := by
  have hlim := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hη
  have hs : γ + 1 < Ordinal.omega0 ^ η := by
    simpa only [Ordinal.add_one_eq_succ] using hlim.succ_lt hγ
  exact (ordinalIntervalSumHomeomorph γ (Ordinal.omega0 ^ η)).trans
    (ordinalIntervalCongr (Ordinal.add_omega0_opow hs))

/-- The short-tail absorption step in Baker's classification, with an
actual homeomorphism and no countability restriction. -/
def ordinalPowerTailAbsorb {η δ : Ordinal.{u}} (hη : η ≠ 0)
    (hδ : δ < Ordinal.omega0 ^ η) :
    OrdinalInterval (Ordinal.omega0 ^ η + δ) ≃ₜ OrdinalInterval (Ordinal.omega0 ^ η) := by
  by_cases hzero : δ = 0
  · subst δ
    exact ordinalIntervalCongr (add_zero _)
  let γ := δ - 1
  have hγ : γ < Ordinal.omega0 ^ η := (Ordinal.sub_le_self δ 1).trans_lt hδ
  have hδeq : 1 + γ = δ := Ordinal.add_sub_cancel_of_le (Ordinal.one_le_iff_ne_zero.mpr hzero)
  have hwhole : Ordinal.omega0 ^ η + 1 + γ = Ordinal.omega0 ^ η + δ := by
    rw [add_assoc, hδeq]
  exact ((ordinalIntervalCongr hwhole.symm).trans
    (ordinalIntervalSumHomeomorph (Ordinal.omega0 ^ η) γ).symm).trans
    ((Homeomorph.sumComm _ _).trans (ordinalPowerSumAbsorb hη hγ))

end ThesisCommon
