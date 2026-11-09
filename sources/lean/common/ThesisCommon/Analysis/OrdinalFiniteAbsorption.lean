import ThesisCommon.Analysis.OrdinalAbsorption

/-! Short-tail absorption for a positive finite multiple of an ordinal
power. This is the final topological step in general ordinal normalization. -/

noncomputable section
open Set Order Topology
universe u
namespace ThesisCommon

def ordinalPowerNatSumAbsorb {η γ : Ordinal.{u}} (hη : η ≠ 0)
    (hγ : γ < Ordinal.omega0 ^ η) (n : ℕ) (hn : 0 < n) :
    (OrdinalInterval γ ⊕ OrdinalInterval (Ordinal.omega0 ^ η * (n : Ordinal))) ≃ₜ
      OrdinalInterval (Ordinal.omega0 ^ η * (n : Ordinal)) := by
  have hlim := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hη
  have hs : γ + 1 < Ordinal.omega0 ^ η := by
    simpa only [Ordinal.add_one_eq_succ] using hlim.succ_lt hγ
  have heq : γ + 1 + Ordinal.omega0 ^ η * (n : Ordinal) =
      Ordinal.omega0 ^ η * (n : Ordinal) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have hnrepr : ((m + 1 : ℕ) : Ordinal.{u}) = 1 + (m : Ordinal.{u}) := by
      calc
        ((m + 1 : ℕ) : Ordinal.{u}) = ((1 + m : ℕ) : Ordinal.{u}) :=
          congrArg (fun k : ℕ => (k : Ordinal.{u})) (Nat.add_comm m 1)
        _ = 1 + (m : Ordinal.{u}) := by rw [Nat.cast_add, Nat.cast_one]
    change γ + 1 + Ordinal.omega0 ^ η * ((m + 1 : ℕ) : Ordinal) =
      Ordinal.omega0 ^ η * ((m + 1 : ℕ) : Ordinal)
    rw [hnrepr, mul_add, mul_one, ← add_assoc, Ordinal.add_omega0_opow hs]
  exact (ordinalIntervalSumHomeomorph γ _).trans (ordinalIntervalCongr heq)

def ordinalPowerNatTailAbsorb {η δ : Ordinal.{u}} (hη : η ≠ 0)
    (hδ : δ < Ordinal.omega0 ^ η) (n : ℕ) (hn : 0 < n) :
    OrdinalInterval (Ordinal.omega0 ^ η * (n : Ordinal) + δ) ≃ₜ
      OrdinalInterval (Ordinal.omega0 ^ η * (n : Ordinal)) := by
  by_cases hzero : δ = 0
  · subst δ
    exact ordinalIntervalCongr (add_zero _)
  let γ := δ - 1
  have hγ : γ < Ordinal.omega0 ^ η := (Ordinal.sub_le_self δ 1).trans_lt hδ
  have hδeq : 1 + γ = δ := Ordinal.add_sub_cancel_of_le (Ordinal.one_le_iff_ne_zero.mpr hzero)
  have hwhole : Ordinal.omega0 ^ η * (n : Ordinal) + 1 + γ =
      Ordinal.omega0 ^ η * (n : Ordinal) + δ := by rw [add_assoc, hδeq]
  exact ((ordinalIntervalCongr hwhole.symm).trans
    (ordinalIntervalSumHomeomorph (Ordinal.omega0 ^ η * (n : Ordinal)) γ).symm).trans
    ((Homeomorph.sumComm _ _).trans (ordinalPowerNatSumAbsorb hη hγ n hn))

end ThesisCommon
