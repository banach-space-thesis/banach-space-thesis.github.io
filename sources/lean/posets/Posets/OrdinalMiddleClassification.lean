import Posets.OrdinalMiddleClassificationPowers

/-! Actual Banach-space classification in the interval
ω^ω ≤ α < ω^(ω²), needed for the uniform ideal-count gap. -/
noncomputable section
namespace Posets
open ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 800000

def ordinalMiddlePowerEquiv (β : Ordinal.{0}) (hlo : Ordinal.omega0 ≤ β)
    (hhi : β < Ordinal.omega0 ^ (2 : Ordinal.{0})) :
    OrdinalSpace 𝕜 (Ordinal.omega0 ^ β) ≃L[𝕜]
      OrdinalSpace 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 : Ordinal.{0})) := by
  have hinf : Ordinal.omega0 ≤ Ordinal.omega0 ^ β := by
    simpa only [Ordinal.opow_one] using Ordinal.opow_le_opow_right Ordinal.omega0_pos
      (Ordinal.one_lt_omega0.le.trans hlo)
  exact (JLMS.ordinalSpaceEndpointZeroEquiv (𝕜 := 𝕜) _ hinf).trans
    ((ordinalMiddleEndpointPowerEquiv β hlo hhi).trans
      (JLMS.ordinalSpaceEndpointZeroEquiv (𝕜 := 𝕜) _ ordinalMiddle_base_infinite).symm)

def ordinalMiddleSquareEquiv :
    OrdinalSpace 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 : Ordinal.{0})) ≃L[𝕜]
      OrdinalSpace 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 : Ordinal.{0})) ×
      OrdinalSpace 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 : Ordinal.{0})) := by
  have e := JLMS.ordinalSpaceInitialPowerSquareEquiv (𝕜 := 𝕜) Cardinal.aleph0 le_rfl
    (Ordinal.omega0 : Ordinal.{0}) (Ordinal.nat_lt_omega0 2).le (by simp)
  rw [Cardinal.ord_aleph0] at e
  exact e

def ordinalMiddlePowerMultipleEquiv (β : Ordinal.{0}) (hlo : Ordinal.omega0 ≤ β)
    (hhi : β < Ordinal.omega0 ^ (2 : Ordinal.{0})) (n : ℕ) :
    OrdinalSpace 𝕜 (Ordinal.omega0 ^ β * ((n+1 : ℕ) : Ordinal)) ≃L[𝕜]
      OrdinalSpace 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 : Ordinal.{0})) := by
  have hinf : Ordinal.omega0 ≤ Ordinal.omega0 ^ β := by
    simpa only [Ordinal.opow_one] using Ordinal.opow_le_opow_right Ordinal.omega0_pos
      (Ordinal.one_lt_omega0.le.trans hlo)
  exact (JLMS.ordinalSpaceFinitePower (𝕜 := 𝕜) _ hinf n).trans
    ((ContinuousLinearEquiv.piCongrRight (fun _ : Fin (n+1) => ordinalMiddlePowerEquiv β hlo hhi)).trans
      (finitePiCollapseEquiv ordinalMiddleSquareEquiv n))

def ordinalMiddleEquiv (α : Ordinal.{0})
    (hlo : Ordinal.omega0 ^ (Ordinal.omega0 : Ordinal.{0}) ≤ α)
    (hhi : α < Ordinal.omega0 ^ (Ordinal.omega0 ^ (2 : Ordinal.{0}))) :
    OrdinalSpace 𝕜 α ≃L[𝕜] OrdinalSpace 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 : Ordinal.{0})) := by
  refine Classical.choice ?_
  have hα : α ≠ 0 := (Ordinal.opow_pos _ Ordinal.omega0_pos |>.trans_le hlo).ne'
  let β := Ordinal.log Ordinal.omega0 α
  have hβ : Ordinal.omega0 ≤ β := Ordinal.le_log_of_opow_le Ordinal.one_lt_omega0 hlo
  have hβhi : β < Ordinal.omega0 ^ (2 : Ordinal.{0}) :=
    (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 hα).mp hhi
  let η := α / (Ordinal.omega0 ^ β)
  have hη : 0 < η := Ordinal.div_opow_log_pos Ordinal.omega0 hα
  have hηω : η < Ordinal.omega0 := Ordinal.div_opow_log_lt α Ordinal.one_lt_omega0
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hηω
  have hnpos : 0 < n := by
    have : (0 : Ordinal.{0}) < (n : Ordinal) := by simpa only [← hn] using hη
    exact_mod_cast this
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
  let ρ := α % (Ordinal.omega0 ^ β)
  have hρ : ρ < Ordinal.omega0 ^ β :=
    Ordinal.mod_lt _ (Ordinal.opow_pos β Ordinal.omega0_pos).ne'
  have he : α = Ordinal.omega0 ^ β * η + ρ := (Ordinal.div_add_mod α _).symm
  let er : OrdinalSpace 𝕜 (Ordinal.omega0 ^ β * η + ρ) ≃L[𝕜]
      OrdinalSpace 𝕜 (Ordinal.omega0 ^ β * η) := by
    have e := JLMS.ordinalSpacePowerRemainder (𝕜 := 𝕜) Cardinal.aleph0 le_rfl β η ρ
      (Ordinal.one_lt_omega0.le.trans hβ) hη (by simpa only [Cardinal.ord_aleph0] using hρ)
    rw [Cardinal.ord_aleph0] at e
    exact e
  let ep : OrdinalSpace 𝕜 (Ordinal.omega0 ^ β * η) ≃L[𝕜]
      OrdinalSpace 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 : Ordinal.{0})) := by
    rw [hn]
    exact ordinalMiddlePowerMultipleEquiv β hβ hβhi m
  exact ⟨(JLMS.ordinalSpaceCongrIsometry (𝕜 := 𝕜) he).toContinuousLinearEquiv.trans (er.trans ep)⟩

end Posets
