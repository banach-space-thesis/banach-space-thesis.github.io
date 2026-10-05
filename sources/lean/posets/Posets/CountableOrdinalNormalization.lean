import Posets.CountableOrdinalNormalizationPowers

/-! Every infinite countable ordinal function space is isomorphic to an
actual model C[0,ω^(ω^η)]. Only explicit interval and c₀ decompositions
are used; primary factorisation is not an input to this normalisation. -/
noncomputable section
namespace Posets
open ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 800000

def countablePowerBandEquiv (δ : Ordinal.{0}) (hδ : 2 ≤ δ)
    (hcδ : δ.card ≤ Cardinal.aleph0) (β : Ordinal.{0}) (hlo : δ ≤ β)
    (hhi : β < δ * Ordinal.omega0) :
    OrdinalSpace 𝕜 (Ordinal.omega0 ^ β) ≃L[𝕜] OrdinalSpace 𝕜 (Ordinal.omega0 ^ δ) :=
  (JLMS.ordinalSpaceEndpointZeroEquiv (𝕜 := 𝕜) _
    (countableNormal_power_infinite ((one_le_two.trans hδ).trans hlo))).trans
    ((countablePowerEndpointBandEquiv δ hδ hcδ β hlo hhi).trans
      (JLMS.ordinalSpaceEndpointZeroEquiv (𝕜 := 𝕜) _
        (countableNormal_power_infinite (one_le_two.trans hδ))).symm)

def countablePowerModelSquareEquiv (δ : Ordinal.{0}) (hδ : 2 ≤ δ)
    (hcδ : δ.card ≤ Cardinal.aleph0) :
    OrdinalSpace 𝕜 (Ordinal.omega0 ^ δ) ≃L[𝕜]
      OrdinalSpace 𝕜 (Ordinal.omega0 ^ δ) × OrdinalSpace 𝕜 (Ordinal.omega0 ^ δ) := by
  have e := JLMS.ordinalSpaceInitialPowerSquareEquiv (𝕜 := 𝕜)
    Cardinal.aleph0 le_rfl δ hδ hcδ
  rw [Cardinal.ord_aleph0] at e
  exact e

def countablePowerBandMultipleEquiv (δ : Ordinal.{0}) (hδ : 2 ≤ δ)
    (hcδ : δ.card ≤ Cardinal.aleph0) (β : Ordinal.{0}) (hlo : δ ≤ β)
    (hhi : β < δ * Ordinal.omega0) (n : ℕ) :
    OrdinalSpace 𝕜 (Ordinal.omega0 ^ β * ((n+1 : ℕ) : Ordinal)) ≃L[𝕜]
      OrdinalSpace 𝕜 (Ordinal.omega0 ^ δ) :=
  (JLMS.ordinalSpaceFinitePower (𝕜 := 𝕜) _
    (countableNormal_power_infinite ((one_le_two.trans hδ).trans hlo)) n).trans
    ((ContinuousLinearEquiv.piCongrRight (fun _ : Fin (n+1) =>
      countablePowerBandEquiv δ hδ hcδ β hlo hhi)).trans
        (finitePiCollapseEquiv (countablePowerModelSquareEquiv δ hδ hcδ) n))

def countableOrdinalBandEquiv (δ : Ordinal.{0}) (hδ : 2 ≤ δ)
    (hcδ : δ.card ≤ Cardinal.aleph0) (α : Ordinal.{0})
    (hlo : Ordinal.omega0 ^ δ ≤ α)
    (hhi : α < Ordinal.omega0 ^ (δ * Ordinal.omega0)) :
    OrdinalSpace 𝕜 α ≃L[𝕜] OrdinalSpace 𝕜 (Ordinal.omega0 ^ δ) := by
  refine Classical.choice ?_
  have hα : α ≠ 0 := (Ordinal.opow_pos _ Ordinal.omega0_pos |>.trans_le hlo).ne'
  let β := Ordinal.log Ordinal.omega0 α
  have hβ : δ ≤ β := Ordinal.le_log_of_opow_le Ordinal.one_lt_omega0 hlo
  have hβhi : β < δ * Ordinal.omega0 :=
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
  have hρ : ρ < Ordinal.omega0 ^ β := Ordinal.mod_lt _ (Ordinal.opow_pos β Ordinal.omega0_pos).ne'
  have he : α = Ordinal.omega0 ^ β * η + ρ := (Ordinal.div_add_mod α _).symm
  let er : OrdinalSpace 𝕜 (Ordinal.omega0 ^ β * η + ρ) ≃L[𝕜]
      OrdinalSpace 𝕜 (Ordinal.omega0 ^ β * η) := by
    have e := JLMS.ordinalSpacePowerRemainder (𝕜 := 𝕜) Cardinal.aleph0 le_rfl β η ρ
      ((one_le_two.trans hδ).trans hβ) hη (by simpa only [Cardinal.ord_aleph0] using hρ)
    rw [Cardinal.ord_aleph0] at e
    exact e
  let ep : OrdinalSpace 𝕜 (Ordinal.omega0 ^ β * η) ≃L[𝕜]
      OrdinalSpace 𝕜 (Ordinal.omega0 ^ δ) := by
    rw [hn]
    exact countablePowerBandMultipleEquiv δ hδ hcδ β hβ hβhi m
  exact ⟨(JLMS.ordinalSpaceCongrIsometry (𝕜 := 𝕜) he).toContinuousLinearEquiv.trans (er.trans ep)⟩

theorem exists_countableOrdinal_normal_form (α : Ordinal.{0})
    (hcα : α.card ≤ Cardinal.aleph0) (hα : Ordinal.omega0 ≤ α) :
    ∃ η : Ordinal.{0}, η.card ≤ Cardinal.aleph0 ∧
      Nonempty (OrdinalSpace 𝕜 α ≃L[𝕜]
        OrdinalSpace 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 ^ η))) := by
  by_cases hsmall : α < Ordinal.omega0 ^ (Ordinal.omega0 : Ordinal.{0})
  · refine ⟨0, by simp, ?_⟩
    change Nonempty (OrdinalSpace 𝕜 α ≃L[𝕜]
      OrdinalSpace 𝕜 (Ordinal.omega0 ^ (Ordinal.omega0 ^ (0 : Ordinal.{0}))))
    rw [Ordinal.opow_zero, Ordinal.opow_one]
    exact ⟨(ordinalBelowOmegaOmegaCZeroEquiv α hα hsmall).trans ordinalOmegaCZeroEquiv.symm⟩
  · let β := Ordinal.log Ordinal.omega0 α
    let η := Ordinal.log Ordinal.omega0 β
    have hβ : Ordinal.omega0 ≤ β := Ordinal.le_log_of_opow_le Ordinal.one_lt_omega0
      (le_of_not_gt hsmall)
    have hη : 1 ≤ η := Ordinal.le_log_of_opow_le Ordinal.one_lt_omega0 (by simpa using hβ)
    have hcβ : β.card ≤ Cardinal.aleph0 :=
      (Ordinal.card_le_card (Ordinal.log_le_self _ _)).trans hcα
    have hcη : η.card ≤ Cardinal.aleph0 :=
      (Ordinal.card_le_card (Ordinal.log_le_self _ _)).trans hcβ
    have hδ : 2 ≤ Ordinal.omega0 ^ η :=
      (Ordinal.nat_lt_omega0 2).le.trans (countableNormal_power_infinite hη)
    have hlo : Ordinal.omega0 ^ (Ordinal.omega0 ^ η) ≤ α :=
      (Ordinal.opow_le_opow_right Ordinal.omega0_pos
        (Ordinal.opow_log_le_self Ordinal.omega0 (Ordinal.omega0_pos.trans_le hβ).ne')).trans
          (Ordinal.opow_log_le_self Ordinal.omega0 (Ordinal.omega0_pos.trans_le hα).ne')
    have hβhi : β < Ordinal.omega0 ^ η * Ordinal.omega0 := by
      simpa only [Ordinal.opow_succ] using Ordinal.lt_opow_succ_log_self Ordinal.one_lt_omega0 β
    have hhi : α < Ordinal.omega0 ^ (Ordinal.omega0 ^ η * Ordinal.omega0) :=
      (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 (Ordinal.omega0_pos.trans_le hα).ne').mpr hβhi
    exact ⟨η, hcη, ⟨countableOrdinalBandEquiv _ hδ (omega_power_card_le_aleph0 hcη) α hlo hhi⟩⟩

end Posets
