import Posets.OrdinalIdealTransportCountablePowers
import JLMS.OrdinalSpacePowerReduction

/-! The full primary-factorisation and maximal-ideal assertions for
ω ≤ α < ω^ω, obtained from the actual c₀ models and ordinal division. -/
noncomputable section
namespace Posets
open ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000

def finitePiCollapseEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (e : E ≃L[𝕜] E × E) (n : ℕ) : (Fin (n+1) → E) ≃L[𝕜] E := by
  induction n with
  | zero => exact ContinuousLinearEquiv.piUnique 𝕜 (fun _ : Fin 1 => E)
  | succ n ih =>
    exact (Fin.consEquivL 𝕜 (fun _ : Fin (n+1+1) => E)).symm.trans
      (((ContinuousLinearEquiv.refl 𝕜 E).prodCongr ih).trans e.symm)

def ordinalFinitePowerMultipleCZeroEquiv (n m : ℕ) :
    OrdinalSpace 𝕜
      (Ordinal.omega0 ^ ((n+1 : ℕ) : Ordinal.{0}) * ((m+1 : ℕ) : Ordinal)) ≃L[𝕜]
      CZeroSum 𝕜 := by
  have hn : (1 : Ordinal.{0}) ≤ ((n+1 : ℕ) : Ordinal) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hinf : Ordinal.omega0 ≤ Ordinal.omega0 ^ ((n+1 : ℕ) : Ordinal.{0}) := by
    simpa only [Ordinal.opow_one] using
      Ordinal.opow_le_opow_right Ordinal.omega0_pos hn
  let e := (ordinalFinitePowerCZeroEquiv (𝕜 := 𝕜) n).trans ordinalOmegaCZeroEquiv.symm
  exact (JLMS.ordinalSpaceFinitePower (𝕜 := 𝕜) _ hinf m).trans
    ((ContinuousLinearEquiv.piCongrRight (fun _ : Fin (m+1) => e)).trans
      ((finitePiCollapseEquiv JLMS.ordinalSpaceOmegaSquareEquiv m).trans ordinalOmegaCZeroEquiv))

def ordinalBelowOmegaOmegaCZeroEquiv (α : Ordinal.{0}) (hlo : Ordinal.omega0 ≤ α)
    (hhi : α < Ordinal.omega0 ^ Ordinal.omega0) : OrdinalSpace 𝕜 α ≃L[𝕜] CZeroSum 𝕜 := by
  refine Classical.choice ?_
  have hα : α ≠ 0 := (Ordinal.omega0_pos.trans_le hlo).ne'
  let β := Ordinal.log Ordinal.omega0 α
  have hβ : 1 ≤ β := Ordinal.le_log_of_opow_le Ordinal.one_lt_omega0 (by simpa using hlo)
  have hβω : β < Ordinal.omega0 :=
    (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 hα).mp hhi
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hβω
  have hnpos : 0 < n := by
    have : (0 : Ordinal.{0}) < (n : Ordinal) := by simpa only [← hn] using lt_of_lt_of_le zero_lt_one hβ
    exact_mod_cast this
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
  let η := α / (Ordinal.omega0 ^ β)
  have hη : 0 < η := Ordinal.div_opow_log_pos Ordinal.omega0 hα
  have hηω : η < Ordinal.omega0 := Ordinal.div_opow_log_lt α Ordinal.one_lt_omega0
  obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp hηω
  have hmpos : 0 < m := by
    have : (0 : Ordinal.{0}) < (m : Ordinal) := by simpa only [← hm] using hη
    exact_mod_cast this
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
  let ρ := α % (Ordinal.omega0 ^ β)
  have hρ : ρ < Ordinal.omega0 ^ β :=
    Ordinal.mod_lt _ (Ordinal.opow_pos β Ordinal.omega0_pos).ne'
  have he : α = Ordinal.omega0 ^ β * η + ρ := (Ordinal.div_add_mod α _).symm
  let er : OrdinalSpace 𝕜 (Ordinal.omega0 ^ β * η + ρ) ≃L[𝕜]
      OrdinalSpace 𝕜 (Ordinal.omega0 ^ β * η) := by
    have hr := JLMS.ordinalSpacePowerRemainder (𝕜 := 𝕜) Cardinal.aleph0 le_rfl β η ρ
      hβ hη (by simpa only [Cardinal.ord_aleph0] using hρ)
    rw [Cardinal.ord_aleph0] at hr
    exact hr
  let ep : OrdinalSpace 𝕜 (Ordinal.omega0 ^ β * η) ≃L[𝕜] CZeroSum 𝕜 := by
    rw [hn, hm]
    exact ordinalFinitePowerMultipleCZeroEquiv k l
  exact ⟨(JLMS.ordinalSpaceCongrIsometry (𝕜 := 𝕜) he).toContinuousLinearEquiv.trans
    (er.trans ep)⟩

theorem ordinalBelowOmegaOmega_hasUPFP (α : Ordinal.{0}) (hlo : Ordinal.omega0 ≤ α)
    (hhi : α < Ordinal.omega0 ^ Ordinal.omega0) : HasUPFP 𝕜 (OrdinalSpace 𝕜 α) :=
  scalar_cZero_hasUPFP.of_equiv (ordinalBelowOmegaOmegaCZeroEquiv α hlo hhi).symm

theorem proposition_3_1_below_omega_omega (α : Ordinal.{0})
    (hhi : α < Ordinal.omega0 ^ Ordinal.omega0) : Proposition_3_1 𝕜 α := by
  intro hlo
  letI : Nonempty (Set.Icc (0 : Ordinal.{0}) α) := ⟨⟨0, le_rfl, Ordinal.zero_le _⟩⟩
  have h := uniqueMaximal_of_hasPFP (ordinalBelowOmegaOmega_hasUPFP (𝕜 := 𝕜) α hlo hhi).hasPFP
  exact ⟨h.2, fun _ => h.1⟩

end Posets
