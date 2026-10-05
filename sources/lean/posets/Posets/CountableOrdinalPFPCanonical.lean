import Posets.CountableOrdinalPFPPreservation
import Posets.OrdinalIdealTransportOmega
import ThesisCommon.Analysis.OrdinalBakerPowers

/-! The full primary factorisation property for the canonical countable
ordinal representatives C[0,ω^(ω^η)], over either real or complex scalars. -/

noncomputable section
open Set Topology TopologicalSpace Order ThesisCommon
open scoped Ordinal
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

theorem countableCanonicalOrdinal_hasPFP (η : Ordinal.{0})
    (hcη : η.card ≤ Cardinal.aleph0) : HasPFP 𝕜 (OrdinalSpace 𝕜 (ω ^ (ω ^ η))) := by
  by_cases hη : η = 0
  · subst η
    rw [Ordinal.opow_zero, Ordinal.opow_one]
    exact (ordinalOmega_hasUPFP (𝕜 := 𝕜)).hasPFP
  let γ : Ordinal.{0} := ω ^ η
  have hγ : IsSuccLimit γ := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hη
  have hcγ : γ.card ≤ Cardinal.aleph0 := by
    dsimp only [γ]
    rw [Ordinal.card_omega0_opow hη]
    exact max_le le_rfl hcη
  have hcθ : (ω ^ γ).card ≤ Cardinal.aleph0 := by
    rw [Ordinal.card_omega0_opow hγ.ne_bot]
    exact max_le le_rfl hcγ
  have hθ : ω ^ γ ∈ ordinalTowerLevel (ω ^ γ) γ := by
    change ω ^ γ ∈ ordinalDerived (Iic (ω ^ γ)) γ
    rw [ordinalDerived_Iic_power_self hγ.ne_bot]
    exact mem_singleton _
  have hmul : ∀ β < γ, ∀ N : ℕ, β * N < γ := fun β hβ N =>
    Ordinal.mul_lt_omega0_opow (Ordinal.pos_iff_ne_zero.mpr hη) hβ (Ordinal.nat_lt_omega0 N)
  intro T
  let e := ordinalIicContinuousCZeroEquiv (𝕜 := 𝕜) (ω ^ γ)
  let T' := e.toContinuousLinearMap.comp (T.comp e.symm.toContinuousLinearMap)
  let S' := e.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id 𝕜 _ - T).comp e.symm.toContinuousLinearMap)
  have hTS : T' + S' = ContinuousLinearMap.id 𝕜 _ := by
    apply ContinuousLinearMap.ext
    intro f
    change e (T (e.symm f)) + e (e.symm f - T (e.symm f)) = f
    rw [← map_add]
    have hf : T (e.symm f) + (e.symm f - T (e.symm f)) = e.symm f := by abel
    rw [hf, e.apply_symm_apply]
  obtain ⟨b, I, R, hR⟩ := ordinalTower_identity_factorization hcθ hcγ hγ hθ hmul T' S' hTS
  cases b with
  | false =>
    refine Or.inr ⟨R.comp e.toContinuousLinearMap, e.symm.toContinuousLinearMap.comp I, ?_⟩
    apply ContinuousLinearMap.ext
    intro f
    have hf := congrArg (fun L : OrdinalContinuous 𝕜 (ω ^ γ) →L[𝕜] _ => L f) hR
    exact hf
  | true =>
    refine Or.inl ⟨R.comp e.toContinuousLinearMap, e.symm.toContinuousLinearMap.comp I, ?_⟩
    apply ContinuousLinearMap.ext
    intro f
    have hf := congrArg (fun L : OrdinalContinuous 𝕜 (ω ^ γ) →L[𝕜] _ => L f) hR
    exact hf

end Posets
