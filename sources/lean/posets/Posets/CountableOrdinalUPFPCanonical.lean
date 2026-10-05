import Posets.CountableOrdinalUPFPPreservation
import Posets.CountableOrdinalNormalization
import Posets.OrdinalIdealTransportOmega
import ThesisCommon.Analysis.OrdinalBakerPowers

/-! Uniform primary factorisation for every infinite countable ordinal
coefficient space. The fixed-model quantitative tower bound is chosen before
the operator; actual ordinal normalisation then transports the property. -/
noncomputable section
open Set Topology TopologicalSpace Order ThesisCommon
open scoped Ordinal
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

theorem countableCanonicalOrdinal_hasUPFP (η : Ordinal.{0})
    (hcη : η.card ≤ Cardinal.aleph0) : HasUPFP 𝕜 (OrdinalSpace 𝕜 (ω ^ (ω ^ η))) := by
  by_cases hη : η = 0
  · subst η
    rw [Ordinal.opow_zero, Ordinal.opow_one]
    exact ordinalOmega_hasUPFP
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
  let e := ordinalIicContinuousCZeroEquiv (𝕜 := 𝕜) (ω ^ γ)
  let C := ordinalTowerFactorBound (𝕜 := 𝕜) γ hγ hcγ
  let d := ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖
  have h : HasUPFP 𝕜 (JLMS.CZero 𝕜 (Iic (ω ^ γ))) := by
    refine ⟨max 1 (C * d), le_max_left _ _, ?_⟩
    intro T
    obtain ⟨b, hb⟩ := ordinalTower_identity_factorization_with_bound hcθ hcγ hγ hθ hmul
      T (ContinuousLinearMap.id 𝕜 _ - T) (by abel)
    have hb' := (hb.target_equiv e).mono (le_max_right 1 (C * d))
    cases b with
    | false => exact Or.inr hb'
    | true => exact Or.inl hb'
  exact h.of_equiv e.symm

theorem countableOrdinal_hasUPFP (α : Ordinal.{0})
    (hcα : α.card ≤ Cardinal.aleph0) (hα : Ordinal.omega0 ≤ α) :
    HasUPFP 𝕜 (OrdinalSpace 𝕜 α) := by
  obtain ⟨η, hcη, ⟨e⟩⟩ := exists_countableOrdinal_normal_form (𝕜 := 𝕜) α hcα hα
  exact (countableCanonicalOrdinal_hasUPFP η hcη).of_equiv e.symm

end Posets
