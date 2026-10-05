import PFP.OrdinalMatrixSmallDomain
import JLMS.OrdinalColumnLocality
import ThesisCommon.Analysis.ContinuousMapPullback

/-! Operators from a large ordinal to a smaller one annihilate a common late
endpoint-zero tail. The proof uses the genuine atomic operator rows. -/
noncomputable section
namespace Posets.UniverseRegularMatrix
universe ordU
open Posets.UniverseRegularInitial
open JLMS
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096

theorem exists_smallCodomain_operator_annihilating_tail {κ σ : Ordinal.{ordU}}
    (hκ : Cardinal.aleph0 < κ.cof) (hσ : σ.card < κ.cof)
    (T : OrdinalC 𝕜 κ →L[𝕜] OrdinalC 𝕜 σ) :
    ∃ β < κ, ∀ f : OrdinalC 𝕜 κ,
      (∀ x : OrdinalInterval κ, x.val ≤ β → f x = 0) →
      f ⟨κ, Ordinal.zero_le _, le_rfl⟩ = 0 → T f = 0 := by
  have hσκ : σ < κ := by
    by_contra h
    exact hσ.not_ge ((Ordinal.cof_le_card κ).trans (Ordinal.card_le_card (le_of_not_gt h)))
  have hsucc : (Order.succ σ).card < κ.cof := by
    rw [Ordinal.card_succ]
    exact Cardinal.add_lt_of_lt hκ.le hσ (Cardinal.one_lt_aleph0.trans hκ)
  let g : C(OrdinalInterval κ, OrdinalInterval σ) :=
    (ordinalIntervalClamp σ).comp ⟨Subtype.val, continuous_subtype_val⟩
  let E : OrdinalC 𝕜 σ →L[𝕜] OrdinalC 𝕜 κ := ThesisCommon.continuousMapPullback g
  let S := E.comp T
  obtain ⟨β, hβ, hcut⟩ := exists_ordinalOperator_strip_cutoff hκ
    (Order.succ_le_iff.mpr hσκ) hsucc S
  refine ⟨β, hβ, ?_⟩
  intro f hhead htop
  ext x
  let x' : OrdinalInterval κ := ⟨x.val, x.property.1, x.property.2.trans hσκ.le⟩
  have hx' : x'.val < Order.succ σ := Order.lt_succ_iff.mpr x.property.2
  have hz : S f x' = 0 := by
    rw [← (ordinalOperatorRow_hasSum κ S f x').tsum_eq]
    calc
      _ = ∑' _ : OrdinalInterval κ, (0 : 𝕜) := by
        apply tsum_congr
        intro y
        by_cases hy : y.val ≤ β
        · rw [hhead y hy, mul_zero]
        · by_cases hytop : y.val = κ
          · have he : y = (⟨κ, Ordinal.zero_le _, le_rfl⟩ : OrdinalInterval κ) := Subtype.ext hytop
            rw [he, htop, mul_zero]
          · rw [hcut x' hx' y (lt_of_not_ge hy) (lt_of_le_of_ne y.property.2 hytop), zero_mul]
      _ = 0 := tsum_zero
  have hgx : g x' = x := by
    apply Subtype.ext
    exact min_eq_left x.property.2
  change T f (g x') = 0 at hz
  simpa only [hgx] using hz

theorem exists_smallCodomain_operator_tail_projection {κ σ : Ordinal.{ordU}}
    (hκ : Cardinal.aleph0 < κ.cof) (hσ : σ.card < κ.cof)
    (T : OrdinalC 𝕜 κ →L[𝕜] OrdinalC 𝕜 σ) :
    ∃ β < κ, ∀ f : OrdinalC 𝕜 κ,
      f ⟨κ, Ordinal.zero_le _, le_rfl⟩ = 0 →
      T (f - ordinalHeadProjection κ β f) = 0 := by
  obtain ⟨β, hβ, hkill⟩ := exists_smallCodomain_operator_annihilating_tail hκ hσ T
  refine ⟨β, hβ, fun f hf => hkill _ ?_ ?_⟩
  · intro x hx
    simp [ordinalHeadProjection_apply, hx]
  · simp [ordinalHeadProjection_apply, not_le_of_gt hβ, hf]

end Posets.UniverseRegularMatrix


