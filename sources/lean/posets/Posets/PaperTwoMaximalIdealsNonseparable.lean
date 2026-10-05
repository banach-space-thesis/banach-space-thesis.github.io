import JLMS.OrdinalHeadProjection
import ThesisCommon.Analysis.SequenceSpaces
import Mathlib.SetTheory.Cardinal.Regular

/-! Uncountably many separated head indicators prevent the ordinal summand
in the Section 3 example from being a quotient of the separable interval space. -/
noncomputable section
open Set ThesisCommon TopologicalSpace
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem paper_ordinal_head_dist_ge_one (α : Ordinal.{0})
    {β γ : Set.Iio α} (h : β ≠ γ) :
    1 ≤ dist (JLMS.ordinalHeadIndicator (𝕜 := 𝕜) α β.val)
      (JLMS.ordinalHeadIndicator α γ.val) := by
  have hn : β.val ≠ γ.val := fun he => h (Subtype.ext he)
  rcases lt_or_gt_of_ne hn with hb | hg
  · let x : JLMS.OrdinalInterval α := ⟨γ.val, Ordinal.zero_le _, γ.property.le⟩
    have hh := (JLMS.ordinalHeadIndicator (𝕜 := 𝕜) α β.val -
      JLMS.ordinalHeadIndicator α γ.val).norm_coe_le_norm x
    simpa [dist_eq_norm, JLMS.ordinalHeadIndicator_apply, x, not_le.mpr hb] using hh
  · let x : JLMS.OrdinalInterval α := ⟨β.val, Ordinal.zero_le _, β.property.le⟩
    have hh := (JLMS.ordinalHeadIndicator (𝕜 := 𝕜) α β.val -
      JLMS.ordinalHeadIndicator α γ.val).norm_coe_le_norm x
    simpa [dist_eq_norm, JLMS.ordinalHeadIndicator_apply, x, not_le.mpr hg] using hh

theorem paper_ordinal_nonseparable {α : Ordinal.{0}}
    (hα : Cardinal.aleph0 < α.card) : ¬SeparableSpace (JLMS.OrdinalC 𝕜 α) := by
  intro hsep
  letI := hsep
  have hd : Pairwise (fun β γ : Set.Iio α =>
      Disjoint (Metric.ball (JLMS.ordinalHeadIndicator (𝕜 := 𝕜) α β.val) (1/2))
        (Metric.ball (JLMS.ordinalHeadIndicator α γ.val) (1/2))) := by
    intro β γ hβγ
    apply Metric.ball_disjoint_ball
    linarith [paper_ordinal_head_dist_ge_one (𝕜 := 𝕜) α hβγ]
  letI : Countable (Set.Iio α) := hd.countable_of_isOpen_disjoint
    (fun _ => Metric.isOpen_ball)
    (fun β => ⟨JLMS.ordinalHeadIndicator α β.val, Metric.mem_ball_self (by norm_num)⟩)
  have hc := Cardinal.mk_le_aleph0 (α := Set.Iio α)
  rw [Ordinal.mk_Iio_ordinal] at hc
  have hc' : α.card ≤ Cardinal.aleph0 := by simpa only [Cardinal.lift_le_aleph0] using hc
  exact (not_le.mpr hα) hc'

theorem paper_nonseparable_not_complemented_in_separable
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [SeparableSpace E]
    (hF : ¬SeparableSpace F) :
    ¬∃ A : F →L[𝕜] E, ∃ B : E →L[𝕜] F,
      B.comp A = ContinuousLinearMap.id 𝕜 F := by
  rintro ⟨A, B, hBA⟩
  have hb : Function.Surjective B := fun y => ⟨A y, DFunLike.congr_fun hBA y⟩
  exact hF (hb.denseRange.separableSpace B.continuous)

end Posets
