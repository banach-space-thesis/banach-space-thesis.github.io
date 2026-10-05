import ThesisCommon.Analysis.L1ModulusRestriction

/-! For finite input measure, modulus preservation by a one-preserving L1
restriction persists under enlargement of its range. -/
noncomputable section
open MeasureTheory Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y Z Z' : Type*}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace Z']
variable {μ : Measure X} {ν : Measure Y} {η : Measure Z} {η' : Measure Z'}
variable [IsFiniteMeasure μ] [IsFiniteMeasure η] [IsFiniteMeasure η']

theorem lOneOperatorModulus_comp_eq_of_range_mono
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (J : Lp ℝ 1 η →L[ℝ] Lp ℝ 1 μ) (J' : Lp ℝ 1 η' →L[ℝ] Lp ℝ 1 μ)
    (hJ : ∀ f g, J f ≤ J g ↔ f ≤ g)
    (hJ' : ∀ f g, J' f ≤ J' g ↔ f ≤ g)
    (hone : J (lOneIndicator η univ MeasurableSet.univ) =
      lOneIndicator μ univ MeasurableSet.univ)
    (hone' : J' (lOneIndicator η' univ MeasurableSet.univ) =
      lOneIndicator μ univ MeasurableSet.univ)
    (hrange : range J ⊆ range J')
    (hmod : lOneOperatorModulus (T.comp J) = (lOneOperatorModulus T).comp J) :
    lOneOperatorModulus (T.comp J') = (lOneOperatorModulus T).comp J' := by
  let W := J '' Icc (-lOneIndicator η univ MeasurableSet.univ)
    (lOneIndicator η univ MeasurableSet.univ)
  have hW : W ⊆ Icc (-lOneIndicator μ univ MeasurableSet.univ)
      (lOneIndicator μ univ MeasurableSet.univ) := by
    rintro _ ⟨f, hf, rfl⟩
    constructor
    · simpa only [map_neg, hone] using (hJ _ _).mpr hf.1
    · simpa only [hone] using (hJ _ _).mpr hf.2
  have hsup : IsLUB (T '' W)
      (lOneOperatorModulus T (lOneIndicator μ univ MeasurableSet.univ)) := by
    have h := lOneOperatorModulus_rieszKantorovich (T.comp J)
      (lOneIndicator η univ MeasurableSet.univ) (lOneIndicator_nonneg _ _)
    rw [hmod, ContinuousLinearMap.comp_apply, hone] at h
    simpa only [W, image_image, ContinuousLinearMap.comp_apply, Function.comp_def] using h
  apply lOneOperatorModulus_comp_eq_of_witnesses T J' hJ' hone' W hW hsup
  rintro _ ⟨f, _, rfl⟩
  exact hrange (mem_range_self f)

end ThesisCommon
