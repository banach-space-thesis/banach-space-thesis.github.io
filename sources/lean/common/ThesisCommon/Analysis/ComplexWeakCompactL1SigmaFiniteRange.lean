import ThesisCommon.Analysis.WeakCompactL1SigmaFiniteRange
import ThesisCommon.Analysis.ComplexL1WeakUniformIntegrable

/-! A genuinely weakly compact complex operator has one measurable
sigma-finite output support, obtained from its full real coordinates. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon
variable {Y E : Type*} [MeasurableSpace Y] {ν : Measure Y}
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem IsWeaklyCompactOperator.exists_sigmaFinite_range_part_complex
    {T : E →L[ℂ] Lp ℂ 1 ν} (hT : IsWeaklyCompactOperator T) :
    ∃ Θ : Set Y, MeasurableSet Θ ∧ SigmaFinite (ν.restrict Θ) ∧
      ∀ f, T f =ᵐ[ν.restrict Θᶜ] 0 := by
  obtain ⟨A, hA, hσA, hr⟩ :=
    (hT.restrictScalars_real.comp_left (complexL1Re ν)).exists_sigmaFinite_range_part
  obtain ⟨B, hB, hσB, hi⟩ :=
    (hT.restrictScalars_real.comp_left (complexL1Im ν)).exists_sigmaFinite_range_part
  letI := hσA
  letI := hσB
  refine ⟨A ∪ B, hA.union hB, inferInstance, fun f => ?_⟩
  have hr' := (hr f).filter_mono (ae_mono (Measure.restrict_mono
    (compl_subset_compl.mpr (show A ⊆ A ∪ B from subset_union_left)) (le_rfl : ν ≤ ν)))
  have hi' := (hi f).filter_mono (ae_mono (Measure.restrict_mono
    (compl_subset_compl.mpr (show B ⊆ A ∪ B from subset_union_right)) (le_rfl : ν ≤ ν)))
  filter_upwards [hr', hi', ae_restrict_of_ae (complexL1Re_coe (T f)),
    ae_restrict_of_ae (complexL1Im_coe (T f))] with y hyr hyi hcr hci
  change complexL1Re ν (T f) y = 0 at hyr
  change complexL1Im ν (T f) y = 0 at hyi
  apply Complex.ext
  · exact hcr.symm.trans hyr
  · exact hci.symm.trans hyi

end ThesisCommon
