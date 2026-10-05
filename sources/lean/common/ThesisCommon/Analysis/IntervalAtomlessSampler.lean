import ThesisCommon.Analysis.IntervalProbabilitySampler
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! The actual interval sampler is injective for every atomless probability
measure, including measures with gaps in their support. A plateau would send
a positive-length Lebesgue interval into a singleton of positive mass. -/
noncomputable section
open MeasureTheory Set
namespace ThesisCommon
variable (μ : Measure unitInterval) [IsProbabilityMeasure μ] [NoAtoms μ]

theorem intervalProbabilitySampler_strictMono : StrictMono (intervalProbabilitySampler μ) := by
  intro s t hst
  have hmono := intervalProbabilitySampler_monotone μ
  by_contra h
  have he : intervalProbabilitySampler μ s = intervalProbabilitySampler μ t :=
    le_antisymm (hmono hst.le) (le_of_not_gt h)
  have hsub : Icc s t ⊆ intervalProbabilitySampler μ ⁻¹' {intervalProbabilitySampler μ s} := by
    intro x hx
    change intervalProbabilitySampler μ x = intervalProbabilitySampler μ s
    exact le_antisymm ((hmono hx.2).trans he.ge) (hmono hx.1)
  have hzero : (volume : Measure unitInterval)
      (intervalProbabilitySampler μ ⁻¹' {intervalProbabilitySampler μ s}) = 0 := by
    rw [← Measure.map_apply (intervalProbabilitySampler_measurable μ) (measurableSet_singleton _),
      intervalProbabilitySampler_map, measure_singleton]
  have hm : (volume : Measure unitInterval) (Icc s t) ≤
      volume (intervalProbabilitySampler μ ⁻¹' {intervalProbabilitySampler μ s}) := measure_mono hsub
  rw [hzero, unitInterval.volume_Icc] at hm
  exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr (show (s : ℝ) < (t : ℝ) from hst))).not_ge hm

theorem intervalProbabilitySampler_measurableEmbedding :
    MeasurableEmbedding (intervalProbabilitySampler μ) :=
  (intervalProbabilitySampler_measurable μ).measurableEmbedding
    (intervalProbabilitySampler_strictMono μ).injective

end ThesisCommon
