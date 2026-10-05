import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-! An actual measurable sampler for every probability measure on [0,1].
This measure-only inverse-CDF construction adapts the later mathlib kernel
representation proof of Gaëtan Serré and Rémy Degenne to the pinned library.
No atomlessness, measure-space isomorphism, or representation is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter unitInterval
open scoped Topology
namespace ThesisCommon
variable (μ : Measure unitInterval)

def intervalProbabilitySampler (t : unitInterval) : unitInterval :=
  sSup {x | μ.real (Icc 0 x) < (t : ℝ)}

theorem intervalProbabilitySampler_monotone : Monotone (intervalProbabilitySampler μ) := by
  intro s t hst
  apply sSup_le
  intro x hx
  exact le_sSup (show μ.real (Icc 0 x) < (t : ℝ) from
    lt_of_lt_of_le hx (show (s : ℝ) ≤ (t : ℝ) from hst))

theorem intervalProbabilitySampler_measurable : Measurable (intervalProbabilitySampler μ) :=
  (intervalProbabilitySampler_monotone μ).measurable

variable [IsProbabilityMeasure μ]

theorem intervalProbabilitySampler_le_iff (t x : unitInterval) :
    intervalProbabilitySampler μ t ≤ x ↔ (t : ℝ) ≤ μ.real (Icc 0 x) := by
  constructor
  · intro ht
    by_cases hx : x = 1
    · simp [hx, ← unitInterval.univ_eq_Icc, t.property.2]
    let g := fun y : unitInterval => μ.real (Icc 0 y)
    letI : NeBot (𝓝[>] x) := nhdsGT_neBot_of_exists_gt ⟨1, lt_of_le_of_ne x.property.2 hx⟩
    refine le_of_tendsto_of_tendsto (b := 𝓝[>] x) (g := g) continuousWithinAt_const ?_ ?_
    · let h := cdf (μ.map Subtype.val)
      have hh := continuousWithinAt_Ioi_iff_Ici.mpr (h.right_continuous x)
      simp_rw [g, ← unitInterval.cdf_eq_real μ]
      exact hh.comp (Continuous.continuousWithinAt (by fun_prop)) (fun y hy => hy)
    · refine eventually_nhdsWithin_of_forall fun y hy => ?_
      by_contra! h
      have hh := (sSup_le_iff.mp ht) y h
      exact (not_le_of_gt hy) hh
  · intro ht
    apply sSup_le_iff.mpr
    intro c hc
    by_contra! h
    have hm : μ.real (Icc 0 x) ≤ μ.real (Icc 0 c) := measureReal_mono (by gcongr)
    exact (not_lt_of_ge (ht.trans hm)) hc

theorem intervalProbabilitySampler_map :
    (volume : Measure unitInterval).map (intervalProbabilitySampler μ) = μ := by
  apply Measure.ext_of_Iic
  intro x
  have hx : μ.real (Icc 0 x) ∈ (unitInterval : Set ℝ) :=
    ⟨measureReal_nonneg, measureReal_le_one⟩
  have he : intervalProbabilitySampler μ ⁻¹' Iic x = Iic (⟨_, hx⟩ : unitInterval) := by
    ext t
    exact intervalProbabilitySampler_le_iff μ t x
  rw [Measure.map_apply (intervalProbabilitySampler_measurable μ) measurableSet_Iic, he,
    unitInterval.volume_Iic]
  change ENNReal.ofReal (μ (Icc 0 x)).toReal = μ (Iic x)
  rw [ENNReal.ofReal_toReal (measure_ne_top μ _)]
  congr 1
  ext t
  simp

theorem intervalProbabilitySampler_measurePreserving :
    MeasurePreserving (intervalProbabilitySampler μ) (volume : Measure unitInterval) μ :=
  ⟨intervalProbabilitySampler_measurable μ, intervalProbabilitySampler_map μ⟩

end ThesisCommon
