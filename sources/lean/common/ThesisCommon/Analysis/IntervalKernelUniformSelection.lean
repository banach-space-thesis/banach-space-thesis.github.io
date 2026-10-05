import ThesisCommon.Analysis.IntervalKernelResidualMeasurable
import ThesisCommon.Analysis.IntervalKernelAtomSelection
import Mathlib.Topology.UniformSpace.UniformApproximation

/-! A compact positive-measure selection with continuous large atom and uniform residual control.
This is a diagonal-atom localization construction, not an identification with Weis's original proof. -/
noncomputable section
open Filter Topology MeasureTheory
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem positive_measure_diff_of_half_bound (ν : Measure UnitInterval) [IsFiniteMeasure ν]
    {A E : Set UnitInterval} (hA : 0 < ν A) (hEA : E ⊆ A) (hE : MeasurableSet E)
    (hbound : ν E ≤ ENNReal.ofReal (ν.real A / 2)) : 0 < ν (A \ E) := by
  have hAr : 0 < ν.real A := ENNReal.toReal_pos hA.ne' (measure_ne_top _ _)
  have hEr : ν.real E ≤ ν.real A / 2 :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hd : 0 < ν.real (A \ E) := by
    rw [measureReal_diff hEA hE]
    linarith
  exact (ENNReal.toReal_pos_iff.mp hd).1

theorem intervalKernelResidual_positive_uniform
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜)
    (ν : Measure UnitInterval) [IsFiniteMeasure ν] {A : Set UnitInterval}
    (hA : MeasurableSet A) (hpos : 0 < ν A) :
    ∃ D ⊆ A, MeasurableSet D ∧ 0 < ν D ∧
      TendstoUniformlyOn (intervalKernelResidualMass T) (fun _ => 0) atTop D := by
  have hhalf : 0 < ν.real A / 2 := half_pos (ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _))
  obtain ⟨E, hEA, hE, hbound, hunif⟩ := intervalKernelResidual_egorov T ν hA hhalf
  exact ⟨A \ E, Set.diff_subset, hA.diff hE,
    positive_measure_diff_of_half_bound ν hpos hEA hE hbound, hunif⟩

theorem intervalOperatorAtom_positive_continuous
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜)
    (ν : Measure UnitInterval) [IsFiniteMeasure ν] {A : Set UnitInterval}
    (hA : MeasurableSet A) (hpos : 0 < ν A) :
    ∃ D ⊆ A, MeasurableSet D ∧ 0 < ν D ∧ ContinuousOn (intervalOperatorAtom T) D := by
  have hhalf : 0 < ν.real A / 2 := half_pos (ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _))
  obtain ⟨E, hEA, hE, hbound, hunif⟩ := tendstoUniformlyOn_of_ae_tendsto
    (μ := ν)
    (fun n => (continuous_intervalKernelBump_coefficient T n).measurable.stronglyMeasurable)
    (measurable_intervalOperatorAtom T).stronglyMeasurable hA (measure_ne_top _ _)
    (Eventually.of_forall fun t _ => intervalOperatorAtom_tendsto T t) hhalf
  refine ⟨A \ E, Set.diff_subset, hA.diff hE,
    positive_measure_diff_of_half_bound ν hpos hEA hE hbound, ?_⟩
  exact hunif.continuousOn (Eventually.of_forall fun n =>
    (continuous_intervalKernelBump_coefficient T n).continuousOn)

theorem intervalKernel_compact_uniform_selection
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜)
    (ν : Measure UnitInterval) [IsFiniteMeasure ν] (hν : ν Set.univ ≠ 0) :
    ∃ (Q : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (K : Set UnitInterval),
      (Q = T ∨ Q = ContinuousLinearMap.id 𝕜 (IntervalContinuous 𝕜) - T) ∧
      IsCompact K ∧ 0 < ν K ∧ (∀ t ∈ K, 1 / 2 ≤ ‖intervalOperatorAtom Q t‖) ∧
      ContinuousOn (intervalOperatorAtom Q) K ∧
      TendstoUniformlyOn (intervalKernelResidualMass Q) (fun _ => 0) atTop K := by
  obtain ⟨Q, A, hQ, hA, hposA, hlarge⟩ := intervalOperatorAtom_positive_branch T ν hν
  obtain ⟨D, hDA, hD, hposD, hres⟩ := intervalKernelResidual_positive_uniform Q ν hA hposA
  obtain ⟨E, hED, hE, hposE, hcont⟩ := intervalOperatorAtom_positive_continuous Q ν hD hposD
  obtain ⟨K, hKE, hK, hposK⟩ := hE.exists_lt_isCompact hposE
  refine ⟨Q, K, hQ, hK, hposK, fun t ht => hlarge t (hDA (hED (hKE ht))),
    hcont.mono hKE, hres.mono (hKE.trans hED)⟩

end ThesisCommon
