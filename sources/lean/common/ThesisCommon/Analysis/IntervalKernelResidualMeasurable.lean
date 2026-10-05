import ThesisCommon.Analysis.IntervalKernelPositiveTests
import ThesisCommon.Analysis.IntervalPuncturedCutoffs
import Mathlib.MeasureTheory.Function.Egorov

/-! The shrinking control masses are Borel functions with Egorov uniformization. -/
noncomputable section
open Filter Topology MeasureTheory
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem measurable_intervalKernel_control_punctured_ball
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (r : ℝ) :
    Measurable (fun t => (continuousMapRieszControl (intervalOperatorKernel T t)).real
      (Metric.ball t r \ {t})) := by
  apply measurable_of_tendsto_metrizable
    (fun n => measurable_intervalKernel_control_integral T (intervalPuncturedCutoff r n)
      (continuous_intervalPuncturedCutoff r n) (intervalPuncturedCutoff_nonneg r n))
  apply tendsto_pi_nhds.mpr
  intro t
  exact integral_intervalPuncturedCutoff_tendsto
    (continuousMapRieszControl (intervalOperatorKernel T t)) r t

theorem measurable_intervalKernelResidualMass
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (n : ℕ) :
    Measurable (intervalKernelResidualMass T n) :=
  measurable_intervalKernel_control_punctured_ball T (1 / (n + 1 : ℝ))

theorem intervalKernelResidual_egorov
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜)
    (ν : Measure UnitInterval) [IsFiniteMeasure ν] {A : Set UnitInterval}
    (hA : MeasurableSet A) {ε : ℝ} (hε : 0 < ε) :
    ∃ E ⊆ A, MeasurableSet E ∧ ν E ≤ ENNReal.ofReal ε ∧
      TendstoUniformlyOn (intervalKernelResidualMass T) (fun _ => 0) atTop (A \ E) := by
  apply tendstoUniformlyOn_of_ae_tendsto
    (fun n => (measurable_intervalKernelResidualMass T n).stronglyMeasurable)
    stronglyMeasurable_const hA (measure_ne_top _ _) _ hε
  exact Eventually.of_forall fun t _ => intervalKernelResidualMass_tendsto T t

end ThesisCommon
