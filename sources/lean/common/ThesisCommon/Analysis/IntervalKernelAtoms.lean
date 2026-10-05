import ThesisCommon.Analysis.IntervalKernelBumps
import ThesisCommon.Analysis.ContinuousMapComplexRiesz
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-! The diagonal atom of the real/complex representing kernel is a Borel function.
Moving continuous tents identify it by dominated convergence, without any continuity
assumption on the positive and negative Jordan components. -/
noncomputable section
open Filter Topology MeasureTheory
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem integral_intervalKernelBump_tendsto (ν : Measure UnitInterval) [IsFiniteMeasure ν]
    (t : UnitInterval) :
    Tendsto (fun n => ∫ x, intervalKernelBump (𝕜 := 𝕜) n t x ∂ν) atTop
      (𝓝 (ν.real {t} : 𝕜)) := by
  have h := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ => (1 : ℝ))
    (fun n => (intervalKernelBump (𝕜 := 𝕜) n t).continuous.aestronglyMeasurable)
    (integrable_const 1)
    (fun n => Eventually.of_forall fun x =>
      ((intervalKernelBump (𝕜 := 𝕜) n t).norm_coe_le_norm x).trans
        (norm_intervalKernelBump_le n t))
    (Eventually.of_forall fun x => intervalKernelBump_tendsto (𝕜 := 𝕜) t x)
  have heq : (fun x : UnitInterval => if x = t then (1 : 𝕜) else 0) =
      Set.indicator {t} (fun _ => (1 : 𝕜)) := by
    ext x
    simp only [Set.indicator_apply, Set.mem_singleton_iff]
  rw [heq, integral_indicator (measurableSet_singleton t), integral_const] at h
  simpa [RCLike.real_smul_eq_coe_mul, Measure.real] using h

/-- The actual singleton value of the representing vector measure. -/
def intervalOperatorAtom (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜)
    (t : UnitInterval) : 𝕜 := continuousMapRieszVector (intervalOperatorKernel T t) {t}

theorem intervalOperatorAtom_tendsto
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (t : UnitInterval) :
    Tendsto (fun n => intervalOperatorKernel T t (intervalKernelBump n t)) atTop
      (𝓝 (intervalOperatorAtom T t)) := by
  rw [intervalOperatorAtom, continuousMapRieszVector_apply,
    continuousMapRieszSigned_apply _ (measurableSet_singleton t),
    continuousMapRieszSigned_apply _ (measurableSet_singleton t)]
  simp only [RCLike.ofReal_sub]
  have hr := (integral_intervalKernelBump_tendsto (𝕜 := 𝕜)
      (continuousMapRieszPositive (continuousMapFunctionalRe (intervalOperatorKernel T t))) t).sub
    (integral_intervalKernelBump_tendsto (𝕜 := 𝕜)
      (continuousMapRieszNegative (continuousMapFunctionalRe (intervalOperatorKernel T t))) t)
  have hi := (integral_intervalKernelBump_tendsto (𝕜 := 𝕜)
      (continuousMapRieszPositive (continuousMapFunctionalIm (intervalOperatorKernel T t))) t).sub
    (integral_intervalKernelBump_tendsto (𝕜 := 𝕜)
      (continuousMapRieszNegative (continuousMapFunctionalIm (intervalOperatorKernel T t))) t)
  apply (hr.add (hi.mul_const RCLike.I)).congr'
  exact Eventually.of_forall fun n =>
    (continuousMap_complex_riesz_representation (intervalOperatorKernel T t)
      (intervalKernelBump n t)).symm

theorem measurable_intervalOperatorAtom [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) :
    Measurable (intervalOperatorAtom T) :=
  measurable_of_tendsto_metrizable
    (fun n => (continuous_intervalKernelBump_coefficient T n).measurable)
    (tendsto_pi_nhds.mpr (intervalOperatorAtom_tendsto T))

theorem norm_intervalOperatorAtom_le
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (t : UnitInterval) :
    ‖intervalOperatorAtom T t‖ ≤ ‖T‖ := by
  apply le_of_tendsto (intervalOperatorAtom_tendsto T t).norm
  apply Eventually.of_forall
  intro n
  exact ((intervalOperatorKernel T t).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left (norm_intervalKernelBump_le n t) (norm_nonneg _)).trans
      (by simpa only [mul_one] using norm_intervalOperatorKernel_le T t))

theorem intervalOperatorAtom_add
    (T S : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (t : UnitInterval) :
    intervalOperatorAtom (T + S) t = intervalOperatorAtom T t + intervalOperatorAtom S t := by
  apply tendsto_nhds_unique (intervalOperatorAtom_tendsto (T + S) t)
  simpa only [intervalOperatorKernel_add, ContinuousLinearMap.add_apply] using
    (intervalOperatorAtom_tendsto T t).add (intervalOperatorAtom_tendsto S t)

theorem intervalOperatorAtom_id (t : UnitInterval) :
    intervalOperatorAtom (ContinuousLinearMap.id 𝕜 (IntervalContinuous 𝕜)) t = 1 := by
  apply tendsto_nhds_unique (intervalOperatorAtom_tendsto _ t)
  simpa only [intervalOperatorKernel_id, ContinuousMap.evalCLM_apply,
    intervalKernelBump_center] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : 𝕜)) atTop (𝓝 1))

end ThesisCommon
