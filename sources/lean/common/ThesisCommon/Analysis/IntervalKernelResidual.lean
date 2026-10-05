import ThesisCommon.Analysis.IntervalKernelAtoms
import ThesisCommon.Analysis.ContinuousMapRieszResidual
import ThesisCommon.Analysis.MeasurePuncturedBalls

/-! Pointwise shrinking residual estimates for interval kernels. These estimates
do not yet assert uniform convergence on a positive-measure subset. -/
noncomputable section
open Filter Topology MeasureTheory
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

def intervalKernelResidualMass
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (n : ℕ) (t : UnitInterval) : ℝ :=
  (continuousMapRieszControl (intervalOperatorKernel T t)).real
    (Metric.ball t (1 / (n + 1 : ℝ)) \ {t})

theorem intervalKernelResidualMass_nonneg
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (n : ℕ) (t : UnitInterval) :
    0 ≤ intervalKernelResidualMass T n t := measureReal_nonneg

theorem intervalKernelResidualMass_le
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (n : ℕ) (t : UnitInterval) :
    intervalKernelResidualMass T n t ≤ 2 * ‖T‖ := by
  apply (measureReal_mono (Set.subset_univ _)).trans
  exact (continuousMapRieszControl_mass_le (intervalOperatorKernel T t)).trans
    (mul_le_mul_of_nonneg_left (norm_intervalOperatorKernel_le T t) (by norm_num))

theorem intervalKernelResidualMass_tendsto
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (t : UnitInterval) :
    Tendsto (fun n => intervalKernelResidualMass T n t) atTop (𝓝 0) :=
  tendsto_measureReal_puncturedBalls (continuousMapRieszControl (intervalOperatorKernel T t)) t

theorem intervalKernelResidual_local_bound
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (t : UnitInterval) (n : ℕ)
    (f : IntervalContinuous 𝕜)
    (hf : ∀ x ∉ Metric.ball t (1 / (n + 1 : ℝ)), f x = 0) :
    ‖T f t - intervalOperatorAtom T t * f t‖ ≤ ‖f‖ * intervalKernelResidualMass T n t :=
  continuousMapRiesz_residual_local_bound (intervalOperatorKernel T t) f t _ hf

theorem intervalKernelResidual_exists_small_radius
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (t : UnitInterval)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ f : IntervalContinuous 𝕜, (∀ x ∉ Metric.ball t r, f x = 0) →
      ‖T f t - intervalOperatorAtom T t * f t‖ ≤ ε * ‖f‖ := by
  obtain ⟨n, hn⟩ := ((intervalKernelResidualMass_tendsto T t).eventually
    (gt_mem_nhds hε)).exists
  refine ⟨1 / (n + 1 : ℝ), by positivity, fun f hf => ?_⟩
  exact (intervalKernelResidual_local_bound T t n f hf).trans
    ((mul_le_mul_of_nonneg_left hn.le (norm_nonneg f)).trans_eq (mul_comm _ _))

end ThesisCommon
