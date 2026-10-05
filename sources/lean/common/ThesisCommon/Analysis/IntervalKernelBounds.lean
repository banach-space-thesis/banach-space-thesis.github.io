import ThesisCommon.Analysis.IntervalKernelOscillation

/-! Bounds and weak-star regularity of the actual representing kernel.
Although the kernel need not be norm-continuous, its norm-distance
sublevel sets are closed, by testing against every continuous function. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem norm_intervalOperatorKernel_le
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (t : UnitInterval) :
    ‖intervalOperatorKernel T t‖ ≤ ‖T‖ := by
  apply ((ContinuousMap.evalCLM 𝕜 t).opNorm_comp_le T).trans
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (norm_continuousMap_evalCLM_le (𝕜 := 𝕜) t) (norm_nonneg T)

theorem interval_kernel_oscillation_le
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (t : UnitInterval) :
    oscillation (intervalOperatorKernel T) t ≤ ENNReal.ofReal (2 * ‖T‖) := by
  rw [oscillation_eq_iInf_image]
  apply (show (⨅ U ∈ 𝓝 t, EMetric.diam (intervalOperatorKernel T '' U)) ≤
      EMetric.diam (intervalOperatorKernel T '' Set.univ) from
    iInf_le_of_le Set.univ (iInf_le_of_le (Filter.univ_mem : Set.univ ∈ 𝓝 t) le_rfl)).trans
  apply EMetric.diam_image_le_iff.2
  intro a ha b hb
  rw [edist_dist, dist_eq_norm (intervalOperatorKernel T a) (intervalOperatorKernel T b)]
  apply ENNReal.ofReal_le_ofReal
  apply (norm_sub_le (intervalOperatorKernel T a) (intervalOperatorKernel T b)).trans
  linarith [norm_intervalOperatorKernel_le T a, norm_intervalOperatorKernel_le T b]

theorem interval_kernel_oscillation_ne_top
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (t : UnitInterval) :
    oscillation (intervalOperatorKernel T) t ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (interval_kernel_oscillation_le T t)

theorem continuous_intervalOperatorKernel_apply
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (f : IntervalContinuous 𝕜) :
    Continuous (fun t => intervalOperatorKernel T t f) := (T f).continuous

theorem isClosed_intervalOperatorKernel_ball
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜)
    (μ : IntervalContinuous 𝕜 →L[𝕜] 𝕜) {r : ℝ} (hr : 0 ≤ r) :
    IsClosed {t | ‖intervalOperatorKernel T t - μ‖ ≤ r} := by
  have heq : {t | ‖intervalOperatorKernel T t - μ‖ ≤ r} =
      ⋂ f : IntervalContinuous 𝕜, {t | ‖(T f) t - μ f‖ ≤ r * ‖f‖} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact ContinuousLinearMap.opNorm_le_iff hr
  rw [heq]
  apply isClosed_iInter
  intro f
  exact isClosed_le ((T f).continuous.sub continuous_const).norm continuous_const

end ThesisCommon
