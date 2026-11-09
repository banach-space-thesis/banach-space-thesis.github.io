import PL1.InputCompression

/-! # Passage from finite matrix traces to the whole operator -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

namespace PL1.MatrixTrace

attribute [local instance] DyadicTrace.intervalMeasure_probability

variable {𝕜 Ω : Type*} [RCLike 𝕜] [MeasurableSpace Ω]
  (μ : Measure Ω) [SFinite μ]

theorem trace_tendsto_zero_of_column_tails
    (A : L1Sum (Lp 𝕜 1 μ) →L[𝕜] IntervalL1 𝕜)
    (Q : L1Sum (Lp 𝕜 1 μ) →L[𝕜] L1Sum (Lp 𝕜 1 μ))
    (B : IntervalL1 𝕜 →L[𝕜] L1Sum (Lp 𝕜 1 μ))
    (houtput : ∀ F : Finset ℕ, Tendsto (fun m =>
      ‖(ContinuousLinearMap.id 𝕜 (L1Sum (Lp 𝕜 1 μ)) - compression (Finset.range m)).comp
        (Q.comp (compression F))‖) atTop (𝓝 0))
    (hentry : ∀ i j, Tendsto (fun n => DyadicTrace.trace n
      ((A.comp (insertion i)).comp ((entry Q i j).comp ((coordinate j).comp B))))
        atTop (𝓝 0)) :
    Tendsto (fun n => DyadicTrace.trace n (A.comp (Q.comp B))) atTop (𝓝 0) := by
  let R (F : Finset ℕ) := A.comp (Q.comp ((compression F).comp B))
  have htrace (F : Finset ℕ) : Tendsto (fun n => DyadicTrace.trace n (R F)) atTop (𝓝 0) := by
    let Rm (m : ℕ) := A.comp ((compression (Finset.range m)).comp (Q.comp ((compression F).comp B)))
    have hRm (m : ℕ) : Tendsto (fun n => DyadicTrace.trace n (Rm m)) atTop (𝓝 0) :=
      compressed_trace_tendsto_zero (Finset.range m) F A Q B (fun i _ j _ => hentry i j)
    apply DyadicTrace.trace_tendsto_zero_of_approximation (R F) Rm hRm
    have heq (m : ℕ) : DyadicTrace.restrictLinfty (R F - Rm m) =
        (A.comp ((ContinuousLinearMap.id 𝕜 (L1Sum (Lp 𝕜 1 μ)) - compression (Finset.range m)).comp
          (Q.comp (compression F)))).comp
            (B.comp (ProbabilityLp.inclusion intervalMeasure 1 ∞ le_top)) := by
      apply ContinuousLinearMap.ext
      intro f
      simp only [R, Rm, DyadicTrace.restrictLinfty, ContinuousLinearMap.comp_apply,
        sub_apply, map_sub, ContinuousLinearMap.id_apply]
    have hn (m : ℕ) : ‖DyadicTrace.restrictLinfty (R F - Rm m)‖ ≤
        (‖A‖ * ‖(ContinuousLinearMap.id 𝕜 (L1Sum (Lp 𝕜 1 μ)) - compression (Finset.range m)).comp
          (Q.comp (compression F))‖) * ‖B.comp (ProbabilityLp.inclusion intervalMeasure 1 ∞ le_top)‖ := by
      rw [heq]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    apply squeeze_zero (fun m => norm_nonneg _) hn
    simpa using ((houtput F).const_mul ‖A‖).mul_const
      ‖B.comp (ProbabilityLp.inclusion intervalMeasure 1 ∞ le_top)‖
  apply DyadicTrace.trace_tendsto_zero_of_approximation _ (fun n => R (Finset.range n))
    (fun n => htrace (Finset.range n))
  have heq (n : ℕ) : DyadicTrace.restrictLinfty (A.comp (Q.comp B) - R (Finset.range n)) =
      (A.comp Q).comp
        (((ContinuousLinearMap.id 𝕜 (L1Sum (Lp 𝕜 1 μ)) - compression (Finset.range n)).comp B).comp
          (ProbabilityLp.inclusion intervalMeasure 1 ∞ le_top)) := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [R, DyadicTrace.restrictLinfty, ContinuousLinearMap.comp_apply,
      sub_apply, map_sub, ContinuousLinearMap.id_apply]
  have hn (n : ℕ) : ‖DyadicTrace.restrictLinfty (A.comp (Q.comp B) - R (Finset.range n))‖ ≤
      ‖A.comp Q‖ * ‖((ContinuousLinearMap.id 𝕜 (L1Sum (Lp 𝕜 1 μ)) - compression (Finset.range n)).comp B).comp
        (ProbabilityLp.inclusion intervalMeasure 1 ∞ le_top)‖ := by
    rw [heq]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  apply squeeze_zero (fun n => norm_nonneg _) hn
  simpa using (InputCompression.norm_input_compression_error_tendsto_zero μ B).const_mul ‖A.comp Q‖

theorem one_le_norm_id_sub_of_column_tails
    (A : L1Sum (Lp 𝕜 1 μ) →L[𝕜] IntervalL1 𝕜)
    (Q : L1Sum (Lp 𝕜 1 μ) →L[𝕜] L1Sum (Lp 𝕜 1 μ))
    (B : IntervalL1 𝕜 →L[𝕜] L1Sum (Lp 𝕜 1 μ))
    (houtput : ∀ F : Finset ℕ, Tendsto (fun m =>
      ‖(ContinuousLinearMap.id 𝕜 (L1Sum (Lp 𝕜 1 μ)) - compression (Finset.range m)).comp
        (Q.comp (compression F))‖) atTop (𝓝 0))
    (hentry : ∀ i j, Tendsto (fun n => DyadicTrace.trace n
      ((A.comp (insertion i)).comp ((entry Q i j).comp ((coordinate j).comp B))))
        atTop (𝓝 0)) :
    1 ≤ ‖DyadicTrace.restrictLinfty
      (ContinuousLinearMap.id 𝕜 (IntervalL1 𝕜) - A.comp (Q.comp B))‖ :=
  DyadicTrace.one_le_norm_id_sub _ (trace_tendsto_zero_of_column_tails μ A Q B houtput hentry)

end PL1.MatrixTrace
