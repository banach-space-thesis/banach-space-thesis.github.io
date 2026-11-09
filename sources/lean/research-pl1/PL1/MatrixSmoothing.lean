import PL1.MatrixTraceLimit
import PL1.OutputCompression

/-! # The matrix trace obstruction from summable columns and smoothing entries -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped ENNReal Topology

namespace PL1.MatrixTrace

attribute [local instance] DyadicTrace.intervalMeasure_probability

variable {𝕜 Ω : Type*} [RCLike 𝕜] [MeasurableSpace Ω]
  (μ : Measure Ω) [SFinite μ]

theorem trace_tendsto_zero_of_summable_columns
    (A : L1Sum (Lp 𝕜 1 μ) →L[𝕜] IntervalL1 𝕜)
    (Q : L1Sum (Lp 𝕜 1 μ) →L[𝕜] L1Sum (Lp 𝕜 1 μ))
    (B : IntervalL1 𝕜 →L[𝕜] L1Sum (Lp 𝕜 1 μ))
    (hcolumns : ∀ j, Summable (fun i => ‖entry Q i j‖))
    (hentry : ∀ i j, Tendsto (fun n => DyadicTrace.trace n
      ((A.comp (insertion i)).comp ((entry Q i j).comp ((coordinate j).comp B))))
        atTop (𝓝 0)) :
    Tendsto (fun n => DyadicTrace.trace n (A.comp (Q.comp B))) atTop (𝓝 0) :=
  trace_tendsto_zero_of_column_tails μ A Q B
    (OutputCompression.tendsto_output_compression Q hcolumns) hentry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

theorem trace_tendsto_zero_of_smoothing_entries
    (A : L1Sum (Lp 𝕜 1 μ) →L[𝕜] IntervalL1 𝕜)
    (Q : L1Sum (Lp 𝕜 1 μ) →L[𝕜] L1Sum (Lp 𝕜 1 μ))
    (B : IntervalL1 𝕜 →L[𝕜] L1Sum (Lp 𝕜 1 μ))
    (hcolumns : ∀ j, Summable (fun i => ‖entry Q i j‖))
    (S : ℕ → ℕ → ℕ → Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 μ)
    (hS : ∀ i j, Tendsto (fun m => ‖entry Q i j - S i j m‖) atTop (𝓝 0))
    (p : ℕ → ℕ → ℕ → ℝ≥0∞) [∀ i j m, Fact (1 ≤ p i j m)]
    (hp2 : ∀ i j m, p i j m < 2)
    (T : ∀ i j m, Lp 𝕜 (p i j m) μ →L[𝕜] H)
    (J : H →L[𝕜] Lp 𝕜 1 μ)
    (hT : ∀ i j m (g : Lp 𝕜 1 μ) (f : Lp 𝕜 (p i j m) μ),
      g =ᵐ[μ] f → S i j m g = J (T i j m f)) :
    Tendsto (fun n => DyadicTrace.trace n (A.comp (Q.comp B))) atTop (𝓝 0) := by
  apply trace_tendsto_zero_of_summable_columns μ A Q B hcolumns
  intro i j
  exact SmoothingTrace.trace_tendsto_zero_of_smoothing_approximation μ μ
    (A.comp (insertion i)) (entry Q i j) (S i j) ((coordinate j).comp B)
    (hS i j) (p i j) (hp2 i j) (T i j) J (hT i j)

/-- The whole matrix stays at distance at least one from the interval identity
after arbitrary bounded pre- and post-composition. -/
theorem one_le_norm_id_sub_of_smoothing_entries
    (A : L1Sum (Lp 𝕜 1 μ) →L[𝕜] IntervalL1 𝕜)
    (Q : L1Sum (Lp 𝕜 1 μ) →L[𝕜] L1Sum (Lp 𝕜 1 μ))
    (B : IntervalL1 𝕜 →L[𝕜] L1Sum (Lp 𝕜 1 μ))
    (hcolumns : ∀ j, Summable (fun i => ‖entry Q i j‖))
    (S : ℕ → ℕ → ℕ → Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 μ)
    (hS : ∀ i j, Tendsto (fun m => ‖entry Q i j - S i j m‖) atTop (𝓝 0))
    (p : ℕ → ℕ → ℕ → ℝ≥0∞) [∀ i j m, Fact (1 ≤ p i j m)]
    (hp2 : ∀ i j m, p i j m < 2)
    (T : ∀ i j m, Lp 𝕜 (p i j m) μ →L[𝕜] H)
    (J : H →L[𝕜] Lp 𝕜 1 μ)
    (hT : ∀ i j m (g : Lp 𝕜 1 μ) (f : Lp 𝕜 (p i j m) μ),
      g =ᵐ[μ] f → S i j m g = J (T i j m f)) :
    1 ≤ ‖DyadicTrace.restrictLinfty
      (ContinuousLinearMap.id 𝕜 (IntervalL1 𝕜) - A.comp (Q.comp B))‖ :=
  DyadicTrace.one_le_norm_id_sub _
    (trace_tendsto_zero_of_smoothing_entries μ A Q B hcolumns S hS p hp2 T J hT)

end PL1.MatrixTrace
