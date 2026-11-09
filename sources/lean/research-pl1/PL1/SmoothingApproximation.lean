import PL1.SmoothingTrace

/-! # Stability of the smoothing trace obstruction under operator-norm limits -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped ENNReal Topology

namespace PL1.SmoothingTrace

attribute [local instance] DyadicTrace.intervalMeasure_probability

variable {𝕜 Ω Ω₂ : Type*} [RCLike 𝕜] [MeasurableSpace Ω] [MeasurableSpace Ω₂]
  (μ : Measure Ω) (ν : Measure Ω₂)

theorem norm_restricted_sandwich_sub_le
    (A : Lp 𝕜 1 ν →L[𝕜] IntervalL1 𝕜)
    (S T : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 ν)
    (B : IntervalL1 𝕜 →L[𝕜] Lp 𝕜 1 μ) :
    ‖DyadicTrace.restrictLinfty (A.comp (S.comp B) - A.comp (T.comp B))‖ ≤
      (‖A‖ * ‖S - T‖) * ‖OperatorDomination.restriction μ B‖ := by
  have heq : DyadicTrace.restrictLinfty (A.comp (S.comp B) - A.comp (T.comp B)) =
      (A.comp (S - T)).comp (OperatorDomination.restriction μ B) := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [DyadicTrace.restrictLinfty, OperatorDomination.restriction,
      ContinuousLinearMap.comp_apply, sub_apply, map_sub]
  rw [heq]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))

theorem trace_tendsto_zero_of_operator_approximation
    (A : Lp 𝕜 1 ν →L[𝕜] IntervalL1 𝕜)
    (S : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 ν)
    (Sₙ : ℕ → Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 ν)
    (B : IntervalL1 𝕜 →L[𝕜] Lp 𝕜 1 μ)
    (hS : Tendsto (fun m => ‖S - Sₙ m‖) atTop (𝓝 0))
    (htrace : ∀ m, Tendsto (fun n => DyadicTrace.trace n (A.comp ((Sₙ m).comp B)))
      atTop (𝓝 0)) :
    Tendsto (fun n => DyadicTrace.trace n (A.comp (S.comp B))) atTop (𝓝 0) := by
  apply DyadicTrace.trace_tendsto_zero_of_approximation _
    (fun m => A.comp ((Sₙ m).comp B)) htrace
  apply squeeze_zero (fun m => norm_nonneg _)
    (fun m => norm_restricted_sandwich_sub_le μ ν A S (Sₙ m) B)
  simpa using (hS.const_mul ‖A‖).mul_const ‖OperatorDomination.restriction μ B‖

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The exponents of the smoothing approximations may approach one. -/
theorem trace_tendsto_zero_of_smoothing_approximation
    (A : Lp 𝕜 1 ν →L[𝕜] IntervalL1 𝕜)
    (S : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 ν)
    (Sₙ : ℕ → Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 ν)
    (B : IntervalL1 𝕜 →L[𝕜] Lp 𝕜 1 μ)
    (hS : Tendsto (fun m => ‖S - Sₙ m‖) atTop (𝓝 0))
    (p : ℕ → ℝ≥0∞) [∀ m, Fact (1 ≤ p m)] (hp2 : ∀ m, p m < 2)
    (Q : ∀ m, Lp 𝕜 (p m) μ →L[𝕜] H) (j : H →L[𝕜] Lp 𝕜 1 ν)
    (hQ : ∀ m (g : Lp 𝕜 1 μ) (f : Lp 𝕜 (p m) μ), g =ᵐ[μ] f → Sₙ m g = j (Q m f)) :
    Tendsto (fun n => DyadicTrace.trace n (A.comp (S.comp B))) atTop (𝓝 0) := by
  apply trace_tendsto_zero_of_operator_approximation μ ν A S Sₙ B hS
  intro m
  exact trace_tendsto_zero_of_smoothing μ ν A (Sₙ m) B (p m) (Fact.out) (hp2 m) (Q m) j (hQ m)

theorem one_le_norm_id_sub_of_smoothing_approximation
    (A : Lp 𝕜 1 ν →L[𝕜] IntervalL1 𝕜)
    (S : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 ν)
    (Sₙ : ℕ → Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 ν)
    (B : IntervalL1 𝕜 →L[𝕜] Lp 𝕜 1 μ)
    (hS : Tendsto (fun m => ‖S - Sₙ m‖) atTop (𝓝 0))
    (p : ℕ → ℝ≥0∞) [∀ m, Fact (1 ≤ p m)] (hp2 : ∀ m, p m < 2)
    (Q : ∀ m, Lp 𝕜 (p m) μ →L[𝕜] H) (j : H →L[𝕜] Lp 𝕜 1 ν)
    (hQ : ∀ m (g : Lp 𝕜 1 μ) (f : Lp 𝕜 (p m) μ), g =ᵐ[μ] f → Sₙ m g = j (Q m f)) :
    1 ≤ ‖DyadicTrace.restrictLinfty
      (ContinuousLinearMap.id 𝕜 (IntervalL1 𝕜) - A.comp (S.comp B))‖ :=
  DyadicTrace.one_le_norm_id_sub _
    (trace_tendsto_zero_of_smoothing_approximation μ ν A S Sₙ B hS p hp2 Q j hQ)

end PL1.SmoothingTrace
