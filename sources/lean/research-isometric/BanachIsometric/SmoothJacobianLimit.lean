import BanachIsometric.SmoothLipschitzDerivative
import BanachIsometric.SmoothApproximationSequence

/-!
# Signed Jacobian integrals converge under the actual mollification

This supplies the limiting step in the alternative analytic homotopy argument.
The approximants, their common Lipschitz bound, and almost-everywhere derivative
convergence all come from the original Lipschitz map. There is no assumption of
convergence of Jacobians or of their integrals.
-/

namespace BanachIsometric

open MeasureTheory Metric Set Filter
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem tendsto_integral_signedJacobian_smoothBumpConvolution
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → E} {C : ℝ≥0}
    (hf : LipschitzWith C f) {s : Set E} (hs : IsCompact s)
    {g : E → ℝ} (hg : Continuous g) :
    Tendsto (fun n => ∫ x in s,
      (fderiv ℝ (smoothBumpConvolution μ (shrinkingBump E n) f) x).det *
        g (smoothBumpConvolution μ (shrinkingBump E n) f x) ∂μ)
      atTop (𝓝 (∫ x in s, (fderiv ℝ f x).det * g (f x) ∂μ)) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  letI : IsFiniteMeasure (μ.restrict s) := ⟨by simpa using hs.measure_lt_top⟩
  let fn : ℕ → E → E := fun n => smoothBumpConvolution μ (shrinkingBump E n) f
  have hLip (n : ℕ) : LipschitzWith C (fn n) :=
    lipschitzWith_smoothBumpConvolution μ (shrinkingBump E n) hf
  obtain ⟨R, hR⟩ := hs.exists_bound_of_continuousOn hf.continuous.continuousOn
  let B : ℝ := 2 * (C : ℝ) + max R 0
  have hval (n : ℕ) (x : E) (hx : x ∈ s) : fn n x ∈ closedBall (0 : E) B := by
    have hr : (shrinkingBump E n).rOut ≤ 2 := by
      change 2 / ((n : ℝ) + 1) ≤ 2
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have he := dist_smoothBumpConvolution_le μ (shrinkingBump E n) hf x
    rw [mem_closedBall, dist_zero_right]
    calc
      ‖fn n x‖ ≤ ‖fn n x - f x‖ + ‖f x‖ := norm_le_norm_sub_add _ _
      _ ≤ B := by
        change dist (fn n x) (f x) ≤ _ at he
        rw [dist_eq_norm] at he
        dsimp [B]
        nlinarith [hR x hx, le_max_left R 0, C.coe_nonneg]
  obtain ⟨D, hD⟩ := (isCompact_closedBall (0 : E →L[ℝ] E) (C : ℝ)).exists_bound_of_continuousOn
    ContinuousLinearMap.continuous_det.continuousOn
  obtain ⟨G, hG⟩ := (isCompact_closedBall (0 : E) B).exists_bound_of_continuousOn hg.continuousOn
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun x => (fderiv ℝ (fn n) x).det * g (fn n x)) (μ.restrict s) :=
    ((ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ (fn n))).mul
      (hg.comp (hLip n).continuous).measurable).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ x ∂μ.restrict s,
      ‖(fderiv ℝ (fn n) x).det * g (fn n x)‖ ≤ max D 0 * max G 0 := by
    filter_upwards [ae_restrict_mem hs.measurableSet] with x hx
    rw [norm_mul]
    have hder : fderiv ℝ (fn n) x ∈ closedBall (0 : E →L[ℝ] E) (C : ℝ) := by
      rw [mem_closedBall, dist_zero_right]
      exact norm_fderiv_le_of_lipschitz ℝ (hLip n)
    exact mul_le_mul ((hD _ hder).trans (le_max_left _ _))
      ((hG _ (hval n x hx)).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
  have htD := ae_tendsto_fderiv_smoothBumpConvolution μ
    (shrinkingBump_rOut_tendsto (E := E))
    (Filter.Eventually.of_forall (shrinkingBump_ratio (E := E))) hf
  have ht : ∀ᵐ x ∂μ.restrict s,
      Tendsto (fun n => (fderiv ℝ (fn n) x).det * g (fn n x)) atTop
        (𝓝 ((fderiv ℝ f x).det * g (f x))) := by
    filter_upwards [ae_restrict_of_ae htD] with x hx
    have hv : Tendsto (fun n => fn n x) atTop (𝓝 (f x)) :=
      ContDiffBump.convolution_tendsto_right_of_continuous
        (shrinkingBump_rOut_tendsto (E := E)) hf.continuous x
    exact (ContinuousLinearMap.continuous_det.tendsto _ |>.comp hx).mul
      (hg.continuousAt.tendsto.comp hv)
  exact tendsto_integral_of_dominated_convergence (fun _ => max D 0 * max G 0)
    hmeas (integrable_const _) hbound ht

end BanachIsometric
