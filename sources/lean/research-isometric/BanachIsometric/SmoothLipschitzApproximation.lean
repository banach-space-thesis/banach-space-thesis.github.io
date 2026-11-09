import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Actual smooth approximation of a Lipschitz map

Normalised positive bump convolution preserves a map's Lipschitz constant
and approximates it uniformly within `C*rOut`. These are concrete convolutions,
not an assumed smooth approximation or an assumed approximation in derivative.
-/

namespace BanachIsometric

open MeasureTheory MeasureTheory.Measure Metric Set Filter
open scoped Topology NNReal Convolution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (μ : Measure E) [μ.IsAddHaarMeasure]

noncomputable def smoothBumpConvolution (φ : ContDiffBump (0 : E)) (f : E → F) : E → F :=
  φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f

omit [CompleteSpace F] in
theorem contDiff_smoothBumpConvolution (φ : ContDiffBump (0 : E))
    {f : E → F} {C : ℝ≥0} (hf : LipschitzWith C f) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothBumpConvolution μ φ f) := by
  exact φ.hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) φ.contDiff_normed hf.continuous.locallyIntegrable

theorem dist_smoothBumpConvolution_le (φ : ContDiffBump (0 : E))
    {f : E → F} {C : ℝ≥0} (hf : LipschitzWith C f) (x : E) :
    dist (smoothBumpConvolution μ φ f x) (f x) ≤ (C : ℝ) * φ.rOut := by
  apply ContDiffBump.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
  intro z hz
  exact (hf.dist_le_mul z x).trans
    (mul_le_mul_of_nonneg_left (mem_ball.mp hz).le C.coe_nonneg)

omit [CompleteSpace F] in
theorem lipschitzWith_smoothBumpConvolution (φ : ContDiffBump (0 : E))
    {f : E → F} {C : ℝ≥0} (hf : LipschitzWith C f) :
    LipschitzWith C (smoothBumpConvolution μ φ f) := by
  have hex : ConvolutionExists (φ.normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ :=
    φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
      (ContinuousLinearMap.lsmul ℝ ℝ) φ.continuous_normed.locallyIntegrable hf.continuous
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  change ‖(∫ z, φ.normed μ z • f (x - z) ∂μ) -
      (∫ z, φ.normed μ z • f (y - z) ∂μ)‖ ≤ (C : ℝ) * dist x y
  have hix : Integrable (fun z => φ.normed μ z • f (x - z)) μ := by
    simpa only [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply] using hex x
  have hiy : Integrable (fun z => φ.normed μ z • f (y - z)) μ := by
    simpa only [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply] using hex y
  rw [← integral_sub hix hiy]
  calc
    ‖∫ z, φ.normed μ z • f (x - z) - φ.normed μ z • f (y - z) ∂μ‖ ≤
        ∫ z, φ.normed μ z * ((C : ℝ) * dist x y) ∂μ := by
      apply norm_integral_le_of_norm_le
        (φ.continuous_normed.integrable_of_hasCompactSupport φ.hasCompactSupport_normed |>.mul_const _)
      apply ae_of_all
      intro z
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (φ.nonneg_normed z)]
      apply mul_le_mul_of_nonneg_left ?_ (φ.nonneg_normed z)
      simpa only [← dist_eq_norm, dist_sub_right] using hf.dist_le_mul (x - z) (y - z)
    _ = (C : ℝ) * dist x y := by rw [integral_mul_const, φ.integral_normed, one_mul]

end BanachIsometric
