import BanachIsometric.SmoothLipschitzApproximation
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Derivative convergence of actual Lipschitz mollifications

Differentiation under the integral uses the original Lipschitz bound and
Rademacher's theorem at a fixed translated point. Thus the derivative of the
actual smooth convolution is convolution of the actual measurable derivative.
Lebesgue differentiation then gives almost-everywhere convergence of these
derivatives. No convergence of derivatives is taken as an input hypothesis.
-/

namespace BanachIsometric

open MeasureTheory MeasureTheory.Measure Metric Set Filter
open scoped Topology NNReal Convolution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem hasFDerivAt_smoothBumpConvolution (φ : ContDiffBump (0 : E))
    {f : E → F} {C : ℝ≥0} (hf : LipschitzWith C f) (x : E) :
    HasFDerivAt (smoothBumpConvolution μ φ f)
      (smoothBumpConvolution μ φ (fderiv ℝ f) x) x := by
  letI : CompleteSpace F := FiniteDimensional.complete ℝ F
  have hex : ConvolutionExists (φ.normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ :=
    φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
      (ContinuousLinearMap.lsmul ℝ ℝ) φ.continuous_normed.locallyIntegrable hf.continuous
  have hi (y : E) : Integrable (fun z => φ.normed μ z • f (y - z)) μ := by
    simpa only [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply] using hex y
  have hd : ∀ᵐ z ∂μ, DifferentiableAt ℝ f (x - z) := by
    apply ae_of_ae_map ((measurable_id.const_sub x).aemeasurable)
    change ∀ᵐ y ∂Measure.map (fun z => x - z) μ, DifferentiableAt ℝ f y
    rw [(μ.measurePreserving_sub_left x).map_eq]
    exact hf.ae_differentiableAt
  have hmD : AEStronglyMeasurable
      (fun z => φ.normed μ z • fderiv ℝ f (x - z)) μ :=
    (φ.continuous_normed.measurable.smul
      ((measurable_fderiv ℝ f).comp (measurable_id.const_sub x))).aestronglyMeasurable
  have hb : Integrable (fun z => φ.normed μ z * (C : ℝ)) μ :=
    (φ.continuous_normed.integrable_of_hasCompactSupport φ.hasCompactSupport_normed).mul_const _
  have hLip : ∀ᵐ z ∂μ, LipschitzOnWith (Real.nnabs (φ.normed μ z * (C : ℝ)))
      (fun y => φ.normed μ z • f (y - z)) (ball x 1) := by
    apply ae_of_all
    intro z
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro y w
    rw [dist_eq_norm, ← smul_sub, norm_smul,
      Real.norm_of_nonneg (φ.nonneg_normed z), Real.coe_nnabs,
      abs_of_nonneg (mul_nonneg (φ.nonneg_normed z) C.coe_nonneg)]
    calc
      φ.normed μ z * ‖f (y - z) - f (w - z)‖ ≤
          φ.normed μ z * ((C : ℝ) * dist (y - z) (w - z)) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [dist_eq_norm] using (hf.dist_le_mul (y - z) (w - z)))
          (φ.nonneg_normed z)
      _ = (φ.normed μ z * (C : ℝ)) * dist y w := by rw [dist_sub_right]; ring
  have hdiff : ∀ᵐ z ∂μ, HasFDerivAt (fun y => φ.normed μ z • f (y - z))
      (φ.normed μ z • fderiv ℝ f (x - z)) x := by
    filter_upwards [hd] with z hz
    simpa only [ContinuousLinearMap.comp_id] using
      (hz.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const z)).const_smul (φ.normed μ z)
  have ht := hasFDerivAt_integral_of_dominated_loc_of_lip (by norm_num : (0 : ℝ) < 1)
    (Filter.Eventually.of_forall (fun y => (hi y).aestronglyMeasurable)) (hi x) hmD hLip hb hdiff
  exact ht.2

theorem fderiv_smoothBumpConvolution_eq (φ : ContDiffBump (0 : E))
    {f : E → F} {C : ℝ≥0} (hf : LipschitzWith C f) (x : E) :
    fderiv ℝ (smoothBumpConvolution μ φ f) x =
      smoothBumpConvolution μ φ (fderiv ℝ f) x :=
  (hasFDerivAt_smoothBumpConvolution μ φ hf x).fderiv

theorem ae_tendsto_fderiv_smoothBumpConvolution
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : E)} {K : ℝ}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hRatio : ∀ᶠ i in l, (φ i).rOut ≤ K * (φ i).rIn)
    {f : E → F} {C : ℝ≥0} (hf : LipschitzWith C f) :
    ∀ᵐ x ∂μ, Tendsto (fun i => fderiv ℝ (smoothBumpConvolution μ (φ i) f) x)
      l (𝓝 (fderiv ℝ f x)) := by
  letI : CompleteSpace F := FiniteDimensional.complete ℝ F
  have hl : LocallyIntegrable (fderiv ℝ f) μ :=
    (memLp_top_of_bound (measurable_fderiv ℝ f).aestronglyMeasurable (C : ℝ)
      (ae_of_all _ (fun x => norm_fderiv_le_of_lipschitz ℝ hf))).locallyIntegrable le_top
  have ht := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ hRatio hl
  filter_upwards [ht] with x hx
  have he : (fun i => fderiv ℝ (smoothBumpConvolution μ (φ i) f) x) =
      (fun i => smoothBumpConvolution μ (φ i) (fderiv ℝ f) x) := by
    funext i
    exact fderiv_smoothBumpConvolution_eq μ (φ i) hf x
  rw [he]
  exact hx

end BanachIsometric
