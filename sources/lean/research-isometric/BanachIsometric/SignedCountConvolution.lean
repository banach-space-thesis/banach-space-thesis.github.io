import BanachIsometric.SignedMultiplicityIntegrability
import BanachIsometric.SmoothApproximationSequence

/-!
# Actual signed-count convolutions and recovery from an almost-everywhere limit

The convolution is identified with an ordinary signed-Jacobian integral by
the proved signed area formula. Its almost-everywhere limit is the actual
integer fiber count by Lebesgue differentiation.
-/

namespace BanachIsometric

open MeasureTheory Set Filter
open scoped Topology NNReal Convolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem smoothBumpConvolution_signedFiberCount_eq_integral
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → E} {C : ℝ≥0}
    (hf : LipschitzWith C f) {s : Set E} (hs : IsCompact s)
    (φ : ContDiffBump (0 : E)) (y : E) :
    smoothBumpConvolution μ φ
      (fun z => (signedFiberCount f (fderiv ℝ f) s z : ℝ)) y =
      ∫ x in s, (fderiv ℝ f x).det * φ.normed μ (f x - y) ∂μ := by
  have he (z : E) : φ.normed μ (y - z) = φ.normed μ (z - y) := by
    simpa only [neg_sub] using φ.normed_neg (μ := μ) (z - y)
  change (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ]
    (fun z => (signedFiberCount f (fderiv ℝ f) s z : ℝ))) y = _
  rw [convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  calc
    (∫ z, φ.normed μ (y - z) * (signedFiberCount f (fderiv ℝ f) s z : ℝ) ∂μ) =
        ∫ z, (signedFiberCount f (fderiv ℝ f) s z : ℝ) * φ.normed μ (z - y) ∂μ := by
      apply integral_congr_ae
      filter_upwards with z
      rw [he, mul_comm]
    _ = _ := integral_signedFiberCount_of_compact_lipschitz μ hf hs
      (show Continuous (fun z : E => φ.normed μ (z - y)) from
        φ.continuous_normed.comp (continuous_id.sub continuous_const))

theorem ae_tendsto_smoothBumpConvolution_signedFiberCount
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → E} {C : ℝ≥0}
    (hf : LipschitzWith C f) {s : Set E} (hs : IsCompact s) :
    ∀ᵐ y ∂μ, Tendsto (fun k => smoothBumpConvolution μ (shrinkingBump E k)
      (fun z => (signedFiberCount f (fderiv ℝ f) s z : ℝ)) y) atTop
      (𝓝 (signedFiberCount f (fderiv ℝ f) s y : ℝ)) := by
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (shrinkingBump_rOut_tendsto (E := E))
    (Eventually.of_forall (shrinkingBump_ratio (E := E)))
    (integrable_signedFiberCount_of_compact_lipschitz μ hf hs).locallyIntegrable

end BanachIsometric

namespace BanachIsometric

open MeasureTheory Set Filter
open scoped Topology

/-- A nonnull set supplies a point where the almost-everywhere limits exist.
Eventual equality of every approximating function on the set then identifies
the limit almost everywhere with the value at that point. -/
theorem exists_anchor_ae_eq_of_eventually_eq_on_of_ae_tendsto
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {s : Set X}
    (hs : μ s ≠ 0) {u : ℕ → X → ℝ} {f : X → ℝ}
    (ht : ∀ᵐ y ∂μ, Tendsto (fun k => u k y) atTop (𝓝 (f y)))
    (heq : ∀ᶠ k in atTop, ∀ y ∈ s, ∀ z ∈ s, u k y = u k z) :
    ∃ z ∈ s, ∀ᵐ y ∂μ, y ∈ s → f y = f z := by
  obtain ⟨z, hz, htz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hs (ae_restrict_of_ae ht)
  refine ⟨z, hz, ?_⟩
  filter_upwards [ht] with y hty
  intro hy
  have hseq : (fun k => u k y) =ᶠ[atTop] (fun k => u k z) :=
    heq.mono (fun k hk => hk y hy z hz)
  exact tendsto_nhds_unique hty (htz.congr' hseq.symm)

end BanachIsometric
